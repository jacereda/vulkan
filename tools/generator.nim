# Written by Leonardo Mariscal <leo@ldmd.mx>, 2019

import strutils, ./utils, os, xmlparser, xmltree, streams, strformat, math, tables, algorithm, system, osproc, pegs, strmisc

type
  VkProc = object
    name: string
    rVal: string
    args: seq[VkArg]
  VkArg = object
    name: string
    argType: string
  VkStruct = object
    name: string
    members: seq[VkArg]

var vkProcs: seq[VkProc]
var vkStructs: seq[VkStruct]
var vkStructureTypes: seq[string]

proc translateSimpleType(s: string): string =
  result = s
  result = result.replace("struct ", "object ")
  result = result.replace("int64_t", "int64")
  result = result.replace("int32_t", "int32")
  result = result.replace("int16_t", "int16")
  result = result.replace("int8_t", "int8")
  result = result.replace("size_t", "uint") # uint matches pointer size just like size_t
  result = result.replace("float", "float32")
  result = result.replace("double", "float64")

proc translateType(s: string): string =
  result = s
  result = result.replace("struct ", " ")
  result = result.translateSimpleType
  result = result.replace("VK_DEFINE_HANDLE", "VkHandle")
  result = result.replace("VK_DEFINE_NON_DISPATCHABLE_HANDLE", "VkNonDispatchableHandle")
  result = result.replace("const ", "")
  result = result.replace(" const", "")
  result = result.replace("unsigned ", "u")
  result = result.replace("signed ", "")

  if result.contains('*'):
    let levels = result.count('*')
    result = result.replace("*", "")
    for i in 0..<levels:
      result = "ptr " & result

  result = result.replace("ptr void", "pointer")
  result = result.replace("void", "pointer")
  result = result.replace("ptr ptr char", "cstringArray")
  result = result.replace("ptr char", "cstring")


proc translateReturnType(s: string): string =
  if s == "void": return s
  result = translateType s

iterator typeItems(node: XmlNode): XmlNode =
  for types in node.findAll("types"):
    for t in types.items:
      if t.attr("category") == "include" or t.attr("requires") == "vk_platform" or
         t.tag != "type" or t.attr("name") == "int":
        continue
      yield t

iterator catItems(node: XmlNode, cat: string): XmlNode =
  for t in node.typeItems:
    if t.attr("category") == cat:
      yield t

proc section(output: var string, s: string) =
  echo "Generating ", s, "..."
  output.add("\n#" & s & "\n\n")

proc genRequires(node: XmlNode, output: var string) =
  output.section("Requires")
  output.add("type\n")
  for t in node.typeItems:
    if t.attr("requires").contains(".h"):
        output.add("  {t.attr(\"name\")}* = ptr object\n".fmt)

proc genDefines(node: XmlNode, output: var string) =
  output.section("Defines")
  for t in node.catItems("define"):
    if t.child("name") == nil:
      continue
    let name = t.child("name").innerText
    if  name == "VK_MAKE_VERSION":
      output.add("\ntemplate vkMakeVersion*(major, minor, patch: untyped): untyped =\n")
      output.add("  (((major) shl 22) or ((minor) shl 12) or (patch))\n")
    elif name == "VK_VERSION_MAJOR":
      output.add("\ntemplate vkVersionMajor*(version: untyped): untyped =\n")
      output.add("  ((uint32)(version) shr 22)\n")
    elif name == "VK_VERSION_MINOR":
      output.add("\ntemplate vkVersionMinor*(version: untyped): untyped =\n")
      output.add("  (((uint32)(version) shr 12) and 0x000003FF)\n")
    elif name == "VK_VERSION_PATCH":
      output.add("\ntemplate vkVersionPatch*(version: untyped): untyped =\n")
      output.add("  ((uint32)(version) and 0x00000FFF)\n")
    elif name == "VK_API_VERSION_1_0":
      output.add("\nconst vkApiVersion1_0* = vkMakeVersion(1, 0, 0)\n")
    elif name == "VK_API_VERSION_1_1":
      output.add("const vkApiVersion1_1* = vkMakeVersion(1, 1, 0)\n")
    elif name == "VK_API_VERSION_1_2":
      output.add("const vkApiVersion1_2* = vkMakeVersion(1, 2, 0)\n")
    elif name == "VK_HEADER_VERSION":
      output.add("const vkHeaderVersion* = {t.innerText.partition(\"VK_HEADER_VERSION\")[2]}\n".fmt)
#define VK_HEADER_VERSION
    elif name == "VK_HEADER_VERSION_COMPLETE":
      output.add("const vkHeaderVersionComplete* = vkMakeVersion(1,2, vkHeaderVersion)\n")
    elif name == "VK_NULL_HANDLE":
      output.add("const vkNullHandle* = 0\n")
    elif name == "VK_API_VERSION":
      discard
    elif name == "VK_DEFINE_HANDLE":
      discard
    else:
      echo "category:define not found {name}".fmt


proc genBaseTypes(node: XmlNode, output: var string) =
  output.section("BaseTypes")
  output.add("type\n")
  for t in node.catItems("basetype"):
      let name = t.child("name").innerText
      var bType = "struct ";
      let tnode = t.child("type")
      if tnode != nil:
        bType = tnode.innerText
      bType = bType.translateSimpleType
      output.add("  {name}* = distinct {bType}\n".fmt)

proc genBitmasks(node: XmlNode, output: var string) =
  output.section("Bitmasks")
  output.add("type\n")
  for t in node.catItems("bitmask"):
      var name = t.attr("name")
      if t.child("name") != nil:
        name = t.child("name").innerText
      var bType = t.attr("alias")
      var alias = true
      if t.child("type") != nil:
        alias = false
        bType = t.child("type").innerText
      bType = bType.translateType
      if not alias:
        bType = "distinct " & bType
      output.add("  {name}* = {bType}\n".fmt)

proc genHandles(node: XmlNode, output: var string) =
  output.section("Handles")
  output.add("type\n")
  for t in node.catItems("handle"):
    var name = t.attr("name")
    if t.child("name") != nil:
      name = t.child("name").innerText
    var bType = t.attr("alias")
    var alias = true
    if t.child("type") != nil:
      alias = false
      bType = t.child("type").innerText
    bType = bType.translateType
    if not alias:
      bType = "distinct " & bType
    output.add("  {name}* = {bType}\n".fmt)

proc genFuncPtr(node: XmlNode, output: var string) =
  let name = node.child("name").innerText
  if name == "PFN_vkInternalAllocationNotification":
    output.add("  PFN_vkInternalAllocationNotification* = proc(pUserData: pointer; size: csize_t; allocationType: VkInternalAllocationType; allocationScope: VkSystemAllocationScope) {.cdecl.}\n")
  elif name == "PFN_vkInternalFreeNotification":
    output.add("  PFN_vkInternalFreeNotification* = proc(pUserData: pointer; size: csize_t; allocationType: VkInternalAllocationType; allocationScope: VkSystemAllocationScope) {.cdecl.}\n")
  elif name == "PFN_vkReallocationFunction":
    output.add("  PFN_vkReallocationFunction* = proc(pUserData: pointer; pOriginal: pointer; size: csize_t; alignment: csize_t; allocationScope: VkSystemAllocationScope): pointer {.cdecl.}\n")
  elif name == "PFN_vkAllocationFunction":
    output.add("  PFN_vkAllocationFunction* = proc(pUserData: pointer; size: csize_t; alignment: csize_t; allocationScope: VkSystemAllocationScope): pointer {.cdecl.}\n")
  elif name == "PFN_vkFreeFunction":
    output.add("  PFN_vkFreeFunction* = proc(pUserData: pointer; pMemory: pointer) {.cdecl.}\n")
  elif name == "PFN_vkVoidFunction":
    output.add("  PFN_vkVoidFunction* = proc() {.cdecl.}\n")
  elif name == "PFN_vkDebugReportCallbackEXT":
    output.add("  PFN_vkDebugReportCallbackEXT* = proc(flags: VkDebugReportFlagsEXT; objectType: VkDebugReportObjectTypeEXT; cbObject: uint64; location: csize_t; messageCode:  int32; pLayerPrefix: cstring; pMessage: cstring; pUserData: pointer): VkBool32 {.cdecl.}\n")
  elif name == "PFN_vkDebugUtilsMessengerCallbackEXT":
    output.add("  PFN_vkDebugUtilsMessengerCallbackEXT* = proc(messageSeverity: VkDebugUtilsMessageSeverityFlagBitsEXT, messageTypes: VkDebugUtilsMessageTypeFlagsEXT, pCallbackData: VkDebugUtilsMessengerCallbackDataEXT, userData: pointer): VkBool32 {.cdecl.}\n"):
  else:
    echo "category:funcpointer not found {name}".fmt

proc genStruct(node: XmlNode, output: var string) =
  let name = node.attr("name")

  var vkStruct: VkStruct
  vkStruct.name = name

  output.add("\n  {name}* = object\n".fmt)

  for member in node.findAll("member"):
    var memberName = member.child("name").innerText
    if keywords.contains(memberName):
      memberName = "`{memberName}`".fmt
    var memberType = member.child("type").innerText
    memberType = memberType.translateType()

    var isArray = false
    var arraySize = "0"
    if member.innerText.contains('['):
      arraySize = member.innerText[member.innerText.find('[') + 1 ..< member.innerText.find(']')]
      if arraySize != "":
        isArray = true
      if arraySize == "_DYNAMIC":
        memberType = "ptr " & memberType
        isArray = false

    var depth = member.innerText.count('*')
    if memberType == "pointer":
      depth.dec
    for i in 0 ..< depth:
      memberType = "ptr " & memberType

    memberType = memberType.replace("ptr void", "pointer")
    memberType = memberType.replace("ptr ptr char", "cstringArray")
    memberType = memberType.replace("ptr char", "cstring")

    var vkArg: VkArg
    vkArg.name = memberName
    if not isArray:
      vkArg.argType = memberType
    else:
      vkArg.argType = "array[{arraySize}, {memberType}]".fmt
    vkStruct.members.add(vkArg)

    if not isArray:
      output.add("    {memberName}*: {memberType}\n".fmt)
    else:
      output.add("    {memberName}*: array[{arraySize}, {memberType}]\n".fmt)
  vkStructs.add(vkStruct)

proc genUnion(node: XmlNode, output: var string) =
  let name = node.attr("name")
  output.add("\n  {name}* {{.union.}} = object\n".fmt)
  for member in node.findAll("member"):
    var memberName = member.child("name").innerText
    if keywords.contains(memberName):
      memberName = "`{memberName}`".fmt
    var memberType = member.child("type").innerText
    memberType = memberType.translateType()
    var isArray = false
    var arraySize = "0"
    if member.innerText.contains('['):
      arraySize = member.innerText[member.innerText.find('[') + 1 ..< member.innerText.find(']')]
      if arraySize != "":
        isArray = true
      if arraySize == "_DYNAMIC":
        memberType = "ptr " & memberType
        isArray = false

    var depth = member.innerText.count('*')
    if memberType == "pointer":
      depth.dec
    for i in 0 ..< depth:
      memberType = "ptr " & memberType

    if not isArray:
      output.add("    {memberName}*: {memberType}\n".fmt)
    else:
      output.add("    {memberName}*: array[{arraySize}, {memberType}]\n".fmt)

proc genAlias(node: XmlNode, output: var string) =
  let name = node.attr("name")
  let alias = node.attr("alias")
  output.add("  {name}* = {alias}\n".fmt)

proc genStructs(node: XmlNode, output: var string) =
  output.section("Structs")
  output.add("type\n")
  for t in node.catItems("struct"):
      t.genStruct(output)

proc genFuncPtrs(node: XmlNode, output: var string) =
  output.section("FuncPtrs")
  output.add("type\n")
  for t in node.catItems("funcpointer"):
      t.genFuncPtr(output)

proc genUnions(node: XmlNode, output: var string) =
  output.section("Unions")
  output.add("type\n")
  for t in node.catItems("union"):
      t.genUnion(output)

proc genAliases(node: XmlNode, output: var string) =
  output.section("Aliases")
  output.add("type\n")
  for t in node.catItems("enum"):
    if t.attr("alias") != "":
      t.genAlias(output)

proc genConsts(node: XmlNode, output: var string) =
  echo "Generating and Adding Constants"
  output.add("# Constants\n\nconst\n")
  for enums in node.findAll("enums"):
    let name = enums.attr("name")
    if name == "API Constants":
      for e in enums.items:
        if e.kind != xnElement:
          continue
        let enumName = e.attr("name")
        var enumValue = e.attr("value")
        enumValue = enumValue.replace("(~0U)", "(not 0)")
        enumValue = enumValue.replace("(~0U-1)", "(not 0 - 1)")
        enumValue = enumValue.replace("(~0U-2)", "(not 0 - 2)")
        enumValue = enumValue.replace("(~0ULL)", "(not 0)")
        let alias = e.attr("alias")
        if alias != "":
          enumValue = alias
        output.add("  {enumName}* = {enumValue}\n".fmt)

proc genEnums(node: XmlNode, output: var string) =
  output.section("Enums")
  output.add("type\n")
  for enums in node.findAll("enums"):
    let name = enums.attr("name")
    if name == "API Constants":
      continue
    var elements: OrderedTableRef[int, string] = newOrderedTable[int, string]()
    for e in enums.items:

      if e.kind != xnElement:
        continue
      if e.tag != "enum":
        continue

      let enumName = e.attr("name")
      var enumValueStr = e.attr("value")
      if enumValueStr == "":
        if e.attr("bitpos") == "":
          continue
        let bitpos = e.attr("bitpos").parseInt()
        enumValueStr = $nextPowerOfTwo(bitpos)
      enumValueStr = enumValueStr.translateType()

      var enumValue = 0
      if enumValueStr.contains('x'):
        enumValue = fromHex[int](enumValueStr)
      else:
        enumValue = enumValueStr.parseInt()

      if elements.hasKey(enumValue):
        continue
      elements[enumValue] = enumName

    if elements.len == 0:
      continue

    output.add("  {name}* {{.size: int32.sizeof.}} = enum\n".fmt)
    elements.sort(system.cmp)
    for k, v in elements.pairs:
      if name == "VkStructureType":
        vkStructureTypes.add(v.replace("_", ""))
      output.add("    {v} = {k}\n".fmt)

proc genProcs(node: XmlNode, output: var string) =
  echo "Generating Procedures..."
  output.add("\n# Procs\n")
  output.add("var\n")
  for commands in node.findAll("commands"):
    for command in commands.findAll("command"):
      var vkProc: VkProc
      if command.child("proto") == nil:
        continue
      vkProc.name = command.child("proto").child("name").innerText
      vkProc.rVal = command.child("proto").innerText
      vkProc.rVal = vkProc.rVal[0 ..< vkProc.rval.len - vkProc.name.len]
      while vkProc.rVal.endsWith(" "):
        vkProc.rVal = vkProc.rVal[0 ..< vkProc.rVal.len - 1]
      vkProc.rVal = vkProc.rVal.translateReturnType()

      if vkProc.name == "vkGetTransformFeedbacki_v":
        continue

      for param in command.findAll("param"):
        var vkArg: VkArg
        if param.child("name") == nil:
          continue
        vkArg.name = param.child("name").innerText
        vkArg.argType = param.innerText
        vkArg.argType = vkArg.argType[0 ..< vkArg.argType.len - vkArg.name.len]
        while vkArg.argType.endsWith(" "):
          vkArg.argType = vkArg.argType[0 ..< vkArg.argType.len - 1]

        for part in vkArg.name.split(" "):
          if keywords.contains(part):
            vkArg.name = "`{vkArg.name}`".fmt

        vkArg.argType = vkArg.argType.translateType()

        if param.innerText.contains('['):
          let arraySize = param.innerText[param.innerText.find('[') + 1 ..< param.innerText.find(']')]
          let typ = param.child("type").innerText
          vkArg.argType = "array[{arraySize}, {typ}]".fmt

        vkProc.args.add(vkArg)

      vkProcs.add(vkProc)
      output.add("  {vkProc.name}*: proc(".fmt)
      for arg in vkProc.args:
        if not output.endsWith('('):
          output.add(", ")
        output.add("{arg.name}: {arg.argType}".fmt)
      output.add("): {vkProc.rval} {{.stdcall.}}\n".fmt)

proc genFeatures(node: XmlNode, output: var string) =
  echo "Generating and Adding Features..."
  for feature in node.findAll("feature"):
    let number = feature.attr("number").replace(".", "_")
    output.add("\n# Vulkan {number}\n".fmt)
    output.add("proc vkLoad{number}*() =\n".fmt)

    for command in feature.findAll("command"):
      let name = command.attr("name")
      for vkProc in vkProcs:
        if name == vkProc.name:
          output.add("  {name} = cast[proc(".fmt)
          for arg in vkProc.args:
            if not output.endsWith("("):
              output.add(", ")
            output.add("{arg.name}: {arg.argType}".fmt)
          output.add("): {vkProc.rVal} {{.stdcall.}}](vkGetProc(\"{vkProc.name}\"))\n".fmt)

proc genExtensionsConstants(node: XmlNode, output: var string) =
  echo "Generating and Adding Extensions Constants..."
  output.add("\n#Extensions constants\nconst\n")
  var constants = initOrderedTable[string, string]()
  for extensions in node.findAll("extensions"):
    for extension in extensions.findAll("extension"):
      let name = extension.attr("name")
      for require in extension.findAll("require"):
        for e in require.findAll("enum"):
          let name = e.attr("name")
          let value = e.attr("value")
          if value != "":
            constants[name] = value
  for name,value in constants.pairs:
   output.add("  {name}* = {value}\n".fmt)

proc genExtensions(node: XmlNode, output: var string) =
  echo "Generating and Adding Extensions..."
  for extensions in node.findAll("extensions"):
    for extension in extensions.findAll("extension"):
      let name = extension.attr("name")
      output.add("\n# Load {name}\n".fmt)

      var commands: seq[VkProc]
      for require in extension.findAll("require"):
        for command in require.findAll("command"):
          for vkProc in vkProcs:
            if vkProc.name == command.attr("name"):
              commands.add(vkProc)

      if commands.len == 0:
        continue

      output.add("proc load{name}*() =\n".fmt)

      for vkProc in commands:
        output.add("  {vkProc.name} = cast[proc(".fmt)
        for arg in vkProc.args:
          if not output.endsWith("("):
            output.add(", ")
          output.add("{arg.name}: {arg.argType}".fmt)
        output.add("): {vkProc.rVal} {{.stdcall.}}](vkGetProc(\"{vkProc.name}\"))\n".fmt)

proc genConstructors(node: XmlNode, output: var string) =
  echo "Generating and Adding Constructors..."
  output.add("\n# Constructors\n")
  for s in vkStructs:
    if s.members.len == 0:
      continue
    output.add("\nproc new{s.name}*(".fmt)
    for m in s.members:
      if not output.endsWith('('):
        output.add(", ")
      output.add("{m.name}: {m.argType}".fmt)

      if m.name.contains("flags"):
        output.add(" = 0.{m.argType}".fmt)
      if m.name == "sType":
        for structType in vkStructureTypes:
          if structType.cmpIgnoreStyle("VkStructureType{s.name[2..<s.name.len]}".fmt) == 0:
            output.add(" = VkStructureType{s.name[2..<s.name.len]}".fmt)
      if m.argType == "pointer":
        output.add(" = nil")

    output.add("): {s.name} =\n".fmt)

    for m in s.members:
      output.add("  result.{m.name} = {m.name}\n".fmt)


proc main() =
  if not os.fileExists("vk.xml"):
    discard execCmd("curl -O https://raw.githubusercontent.com/KhronosGroup/Vulkan-Docs/master/xml/vk.xml")

  var output = srcHeader & "\n"

  let file = newFileStream("vk.xml", fmRead)
  let xml = file.parseXml()

  xml.genConsts(output)
  xml.genEnums(output)
  xml.genAliases(output)
  xml.genRequires(output)
  xml.genDefines(output)
  xml.genBaseTypes(output)
  xml.genBitmasks(output)
  xml.genHandles(output)
  xml.genStructs(output)
  xml.genFuncPtrs(output)
  xml.genUnions(output)
  xml.genConstructors(output)
  xml.genProcs(output)
  xml.genFeatures(output)
  xml.genExtensionsConstants(output)
  xml.genExtensions(output)

  output.add("\n" & vkInit)

  writeFile("src/vulkan.nim", output)

if isMainModule:
  main()
