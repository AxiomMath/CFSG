module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def zT0Tabs (ET : Array Tab) : Array Tab :=
  ET.filter fun z => allBelow (wordTabs wT₀).size fun i => commT z (wordTabs wT₀)[i]!

@[expose] def r2Tabs (ER ES ZT : Array Tab) : Array Tab :=
  ER.filter fun y => (powTab y 4 == idTab 42) && (allBelow ZT.size fun i => commT y ZT[i]!) &&
    !found (indexOf ES) ES y

@[expose] def r2PairsOK (N ES : Array Tab) : Bool :=
  let iS := indexOf ES
  allBelow N.size fun i => allBelow N.size fun j =>
    invOK N[j]! && (!(powTab (comp 42 N[i]! (invTab 42 N[j]!)) 4 == idTab 42) ||
      found iS ES (comp 42 N[i]! (invTab 42 N[j]!)))

@[noinline, expose] def graphIdxOK : Bool :=
  let ER := enumBFS 42 gTabs 241920
  let ES := enumBFS 42 gensS 20160
  let ET := enumBFS 42 (wordTabs wT₀) 64
  r2PairsOK (r2Tabs ER.tabs ES.tabs (zT0Tabs ET.tabs)) ES.tabs

end CFSG.ComponentClassification.GrSLit.GrS4
