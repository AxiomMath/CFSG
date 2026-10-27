module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalCertInputs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[noinline, expose] def borelOK : Bool :=
  let ET := enumBFS 42 (wordTabs wT₀) 64
  let EB := enumBFS 42 (wordTabs wB₀) 192
  allBelow EB.tabs.size fun i =>
    found (indexOf ET.tabs) ET.tabs EB.tabs[i]! ||
      [4, 8, 12].all fun k => !(comp 42 EB.tabs[i]! (tgT k) == comp 42 (tgT k) EB.tabs[i]!)

end CFSG.ComponentClassification.GrSLit.L34Facts
