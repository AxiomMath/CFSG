module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLDisp
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLNs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSL3
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLGrMain

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

theorem oddLieCoreFamilyInput_psl :
    OddLieCoreFamilyInput .PSL :=
  oddLieCoreFamilyInput_psl_of fun _ _ _ hp2 hf _ hn hZ i hi _ hRodd hRi hRc =>
    commute_psl_of
      (@fun _ _ _ hp2 hf _ hn hZ A σ hi _ hRodd hRi hRc =>
        commute_graphField hp2 hf hn hZ A σ hi hRodd hRi hRc)
      commute_inner_three commute_inner_nonsplit hp2 hf hn hZ i hi hRodd hRi hRc

end CFSG.ComponentClassification.Foote5.OddLieCore
