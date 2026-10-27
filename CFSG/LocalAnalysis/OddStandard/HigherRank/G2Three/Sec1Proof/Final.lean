module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LAssemble
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.BrModel
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Reduction

public section

namespace CFSG.OddStandard.HigherRank.G2Three

theorem g23Facts_holds :
    G23Facts :=
  Sec1Proof.g23Facts_of_inputs Sec1Proof.g23_model_exists
    (fun _ _ _ m => Sec1Proof.Tab.facts_of_model m)

end CFSG.OddStandard.HigherRank.G2Three
