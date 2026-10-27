module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Rows

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup Assembly.LowTwoRank

theorem twoNilpFor_suzuki : TwoNilpFor fun Y _ => ∃ p f : ℕ, Blueprint.SuzukiModel Y p f :=
  fun _ _ _ hY _ _ _ _ _ => Or.inr (Or.inl hY)

end CFSG.ComponentClassification.HarrisLit.L33
