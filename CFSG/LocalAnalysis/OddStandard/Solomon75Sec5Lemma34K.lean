module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalAssembly
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma34Full

public section

namespace CFSG.OddStandard.Solomon75

theorem solomon75Lemma34K : Solomon75Lemma34K := by
  intro X _ _ n z Z _ hA hn hp
  exact lemma34K_full hA hn hp

end CFSG.OddStandard.Solomon75
