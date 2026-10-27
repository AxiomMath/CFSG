module

public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.NineSettingOfHypC

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankThree

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
  CFSG.LocalAnalysis.AGL81TheoremCD.Section14

variable {G : Type} [Group G] [Finite G]

@[expose] def NineTenAt (M : Subgroup G) : Prop :=
  ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H → NineTenConclusion G M E H E q

variable {M : Subgroup G}

theorem nineTenAt_of_gen (h10 : NineTenGen) : NineTenAt M :=
  fun q E H h => h10 G M E H E q h.toNineSettingGen h.mem_H2Fam h.not_mem_sigmaM

end CFSG.LocalAnalysis.AGL81TheoremCD.RankThree
