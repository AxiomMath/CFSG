module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitCompAt

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

theorem layerBalanceKAt_of_lemma15At {G : Type} [Group G] [Finite G] (h15 : FS79Lemma15At G) :
    LayerBalanceKAt G := by
  intro hkp hO S t hS ht2 htS _ K hK
  have h1 := (h15 hkp S hS).1 (zpowers t) (zpowers_le.2 htS)
  rw [(h15 hkp S hS).2 hO,
    (h15 hkp (zpowers t) (isPGroup_zpowers_of_orderOf_two ht2)).2 hO] at h1
  exact (le_layerIn_of_isCompIn hK).trans h1

end CFSG.EvenSporadicStandard.Induction.Junction
