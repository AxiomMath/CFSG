module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarFive
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarCent

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.RankTwoStandard
  CFSG.OddStandard.AltStdBal

section Thirteen

variable {G : Type} [Group G] [Finite G] {z : G} (O : OverData G z 13)

theorem l0Normal_thirteen (htri : ExactShapeTrichotomy) {R : Subgroup (Perm (Fin (13 + 3)))}
    (hR : SecR 13 R) (hK : CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G)))
    (hKf : CFSG.SectionRank.IsKGroupCat (fiveC O)) : L0Normal O R :=
  l0Normal_of_not_hn O hR htri hK (by norm_num) (fun _ =>
    not_hnOutcome_of_bound O hR (fun T hT2 hTP hTf =>
      card_dvd_of_two_subgroup O (card_secFive O htri hKf) hR T hT2 hTP hTf))

end Thirteen

section Main

theorem shapeTwoCentDoubleAt_fourteen (htri : ExactShapeTrichotomy)
    (hR2 : RankTwoAlternatingStandard) : ShapeTwoCentDoubleAt 14 := by
  refine centDoubleAt_of_l0 hR2 (m := 13) (by norm_num) ?_
  intro G _ _ z O h4 hK hne
  obtain ⟨hKE, hKy⟩ := isKGroupCat_secP O h4 hK hne
  have hf1 : O.φ fiveCyc ≠ 1 := by
    intro h1
    have : fiveCyc = 1 := O.φ_injective (h1.trans (map_one _).symm)
    exact absurd this (by decide)
  have hKf : CFSG.SectionRank.IsKGroupCat (fiveC O) := hK _ (hne _ hf1)
  exact ⟨l0Normal_thirteen O htri (secR_klein (by omega)) hKE hKf,
    l0Normal_thirteen O htri (secR_cyc (by omega)) hKy hKf⟩

theorem shapeTwoCaseIIClassification_of_rankTwo' (htri : ExactShapeTrichotomy)
    (hR2 : RankTwoAlternatingStandard) : ShapeTwoCaseIIClassification :=
  shapeTwoCaseIIClassification_of_rankTwo htri hR2 (shapeTwoCentDoubleAt_fourteen htri hR2)

end Main

end CFSG.OddStandard.AltStdSec
