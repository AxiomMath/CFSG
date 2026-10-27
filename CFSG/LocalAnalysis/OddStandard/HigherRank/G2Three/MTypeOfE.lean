module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Rows
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Lift

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.ComponentClassification.HarrisLit CFSG.ComponentClassification.HarrisLit.T1

theorem isMTypeSchur_three_of_lieChar {E : Type} [Group E] [Finite E] (hq : CFSG.IsQuasisimple E)
    (hev : Even (Nat.card ↥(center E))) (hL : LieChar 3 (E ⧸ center E))
    (hc : ∀ n r : ℕ, 0 < n → 0 < r →
      ¬ (CFSG.Blueprint.LieModel (E ⧸ center E) .PSL (2 * n) 3 r ∨
        CFSG.Blueprint.LieModel (E ⧸ center E) .PSU (2 * n) 3 r)) :
    IsMTypeSchur 3 E := by
  have h2 : 2 ∣ Nat.card E :=
    (even_iff_two_dvd.mp hev).trans (Subgroup.card_subgroup_dvd_card (center E))
  obtain ⟨h2q, hO⟩ :=
    CFSG.ComponentClassification.HarrisLit.P1.isTwoQuasisimple_of_isQuasisimple hq h2
  have hZ : CFSG.Open.fusionZStar E = center E :=
    CFSG.ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hq hO
  let e := QuotientGroup.quotientMulEquivOfEq hZ
  refine Or.inl ⟨h2q, ?_, ?_, ?_⟩
  · rcases hL with ⟨τ, n, f, hm⟩
    exact ⟨τ, n, f, CFSG.ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv e.symm hm⟩
  · rw [hZ]; exact hev
  · intro n r hn hr h
    exact (hc n r hn hr (h.elim
      (fun hh => Or.inl (CFSG.ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv e hh))
      (fun hh => Or.inr (CFSG.ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv e hh)))).elim

end CFSG.OddStandard.HigherRank.G2Three
