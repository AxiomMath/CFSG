module

public import CFSG.LargeExtraspecial.OutSixSigma
public import CFSG.LargeExtraspecial.OutSixSigmaU
public import CFSG.LargeExtraspecial.BridgeConclusion
public import CFSG.LargeExtraspecial.OfFStar

public section

namespace CFSG.LargeExtraspecial.Bridge

open Subgroup CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

theorem TimmesfeldAlt5.exists_sigma {w : ℕ} {Mbar : Type} [Group Mbar] [Finite Mbar]
    (h : TimmesfeldAlt5 w Mbar) :
    ∃ σ : Mbar, σ * σ = 1 ∧ timmesfeldFStar Mbar ⊔ Subgroup.zpowers σ = ⊤ := by
  obtain ⟨-, hidx, hF⟩ := h
  have : (timmesfeldFStar Mbar).Normal := timmesfeldFStar_normal Mbar
  have hC : centralizer (timmesfeldFStar Mbar : Set Mbar) ≤ timmesfeldFStar Mbar :=
    CFSG.Adapters.generalized_fitting_self_centralizing Mbar
  rcases hF with hL | hU
  · obtain ⟨e⟩ := hL
    exact S14.exists_sigma_of_psl_six _ e hC
  · obtain ⟨e⟩ := hU
    obtain ⟨τ, hτ, hτi⟩ := S14.exists_outer_involution_timmesfeldPSU_six
    have hpos : (timmesfeldFStar Mbar).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hdvd : (timmesfeldFStar Mbar).index ∣ 2 := by
      rcases (show (timmesfeldFStar Mbar).index = 1 ∨ (timmesfeldFStar Mbar).index = 2 by omega)
        with h1 | h2
      · rw [h1]
        exact one_dvd 2
      · rw [h2]
    exact S14.exists_sigma_of_outer_involution _ e hC S14.center_timmesfeldPSU_six
      (by rw [S14.card_outer_timmesfeldPSU_six]; decide) τ hτ hτi hdvd

theorem TimmesfeldConclusion.toPrinted {G : Type*} [Group G] {w : ℕ} {Mbar : Type}
    [Group Mbar] [Finite Mbar] (h : TimmesfeldConclusion G w Mbar) :
    TimmesfeldPrintedConclusion G w Mbar := by
  rcases (timmesfeldConclusion_iff.mp h) with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5.1, h5.2.1, h5.2.2, h5.exists_sigma⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h8))))))

theorem printed_of_mainStatement (h : MainStatement) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (z : G) (hz : orderOf z = 2)
    (hext : timmesfeldIsExtraspecial (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))))
    (w : ℕ)
    (hw : Nat.card (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) = 2 ^ (1 + 2 * w))
    (Mbar : Type) [Group Mbar]
    (hMbar : timmesfeldQuotientIso (timmesfeldFStar (Subgroup.centralizer ({z} : Set G))) Mbar) :
    TimmesfeldPrintedConclusion G w Mbar := by
  have : Finite Mbar := by
    obtain ⟨φ, hφ, -⟩ := hMbar
    exact Finite.of_surjective φ hφ
  exact (h G hnonab z hz hext w hw Mbar hMbar).toPrinted

end CFSG.LargeExtraspecial.Bridge
