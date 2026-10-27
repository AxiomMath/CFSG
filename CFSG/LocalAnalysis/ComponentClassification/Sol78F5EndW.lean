module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndCS

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.Goldschmidt CFSG.Goldschmidt75
  CFSG.Open CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_isGreatest {B W : Subgroup G} (hW : W ∈ NSet B)
    (hmax : ∀ X ∈ NSet B, X ≤ W) : normalizer (B : Set G) ≤ normalizer (W : Set G) := by
  intro x hx
  have hB : conjSub x B = B := by
    unfold conjSub
    exact (mem_normalizer_iff_map_conj_eq.mp (inv_mem hx))
  have h1 := NSet_conjSub x hW
  rw [hB] at h1
  have h2 : conjSub x W = W := Subgroup.eq_of_le_of_card_ge (hmax _ h1) (by
    unfold conjSub
    rw [card_map_of_injective (MulAut.conj x⁻¹).injective])
  have h3 : x⁻¹ ∈ normalizer (W : Set G) := mem_normalizer_iff_map_conj_eq.mpr h2
  simpa using inv_mem h3

omit [Finite G] in
theorem exists_isKleinFour_of_dihData {D : Subgroup G} {ρ b : G} {j : ℕ} (h : DihData D ρ b j) :
    ∃ V ≤ D, IsKleinFour V := by
  have hc2 := h.z0_sq
  have hcomm : Commute (ρ ^ DihData.zc j) b := (h.z0_central b h.s_mem)
  refine ⟨GorensteinWalter.kleinFourOfCommutingInvolutions _ _ hc2 h.s_sq hcomm, fun x hx => ?_,
    GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _ hc2 h.s_sq h.z0_ne_one
      h.s_ne_one h.s_ne_z0.symm hcomm⟩
  rcases mem_kleinFour_iff.mp hx with e | e | e | e <;> rw [e]
  · exact D.mul_mem (zpow_mem h.ρ_mem _) h.s_mem
  · exact zpow_mem h.ρ_mem _
  · exact h.s_mem
  · exact D.one_mem

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem exists_W (h3 : Asc76.Asc76Theorem3Large) :
    ∃ W : Subgroup G, Odd (Nat.card W) ∧
      (∀ B₁ B₂ : Subgroup G, B₁ ≤ S ⊓ L → B₂ ≤ conjugate (S ⊓ L) s → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
        W ∈ NSet (B₁ ⊔ B₂) ∧ (∀ X ∈ NSet (B₁ ⊔ B₂), X ≤ W) ∧
          normalizer ((B₁ ⊔ B₂ : Subgroup G) : Set G) ≤ normalizer (W : Set G)) ∧
      (∀ t₁ ∈ S ⊓ L, orderOf t₁ = 2 → ∀ t₂ ∈ conjugate (S ⊓ L) s, orderOf t₂ = 2 →
        ⁅oddCent t₁, zpowers t₂⁆ ≤ W ∧ ⁅oddCent t₂, zpowers t₁⁆ ≤ W) := by
  have hR2 : IsPGroup 2 ↥(S ⊓ L) := H.sec5.R_sylow.isPGroup
  have hRs2 : IsPGroup 2 ↥(conjugate (S ⊓ L) s) := hR2.map _
  obtain ⟨ρ, b, j, hD, -⟩ := H.exists_dihData_R
  obtain ⟨ρ', b', j', hD', -⟩ := H.exists_dihData_Rs
  obtain ⟨W, hWodd, hWB, hWc⟩ := Goldschmidt75.exists_W hR2 hRs2 H.R_le_centralizer_Rs
    H.R_inf_Rs (H.coreSep h3) (exists_isKleinFour_of_dihData hD)
    (exists_isKleinFour_of_dihData hD')
  refine ⟨W, hWodd, fun B₁ B₂ h₁ h₂ h₁1 h₂1 => ?_, hWc⟩
  obtain ⟨hW, hmax⟩ := hWB B₁ B₂ h₁ h₂ h₁1 h₂1
  exact ⟨hW, hmax, normalizer_le_of_isGreatest hW hmax⟩

end Hyp

end CFSG.ComponentClassification.Sol78.F514
