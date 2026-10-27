module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab65A

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

private theorem conj_mem_inf_Gx {G : Type} [Group G] {y c s k : G} (hk : k ∈ Gx y)
    (hs : s ∈ Gx y ⊓ Gx c) : k * s * k⁻¹ ∈ Gx y ⊓ Gx (k * c * k⁻¹) := by
  obtain ⟨hsy, hsc⟩ := Subgroup.mem_inf.1 hs
  refine Subgroup.mem_inf.2 ⟨(Gx y).mul_mem ((Gx y).mul_mem hk hsy) ((Gx y).inv_mem hk), ?_⟩
  rw [mem_Gx] at hsc ⊢
  calc k * c * k⁻¹ * (k * s * k⁻¹) = k * (c * s) * k⁻¹ := by group
    _ = k * (s * c) * k⁻¹ := by rw [hsc]
    _ = k * s * k⁻¹ * (k * c * k⁻¹) := by group

private theorem symm_mem_inf_Gx {H H' : Type} [Group H] [Group H'] (Ψ : H ≃* H') {y c : H}
    {t : H'} (ht : t ∈ Gx (Ψ y) ⊓ Gx (Ψ c)) : Ψ.symm t ∈ Gx y ⊓ Gx c := by
  obtain ⟨hy, hc⟩ := Subgroup.mem_inf.1 ht
  rw [mem_Gx] at hy hc
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_Gx]
    apply Ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy
  · rw [mem_Gx]
    apply Ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hc

section Cert


theorem suborbitFacts_tableVI_5A_b :
    ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
      ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
        ∀ y : H, IsConj (a * z) y → ∀ c ∈ tab6Set a z b z₁ y 5,
          ∃ s ∈ Gx y ⊓ Gx c, IsConj b s := by
  intro H _ E h a z b z₁ hf hd y hy c hc
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover h.toIsHSCover)
  obtain ⟨Ψ, hΨ, hΨy⟩ := exists_labelled_iso_at_az h hf hd hy
  have hc' : Ψ c ∈ tab6Set pA pZ pB pZ₁ (pA * pZ) 5 := by
    have h1 := (mem_tab6Set_map Ψ a z b z₁ y c 5).2 hc
    rwa [hΨy, hΨ.a_eq, tab6Set_congr pA_mem_center' hΨ.z_conj hΨ.b_conj hΨ.z₁_conj] at h1
  obtain ⟨k, hk, hkc⟩ := ((tableVI_P hP).partition.orbit 5).transitive _ (tab6C_mem_set hP 5) _ hc'
  obtain ⟨s₀, hs₀, hs₀b⟩ := tab6_5A_b hP
  have hs' := conj_mem_inf_Gx hk hs₀
  rw [hkc] at hs'
  refine ⟨Ψ.symm (k * s₀ * k⁻¹), symm_mem_inf_Gx Ψ (by rw [hΨy]; exact hs'), ?_⟩
  have h1 : IsConj (Ψ b) (k * s₀ * k⁻¹) :=
    hΨ.b_conj.symm.trans (hs₀b.trans (isConj_iff.2 ⟨k, rfl⟩))
  exact TwoHSData.isConj_of_map_mulEquiv Ψ (by rwa [MulEquiv.apply_symm_apply])

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3
