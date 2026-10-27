module

public import CFSG.Sporadic.Schreier.LyR3EFusion

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

theorem eq_top_of_conj_invol
    {L : Subgroup J} (hCL : lyC ≤ L) {l t : J} (hl : l ∈ L) (htC : t ∈ lyC)
    (ht2 : orderOf t = 2) (htz : t ≠ lyz) (hlt : l * lyz * l⁻¹ = t) : L = ⊤ := by
  have hSC : (lySylow : Subgroup J) ≤ lyC := lyS_le_lyC
  obtain ⟨c₁, hc₁, hc₁t⟩ : ∃ c ∈ lyC, c * t * c⁻¹ ∈ lyS := by
    have hp : IsPGroup 2 (Subgroup.zpowers (⟨t, htC⟩ : ↥lyC)) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
      exact ht2
    obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥lyC Q (lySylow.subtype hSC)
    have hmem := Subgroup.smul_mem_pointwise_smul (⟨t, htC⟩ : ↥lyC) (MulAut.conj g)
      (Q : Subgroup ↥lyC) (hQ (Subgroup.mem_zpowers _))
    rw [← Sylow.coe_subgroup_smul, hg, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
    refine ⟨g, g.2, ?_⟩
    simpa [MulAut.smul_def, lySylow_coe] using hmem
  have hs2 : orderOf (c₁ * t * c₁⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c₁) t
    rw [MulAut.conj_apply] at this
    rw [this, ht2]
  have hnc : ¬∀ x ∈ lyS, x * (c₁ * t * c₁⁻¹) = (c₁ * t * c₁⁻¹) * x := by
    intro hc
    have hcen : (⟨c₁ * t * c₁⁻¹, hc₁t⟩ : lyS) ∈ Subgroup.center lyS := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hc g.1 g.2
    rw [center_lyS, mem_zpowers_zS] at hcen
    rcases hcen with h | h
    · have h0 := congrArg Subtype.val h
      rw [Subgroup.coe_one] at h0
      have h1 : c₁ * t * c₁⁻¹ = 1 := h0
      rw [h1, orderOf_one] at hs2
      exact absurd hs2 (by norm_num)
    · have h0 := congrArg Subtype.val h
      have h1 : c₁ * t * c₁⁻¹ = lyz := h0
      have hcz : c₁ * lyz = lyz * c₁ := by
        rw [lyC_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hc₁
        exact hc₁
      apply htz
      calc t = c₁⁻¹ * (c₁ * t * c₁⁻¹) * c₁ := by group
        _ = c₁⁻¹ * lyz * c₁ := by rw [h1]
        _ = lyz := by rw [mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨c₂, hc₂, hc₂f⟩ := conj_to_f hc₁t hs2 hnc
  refine (eq_top_of_conj_lyf hCL ⟨c₂⁻¹ * c₁ * l, L.mul_mem (L.mul_mem (L.inv_mem (hCL hc₂))
    (hCL hc₁)) hl, ?_⟩).1
  calc c₂⁻¹ * c₁ * l * lyz * (c₂⁻¹ * c₁ * l)⁻¹
      = c₂⁻¹ * (c₁ * (l * lyz * l⁻¹) * c₁⁻¹) * c₂ := by group
    _ = c₂⁻¹ * (c₁ * t * c₁⁻¹) * c₂ := by rw [hlt]
    _ = c₂⁻¹ * (c₂ * lyf * c₂⁻¹) * c₂ := by rw [hc₂f]
    _ = lyf := by group

end CFSG.AGLEmbedding.R3
