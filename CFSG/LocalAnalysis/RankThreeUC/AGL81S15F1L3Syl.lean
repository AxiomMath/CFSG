module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open CFSG.ABGLocalTools
open scoped Pointwise

section Syl

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem exists_isSylowOf_two_ge {R H : Subgroup Ω} (hR : IsPGroup 2 R) (hRH : R ≤ H) :
    ∃ T : Subgroup Ω, R ≤ T ∧ IsSylowOf 2 T H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hR.comap_subtype (K := H)).exists_le_sylow
  exact ⟨Q.map H.subtype, fun x hx => ⟨⟨x, hRH hx⟩, hQ hx, rfl⟩, Q, rfl⟩

theorem exists_conj_of_isSylowOf_two {T₁ T₂ H : Subgroup Ω} (h₁ : IsSylowOf 2 T₁ H)
    (h₂ : IsSylowOf 2 T₂ H) : ∃ x ∈ H, ∀ y : Ω, y ∈ T₂ ↔ x⁻¹ * y * x ∈ T₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₁, rfl⟩ := h₁
  obtain ⟨Q₂, rfl⟩ := h₂
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H Q₁ Q₂
  have hmem : ∀ s : H, s ∈ Q₂ ↔ h⁻¹ * s * h ∈ Q₁ := by
    intro s
    rw [← hh]
    have : s ∈ ((h • Q₁ : Sylow 2 H) : Subgroup H) ↔ s ∈ MulAut.conj h • (Q₁ : Subgroup H) := by
      rw [Sylow.coe_subgroup_smul]
    rw [show (s ∈ (h • Q₁ : Sylow 2 H)) ↔ s ∈ ((h • Q₁ : Sylow 2 H) : Subgroup H) from Iff.rfl,
      this, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp
    exact Iff.rfl
  refine ⟨h, h.2, fun y => ?_⟩
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact ⟨_, (hmem y').1 hy', by simp⟩
  · rintro ⟨y', hy', hy⟩
    have hyH : y ∈ H := by
      have : (h : Ω)⁻¹ * y * h = y' := hy.symm
      have h1 : y = h * y' * (h : Ω)⁻¹ := by rw [← this]; group
      rw [h1]
      exact H.mul_mem (H.mul_mem h.2 y'.2) (H.inv_mem h.2)
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    refine (hmem ⟨y, hyH⟩).2 ?_
    have : (h : H)⁻¹ * ⟨y, hyH⟩ * h = y' := Subtype.ext hy.symm
    rw [this]
    exact hy'

theorem normalizer_le_of_central_involution {W Y₁ : Subgroup Ω} (hYW : Y₁ ≤ W)
    (hodd : ¬ 2 ∣ Y₁.relIndex W) {z : Ω} (hz : z ∈ Y₁) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hcen : ∀ y ∈ Y₁, y * z = z * y) (hcent : ∀ n : Ω, n * z = z * n → n ∈ Y₁)
    (huniq : ∀ S₁ : Subgroup Ω, S₁ ≤ Y₁ → ¬ 2 ∣ S₁.relIndex Y₁ → ∀ t ∈ S₁,
      (∀ s ∈ S₁, s * t = t * s) → t * t = 1 → t = 1 ∨ t = z)
    {S : Subgroup Ω} (hS : IsSylowOf 2 S W) : Subgroup.normalizer (S : Set Ω) ≤ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := by
    have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨S₁, hzS₁, hS₁⟩ := exists_isSylowOf_two_ge hzp (Subgroup.zpowers_le.mpr hz)
  have hzin : z ∈ S₁ := hzS₁ (Subgroup.mem_zpowers z)
  have hS₁Y : S₁ ≤ Y₁ := hS₁.le
  have hS₁W : IsSylowOf 2 S₁ W := by
    rw [isSylowOf_iff] at hS₁ ⊢
    obtain ⟨_, hp, hidx⟩ := hS₁
    refine ⟨hS₁Y.trans hYW, hp, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex S₁ Y₁ W hS₁Y hYW]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
    · exact hidx h
    · exact hodd h
  obtain ⟨k, hkW, hk⟩ := exists_conj_of_isSylowOf_two hS₁W hS
  intro n hn
  rw [Subgroup.mem_normalizer_iff] at hn
  set n' : Ω := k⁻¹ * n * k with hn'
  have hnorm : ∀ x : Ω, x ∈ S₁ ↔ n' * x * n'⁻¹ ∈ S₁ := by
    intro x
    have h1 : x ∈ S₁ ↔ k * x * k⁻¹ ∈ S := by
      rw [hk]
      have : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      rw [this]
    have h2 : k * x * k⁻¹ ∈ S ↔ n * (k * x * k⁻¹) * n⁻¹ ∈ S := hn _
    have h3 : n * (k * x * k⁻¹) * n⁻¹ ∈ S ↔ n' * x * n'⁻¹ ∈ S₁ := by
      rw [hk]
      have : k⁻¹ * (n * (k * x * k⁻¹) * n⁻¹) * k = n' * x * n'⁻¹ := by
        simp only [hn', mul_inv_rev, inv_inv]
        group
      rw [this]
    rw [h1, h2, h3]
  set t : Ω := n' * z * n'⁻¹ with ht
  have htS : t ∈ S₁ := (hnorm z).mp hzin
  have htc : ∀ s ∈ S₁, s * t = t * s := by
    intro s hs
    have hs' : n'⁻¹ * s * n' ∈ S₁ := by
      rw [hnorm]
      have : n' * (n'⁻¹ * s * n') * n'⁻¹ = s := by group
      rw [this]
      exact hs
    have h1 := hcen _ (hS₁Y hs')
    have : s * t = n' * ((n'⁻¹ * s * n') * z) * n'⁻¹ := by
      simp only [ht]; group
    have h2 : t * s = n' * (z * (n'⁻¹ * s * n')) * n'⁻¹ := by
      simp only [ht]; group
    rw [this, h2, h1]
  have htt : t * t = 1 := by
    have : t * t = n' * (z * z) * n'⁻¹ := by simp only [ht]; group
    rw [this, hz2]; group
  rcases huniq S₁ hS₁Y (isSylowOf_iff.mp hS₁).2.2 t htS htc htt with h | h
  · exfalso
    apply hz1
    have : n' * z * n'⁻¹ = 1 := h
    have h' := mul_inv_eq_one.mp this
    simpa using h'
  · have hcz : n' * z = z * n' := by
      have : n' * z * n'⁻¹ = z := h
      exact (mul_inv_eq_iff_eq_mul.mp this)
    have hn'Y : n' ∈ Y₁ := hcent n' hcz
    have : n = k * n' * k⁻¹ := by simp only [hn']; group
    rw [this]
    exact W.mul_mem (W.mul_mem hkW (hYW hn'Y)) (W.inv_mem hkW)

end Syl

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
