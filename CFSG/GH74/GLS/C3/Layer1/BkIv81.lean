module

public import CFSG.GH74.GLS.C3.Layer1.BkIv81Core
public import CFSG.GH74.GLS.C3.Layer1.Back112Claim

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

theorem b_iv2_8_1_proof : B_iv2_8_1 := by
  intro G _ _ hGs M L Q hM hL hLn hQ hΓ g hR hLg
  have hG : IsSimpleGroup G := hGs.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCle : CMK M L ≤ M := fun c hc => (U1a.mem_CMK_iff.1 hc).1
  obtain ⟨P₀, hQP₀⟩ := (hQ.isPGroup.comap_subtype (K := M)).exists_le_sylow
  have hS₁ : IsSylowOf 2 ((P₀ : Subgroup ↥M).map M.subtype) M := ⟨P₀, rfl⟩
  set S₁ := (P₀ : Subgroup ↥M).map M.subtype with hS₁def
  have hQS₁ : Q ≤ S₁ := by
    intro q hq
    exact ⟨⟨q, hQ.le.trans hCle hq⟩, hQP₀ hq, rfl⟩
  have hQeq : S₁ ⊓ CMK M L = Q :=
    hQ.eq_of_le (le_inf hQS₁ hQ.le) inf_le_right (hS₁.isPGroup.to_inf_left)
  set R := conjugate Q g ⊓ M with hRdef
  have hR2 : IsPGroup 2 R := (isPGroup_conjugate' hQ.isPGroup g).to_le inf_le_left
  obtain ⟨k, hk, hkR⟩ := C3.Layer2.exists_mem_conj_le_of_isSylowOf hS₁ inf_le_right hR2
  have hconj : conjugate Q (g * k) ⊓ M = conjugate R k := by
    rw [conjugate_mul', hRdef, conjugate_inf', conjugate_of_mem hk]
  have hR' : conjugate Q (g * k) ⊓ M ≠ ⊥ := by
    rw [hconj]
    intro hb
    apply hR
    exact (Subgroup.map_eq_bot_iff_of_injective R
      (show Function.Injective (MulAut.conj k⁻¹).toMonoidHom from (MulAut.conj k⁻¹).injective)).mp hb
  have hRn : conjugate Q (g * k) ⊓ M ≤ normalizer (Q : Set G) := by
    intro y hy
    rw [hconj, mem_conjugate_iff'] at hy
    have hyS₁ : y ∈ S₁ := by
      have := hkR _ hy
      have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
      rwa [e] at this
    have hyM : y ∈ M := hS₁.le hyS₁
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      rw [← hQeq] at hq ⊢
      exact ⟨S₁.mul_mem (S₁.mul_mem hyS₁ hq.1) (S₁.inv_mem hyS₁),
        Back.conj_mem_CMK hLn hyM hq.2⟩
    · intro hq
      rw [← hQeq] at hq ⊢
      have h1 : y⁻¹ * (y * q * y⁻¹) * y = q := by group
      refine ⟨?_, ?_⟩
      · have := S₁.mul_mem (S₁.mul_mem (S₁.inv_mem hyS₁) hq.1) hyS₁
        rwa [h1] at this
      · have := Back.conj_mem_CMK hLn (M.inv_mem hyM) hq.2
        have e : y⁻¹ * (y * q * y⁻¹) * y⁻¹⁻¹ = q := by group
        rwa [e] at this
  have hLg' : L ≤ conjugate M (g * k) := by
    intro x hx
    rw [mem_conjugate_iff']
    have h1 : k * x * k⁻¹ ∈ L := hLn k hk x hx
    have h2 := mem_conjugate_iff'.1 (hLg h1)
    have e : g * k * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
    rw [e]
    exact h2
  have hgk : g * k ∈ M := key_normalized hG hM hL hLn hQ hΓ hR' hRn hLg'
  have := M.mul_mem hgk (M.inv_mem hk)
  simpa using this

end CFSG.GH74.GLS.C3.Layer1.Bk
