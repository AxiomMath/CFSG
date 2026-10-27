module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011S4aCases
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma411f

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Proofs2

theorem l2011S4a :
    ∀ (K : Type) [Group K] [Finite K] (ε : ℤ) (q : ℕ), (ε = 1 ∨ ε = -1) → Odd q → 3 < q →
      ¬ ((q : ℤ) ≡ ε [ZMOD 8]) → IVK.IsLnEps 4 K ε q →
      ∀ (P : Sylow 2 K) (z : K), z ∈ (P : Subgroup K) → orderOf z = 2 →
        (∀ x ∈ (P : Subgroup K), x * z = z * x) →
        ∀ I₁ I₂ : Subgroup K, I₁ ⊔ I₂ = IVK.Ez z → (∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) →
          I₁ ⊓ I₂ = zpowers z → HasSL2Model ↥I₁ (fun r => r = q) → HasSL2Model ↥I₂ (fun r => r = q) →
          ∃ y ∈ (P : Subgroup K), orderOf y = 2 ∧ y ≠ z ∧ IsConj z y ∧
            y ∈ normalizer (I₁ : Set K) ∧ y ∈ normalizer (I₂ : Set K) := by
  intro K _ _ ε q hε hodd hq3 h8 hK P z hzP hz2 hzc I₁ I₂ hI hcomm hinter hsl₁ hsl₂
  by_cases h4 : (q : ℤ) ≡ ε [ZMOD 4]
  · exact s4a_fused hodd hq3 P hzc hz2 hI hcomm hinter hsl₁ hsl₂
      (ivk_4_11f K ε q hε hodd hq3 h8 hK h4)
  · have hK' : (q % 4 = 3 ∧ IVK.IsLnEps 4 K 1 q) ∨ (q % 4 = 1 ∧ IVK.IsLnEps 4 K (-1) q) := by
      rcases hε with rfl | rfl
      · left
        refine ⟨?_, hK⟩
        obtain ⟨k, hk⟩ := hodd
        have : ¬ ((q : ℤ) % 4 = 1 % 4) := h4
        omega
      · right
        refine ⟨?_, hK⟩
        obtain ⟨k, hk⟩ := hodd
        have : ¬ ((q : ℤ) % 4 = (-1) % 4) := h4
        omega
    exact s4a_nonfused hodd (by omega) hK' P hzP hz2 hzc hI hcomm hsl₁ hsl₂

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
