module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwistConjData

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem pairOrder_E (hC : CentData z ι) :
    pairOrder z (ι τ₀) = N10 1 ∧ pairOrder z (z * ι τ₀) = N10 1 ∧
      pairOrder (ι τ₀) (z * ι τ₀) = N10 1 := by
  have h1 : pairOrder z (ι τ₀) = N10 1 := by
    rw [pairOrder, hC.card_inf_centralizer τ₀, two_mul_card_centralizer_perm_ten τ₀_mul_self,
      card_cycleType_of_isSwap isSwap_τ₀]
  have h2 : pairOrder z (z * ι τ₀) = N10 1 := by
    rw [pairOrder_mul_right (p := z) (q := ι τ₀) (hC.comm τ₀), h1]
  refine ⟨h1, h2, ?_⟩
  rw [pairOrder_mul_left (p := z) (q := ι τ₀) (hC.comm τ₀), h1]

theorem pairOrder_z_ne_N10_one (hC : CentData z ι) (i j : Fin 2) :
    pairOrder z (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι ρ₄) ≠ N10 1 := by
  have hρ : ρ₄ * ρ₄ = 1 := by
    rw [← liftS8_ρ₄', ← map_mul, ρ₄'_mul_self, map_one]
  have hcardρ : Multiset.card ρ₄.cycleType = 4 := by
    rw [← liftS8_ρ₄', cycleType_liftS8, card_cycleType_ρ₄']
  have hτσ : (τ₀ * ρ₄) * (τ₀ * ρ₄) = 1 := τ₀_mul_ρ₄_mul_self
  have hcardτρ : Multiset.card (τ₀ * ρ₄).cycleType = 5 := card_cycleType_τ₀_mul_ρ₄
  have key : ∀ k : ℕ, (k = 4 ∨ k = 5) → N10 k ≠ N10 1 := by
    rintro k (rfl | rfl)
    · exact N10_one_ne_four.symm
    · exact N10_one_ne_five.symm
  have h_ne : ∀ {σ : Perm (Fin 10)}, σ * σ = 1 →
      (Multiset.card σ.cycleType = 4 ∨ Multiset.card σ.cycleType = 5) →
      pairOrder z (ι σ) ≠ N10 1 := by
    intro σ hσ hcard
    rw [pairOrder, hC.card_inf_centralizer σ, two_mul_card_centralizer_perm_ten hσ]
    exact key _ hcard
  have hz_ne : ∀ {σ : Perm (Fin 10)}, σ * σ = 1 →
      (Multiset.card σ.cycleType = 4 ∨ Multiset.card σ.cycleType = 5) →
      pairOrder z (z * ι σ) ≠ N10 1 := by
    intro σ hσ hcard
    rw [pairOrder_mul_right (p := z) (q := ι σ) (hC.comm σ)]
    exact h_ne hσ hcard
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one]
  · exact h_ne hρ (Or.inl hcardρ)
  · rw [← map_mul]
    exact h_ne hτσ (Or.inr hcardτρ)
  · exact hz_ne hρ (Or.inl hcardρ)
  · rw [mul_assoc, ← map_mul]
    exact hz_ne hτσ (Or.inr hcardτρ)

theorem pairOrder_x_ne_N10_one [Finite G] (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (i j : Fin 2) :
    pairOrder (ι τ₀) (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι ρ₄) ≠ N10 1 := by
  obtain ⟨ι₁, ε, χ, D⟩ := exists_twistData hC hx
  have hpair1 := D.pair_one ρ₄' ρ₄'_mul_self
  rw [liftS8_ρ₄', card_cycleType_ρ₄'] at hpair1
  have hpair2 := D.pair_z ρ₄' ρ₄'_mul_self
  rw [liftS8_ρ₄', card_cycleType_ρ₄'] at hpair2
  have hkey : ∀ k : ℕ, (k = 4 ∨ k = 5) → N10 k ≠ N10 1 := by
    rintro k (rfl | rfl)
    · exact N10_one_ne_four.symm
    · exact N10_one_ne_five.symm
  have h1ne : pairOrder (ι τ₀) (ι ρ₄) ≠ N10 1 := by
    rw [hpair1]
    apply hkey
    by_cases hε : ε ρ₄' = -1
    · right; norm_num [if_pos hε]
    · left; norm_num [if_neg hε]
  have h2ne : pairOrder (ι τ₀) (z * ι ρ₄) ≠ N10 1 := by
    rw [hpair2]
    apply hkey
    by_cases hε : ε ρ₄' = -1
    · left; norm_num [if_pos hε]
    · right; norm_num [if_neg hε]
  have hxt : ι τ₀ * z = z * ι τ₀ := (hC.comm τ₀).symm
  have hxρ : ι τ₀ * ι ρ₄ = ι ρ₄ * ι τ₀ := by
    have h := mem_centralizer_singleton_iff.1 (ι_liftS8_mem_centralizer ι ρ₄')
    rw [liftS8_ρ₄'] at h
    exact h.symm
  have hxq : ι τ₀ * (z * ι ρ₄) = (z * ι ρ₄) * ι τ₀ := by
    calc ι τ₀ * (z * ι ρ₄) = (ι τ₀ * z) * ι ρ₄ := by group
      _ = (z * ι τ₀) * ι ρ₄ := by rw [hxt]
      _ = z * (ι τ₀ * ι ρ₄) := by group
      _ = z * (ι ρ₄ * ι τ₀) := by rw [hxρ]
      _ = (z * ι ρ₄) * ι τ₀ := by group
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one]
  · exact h1ne
  · rw [pairOrder_mul_right hxρ]
    exact h1ne
  · exact h2ne
  · have heq : z * ι τ₀ * ι ρ₄ = ι τ₀ * (z * ι ρ₄) := by
      calc z * ι τ₀ * ι ρ₄ = (z * ι τ₀) * ι ρ₄ := by group
        _ = (ι τ₀ * z) * ι ρ₄ := by rw [hC.comm τ₀]
        _ = ι τ₀ * (z * ι ρ₄) := by group
    rw [heq, pairOrder_mul_right hxq]
    exact h2ne

theorem pairOrder_x₂_ne_N10_one [Finite G] (hC : CentData z ι) (hP1 : IsConj z (z * ι τ₀))
    (i j : Fin 2) :
    pairOrder (z * ι τ₀) (z ^ (i : ℕ) * (ι τ₀) ^ (j : ℕ) * ι ρ₄) ≠ N10 1 := by
  obtain ⟨ι', hC', h1', h2'⟩ := hC.exists_twist
  have hx1 : ι' τ₀ = z * ι τ₀ := h2' τ₀ sign_τ₀
  have hsignρ₄ : sign ρ₄ = 1 := by rw [← liftS8_ρ₄', sign_liftS8, sign_ρ₄']
  have hρ : ι' ρ₄ = ι ρ₄ := h1' ρ₄ hsignρ₄
  have hx' : IsConj z (ι' τ₀) := by rw [hx1]; exact hP1
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one]
  · have h := pairOrder_x_ne_N10_one (hC := hC') (hx := hx') (i := 0) (j := 0)
    simp only [Fin.val_zero, pow_zero, one_mul] at h
    rw [hx1, hρ] at h
    exact h
  · have h := pairOrder_x_ne_N10_one (hC := hC') (hx := hx') (i := 1) (j := 1)
    simp only [Fin.val_one, pow_one] at h
    rw [hx1, hρ] at h
    have heq : z * (z * ι τ₀) * ι ρ₄ = ι τ₀ * ι ρ₄ := by
      rw [← mul_assoc, hC.mul_self, one_mul]
    rw [heq] at h
    exact h
  · have h := pairOrder_x_ne_N10_one (hC := hC') (hx := hx') (i := 1) (j := 0)
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at h
    rw [hx1, hρ] at h
    exact h
  · have h := pairOrder_x_ne_N10_one (hC := hC') (hx := hx') (i := 0) (j := 1)
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one] at h
    rw [hx1, hρ] at h
    exact h

end CFSG.OddStandard.AltStdSec.SwapPartner
