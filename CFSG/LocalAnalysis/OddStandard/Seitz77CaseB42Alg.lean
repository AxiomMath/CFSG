module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Coord

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

theorem pow_four_eq_self_B42 {k : Type} [Field k] (hk : Nat.card k = 4) (x : k) : x ^ 4 = x := by
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype k := Fintype.ofFinite k
  have := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hk] at this

theorem sq_add_self_add_one_eq_zero_B42 {k : Type} [Field k] (hk : Nat.card k = 4) {x : k}
    (h0 : x ≠ 0) (h1 : x ≠ 1) : x ^ 2 + x + 1 = 0 := by
  have hpow := pow_four_eq_self_B42 hk x
  have h3 : x * (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hpow
  rcases mul_eq_zero.1 h3 with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h h0
    · exact absurd (sub_eq_zero.1 h) h1
  · exact h

theorem eq_of_mul_ne_one_card_four_B42 {k : Type} [Field k] (hk : Nat.card k = 4) {l m : k}
    (hl0 : l ≠ 0) (hl1 : l ≠ 1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hlm : l * m ≠ 1) : l = m := by
  have hl := sq_add_self_add_one_eq_zero_B42 hk hl0 hl1
  have hm := sq_add_self_add_one_eq_zero_B42 hk hm0 hm1
  have h : (l - m) * (l + m + 1) = 0 := by linear_combination hl - hm
  rcases mul_eq_zero.1 h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd (by linear_combination l * h - hl) hlm

theorem ringAut_mul_self_eq_one {k : Type} [Field k] (hk : Nat.card k = 4) (σ : k ≃+* k) :
    σ * σ = 1 := by
  have key : ∀ x : k, σ x = x ∨ σ x = x ^ 2 := by
    intro x
    by_cases h0 : x = 0
    · left
      simp [h0]
    by_cases h1 : x = 1
    · left
      simp [h1]
    have hx2 := sq_add_self_add_one_eq_zero_B42 hk h0 h1
    have hy : (σ x) ^ 2 + σ x + 1 = 0 := by
      have := congrArg σ hx2
      simpa only [map_add, map_pow, map_one, map_zero] using this
    have : (σ x - x) * (σ x - x ^ 2) = 0 := by linear_combination hy + (x - 1 - σ x) * hx2
    rcases mul_eq_zero.1 this with h | h
    · left
      exact sub_eq_zero.1 h
    · right
      exact sub_eq_zero.1 h
  ext x
  rw [RingAut.mul_apply, RingAut.one_apply]
  rcases key x with h | h
  · rw [h, h]
  · rw [h, map_pow, h, ← pow_mul]
    exact pow_four_eq_self_B42 hk x

theorem autField_pow_B42 {F : Type} [Field F] [CharP F 2] (α : MulAut (unipAll F)) (n : ℕ) :
    autField (α ^ n) = autField α ^ n := by
  induction n with
  | zero => exact autField_eq autData_one
  | succ n ih => rw [pow_succ, autField_mul, ih, pow_succ]

theorem autSwap_pow_odd_B42 {F : Type} [Field F] [CharP F 2] (α : MulAut (unipAll F)) (j : ℕ) :
    autSwap (α ^ (2 * j + 1)) = autSwap α := by
  induction j with
  | zero => rw [Nat.mul_zero, Nat.zero_add, pow_one]
  | succ j ih =>
    have h : α ^ (2 * (j + 1) + 1) = α ^ (2 * j + 1) * α * α := by
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring, pow_succ, pow_succ]
    rw [h, autSwap_mul, autSwap_mul, ih]
    cases autSwap α <;> rfl

theorem exists_scalar_of_odd {k : Type} [Field k] (hk : Nat.card k = 4)
    {α : MulAut (unipAll k)} {n : ℕ} (hn : Odd n) (hα : α ^ n = 1)
    (hF₁ : ∀ g ∈ radOne k, α g = g → g = 1)
    (hF₂ : ∃ g : unipAll k, coordB (α g) ≠ coordB g) :
    ∃ μ : k, μ ≠ 0 ∧ μ ≠ 1 ∧
      ∀ g : unipAll k, coordA (α g) = μ * coordA g ∧ coordB (α g) = μ * coordB g := by
  have : CharP k 2 := charP_two_of_card_four_B42 hk
  obtain ⟨σ, l, m, sw, hd⟩ := aut_data α
  obtain ⟨j, hj⟩ := hn
  have hσ : σ = 1 := by
    have h1 : autField (α ^ n) = autField α ^ n := autField_pow_B42 α n
    rw [hα, autField_eq hd, hj, pow_succ, pow_mul, sq, ringAut_mul_self_eq_one hk σ, one_pow,
      one_mul] at h1
    exact h1.symm.trans (autField_eq autData_one)
  have hsw : sw = false := by
    have h1 := autSwap_pow_odd_B42 α j
    rw [← hj, hα, autSwap_eq autData_one, autSwap_eq hd] at h1
    exact h1.symm
  subst hσ
  subst hsw
  have hA : ∀ g, coordA (α g) = (l : k) * coordA g := fun g => by
    rw [hd.coordA_eq]
    simp
  have hB : ∀ g, coordB (α g) = (m : k) * coordB g := fun g => by
    rw [hd.coordB_eq]
    simp
  have hZ : ∀ c : k, α (uelt 0 0 c) = uelt 0 0 ((l : k) * m * c) := fun c => by
    rw [hd.2 c]
    simp
  have hm1 : (m : k) ≠ 1 := by
    intro h
    obtain ⟨g, hg⟩ := hF₂
    apply hg
    rw [hB, h, one_mul]
  have hlm : (l : k) * m ≠ 1 := by
    intro h
    have hmem : (uelt 0 0 1 : unipAll k) ∈ radOne k := (mem_radOne _).2 (by simp)
    have hfix := hF₁ _ hmem (by rw [hZ, h, mul_one])
    have h10 : (uelt 0 0 1 : unipAll k) = uelt 0 0 0 := by rw [hfix, uelt_zero]
    exact one_ne_zero (uelt_inj.1 h10).2.2
  have hl1 : (l : k) ≠ 1 := by
    intro hl
    obtain ⟨γ, hx⟩ : ∃ γ : k, α (uelt 1 0 0) = uelt 1 0 γ := by
      refine ⟨coordC (α (uelt 1 0 0)), ?_⟩
      have h1 : coordA (α (uelt 1 0 0)) = 1 := by rw [hA, hl]; simp
      have h2 : coordB (α (uelt 1 0 0)) = 0 := by rw [hB]; simp
      have := uelt_coords (α (uelt 1 0 0))
      rw [h1, h2] at this
      exact this.symm
    have hy : ∀ c : k, α (uelt 1 0 c) = uelt 1 0 (γ + m * c) := by
      intro c
      rw [uelt_eq_mul, map_mul, hx, hZ c, uelt_mul, uelt_inj]
      refine ⟨by simp, by simp, ?_⟩
      rw [hl]
      ring
    have h1m : (1 - (m : k)) ≠ 0 := sub_ne_zero.2 (Ne.symm hm1)
    have hmem : (uelt 1 0 (γ / (1 - m)) : unipAll k) ∈ radOne k := (mem_radOne _).2 (by simp)
    have hfix := hF₁ _ hmem (by
      rw [hy]
      congr 2
      field_simp
      ring)
    have h10 := congrArg coordA hfix
    simp at h10
  have hlm_eq : (l : k) = m :=
    eq_of_mul_ne_one_card_four_B42 hk l.ne_zero hl1 m.ne_zero hm1 hlm
  refine ⟨l, l.ne_zero, hl1, fun g => ⟨hA g, ?_⟩⟩
  rw [hB, ← hlm_eq]

end CFSG.OddStandard.Seitz77
