module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1UnFix

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K]

abbrev ue1 : HypIndex 2 0 := Sum.inl 0

abbrev ue2 : HypIndex 2 0 := Sum.inl 1

abbrev uf1 : HypIndex 2 0 := Sum.inr (Sum.inr 0)

abbrev uf2 : HypIndex 2 0 := Sum.inr (Sum.inr 1)

theorem sum_hyp4 {α : Type*} [AddCommMonoid α] (F : HypIndex 2 0 → α) :
    ∑ k, F k = F ue1 + F ue2 + F uf1 + F uf2 := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_two, add_assoc]

theorem hyp4_cases {P : HypIndex 2 0 → Prop} (h1 : P ue1) (h2 : P ue2) (h3 : P uf1)
    (h4 : P uf2) : ∀ i, P i := by
  rintro (i | k | i)
  · fin_cases i
    · exact h1
    · exact h2
  · exact k.elim0
  · fin_cases i
    · exact h3
    · exact h4

theorem entry_comm₁ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (σ : K ≃+* K)
    (a b : ι) (c : K) (h : A * (single a b c).map σ = single a b c * A) (i j : ι) :
    (if j = b then A i a * σ c else 0) = if i = a then c * A b j else 0 := by
  have := congrFun (congrFun h i) j
  rwa [Matrix.map_single, mul_single_apply', single_mul_apply'] at this

theorem entry_comm₂ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (σ : K ≃+* K)
    (a b a' b' : ι) (c c' : K)
    (h : A * (single a b c - single a' b' c').map σ = (single a b c - single a' b' c') * A)
    (i j : ι) :
    (if j = b then A i a * σ c else 0) - (if j = b' then A i a' * σ c' else 0) =
      (if i = a then c * A b j else 0) - (if i = a' then c' * A b' j else 0) := by
  have h1 : (single a b c - single a' b' c').map σ = single a b (σ c) - single a' b' (σ c') := by
    ext x y
    simp only [Matrix.map_apply, Matrix.sub_apply, single_apply, apply_ite σ, map_sub, map_zero]
  have := congrFun (congrFun h i) j
  rwa [h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, Matrix.sub_apply, mul_single_apply',
    mul_single_apply', single_mul_apply', single_mul_apply'] at this

theorem pow_eq_smul_one_of_sq_zero {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {p : ℕ}
    [Fact p.Prime] [CharP K p] (A M : Matrix ι ι K) (a : K) (hA : A = a • 1 + M) (hM : M * M = 0) :
    A ^ p = a ^ p • 1 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hMp : M ^ p = 0 := by
    rw [show p = 2 + (p - 2) by omega, pow_add, pow_two, hM, zero_mul]
  rw [hA, add_pow_char_of_commute p ((Commute.one_left M).smul_left a), hMp, add_zero, smul_pow,
    one_pow]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
