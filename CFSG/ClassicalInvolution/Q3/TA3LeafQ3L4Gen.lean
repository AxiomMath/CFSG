module

public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQ8

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

namespace Q3L4

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem mul_self_eq (M : SL(2, F)) :
    (M : Matrix (Fin 2) (Fin 2) F) * M =
      (M : Matrix (Fin 2) (Fin 2) F).trace • (M : Matrix (Fin 2) (Fin 2) F) - 1 := by
  have hd := M.2
  rw [Matrix.det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | linear_combination -hd | ring

theorem eq_zero_or_eq_one_or_eq_neg_one [Fintype F] (hF : Fintype.card F = 3) (x : F) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have h := FiniteField.pow_card x
  rw [hF] at h
  have h0 : x * (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl (sub_eq_zero.1 h2))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h1))

theorem two_ne_zero' [Fintype F] (hF : Fintype.card F = 3) : (2 : F) ≠ 0 := by
  have hc : ringChar F ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, hF]
    decide
  exact Ring.two_ne_zero hc

theorem neg_one_ne_one [Fintype F] (hF : Fintype.card F = 3) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have e := congrArg (fun M : SL(2, F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at e
  exact two_ne_zero' hF (by linear_combination -e)

theorem pow_three_or_sq [Fintype F] (hF : Fintype.card F = 3) (M : SL(2, F)) :
    M ^ 3 = 1 ∨ M ^ 3 = -1 ∨ M ^ 2 = -1 := by
  set A := (M : Matrix (Fin 2) (Fin 2) F) with hA
  have hc := mul_self_eq M
  rw [← hA] at hc
  have e3 : ((M ^ 3 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = A * A * A := by
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, sq]
  have e2 : ((M ^ 2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = A * A := by
    rw [Matrix.SpecialLinearGroup.coe_pow, sq]
  have hn1 : ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  rcases eq_zero_or_eq_one_or_eq_neg_one hF A.trace with h | h | h
  · refine Or.inr (Or.inr (Subtype.ext ?_))
    change ((M ^ 2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = ((-1 : SL(2, F)) : Matrix _ _ F)
    rw [e2, hn1, hc, h, zero_smul, zero_sub]
  · refine Or.inr (Or.inl (Subtype.ext ?_))
    change ((M ^ 3 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = ((-1 : SL(2, F)) : Matrix _ _ F)
    rw [e3, hn1, hc, h, one_smul, Matrix.sub_mul, hc, h, one_smul, Matrix.one_mul]
    abel
  · refine Or.inl (Subtype.ext ?_)
    change ((M ^ 3 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = ((1 : SL(2, F)) : Matrix _ _ F)
    rw [e3, Matrix.SpecialLinearGroup.coe_one, hc, h, neg_one_smul, Matrix.sub_mul,
      Matrix.neg_mul, hc, h, neg_one_smul, Matrix.one_mul]
    abel

theorem pow_twelve [Fintype F] (hF : Fintype.card F = 3) (M : SL(2, F)) : (M ^ 4) ^ 3 = 1 := by
  rcases pow_three_or_sq hF M with h | h | h
  · rw [← pow_mul, show 4 * 3 = 3 * 4 by norm_num, pow_mul, h, one_pow]
  · rw [← pow_mul, show 4 * 3 = 3 * (2 * 2) by norm_num, pow_mul, h, pow_mul, neg_one_sq,
      one_pow]
  · rw [show M ^ 4 = (M ^ 2) ^ 2 by rw [← pow_mul], h, neg_one_sq, one_pow]

theorem eq_one_or_neg_one_of_sq [Fintype F] (hF : Fintype.card F = 3) {M : SL(2, F)}
    (hM : M ^ 2 = 1) : M = 1 ∨ M = -1 := by
  rcases pow_three_or_sq hF M with h | h | h
  · left
    rw [pow_succ, hM, one_mul] at h
    exact h
  · right
    rw [pow_succ, hM, one_mul] at h
    exact h
  · exact absurd (h.symm.trans hM) (neg_one_ne_one hF)

theorem ne_one_and_ne_neg_one_of_sq [Fintype F] (hF : Fintype.card F = 3) {M : SL(2, F)}
    (hM : M ^ 2 = -1) : M ≠ 1 ∧ M ≠ -1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, one_pow] at hM
    exact neg_one_ne_one hF hM.symm
  · rw [h, neg_one_sq] at hM
    exact neg_one_ne_one hF hM.symm

theorem commute_of_commutator_mem {G : Type*} [Group G] {m : G} {X : Set G} {Z : Subgroup G}
    {n : ℕ} (hX : ∀ x ∈ X, x ^ n = 1) (hZ : ∀ z ∈ Z, z ^ n = 1 → z = 1)
    (hZX : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z) (h : ∀ x ∈ X, m * x * m⁻¹ * x⁻¹ ∈ Z) :
    ∀ g ∈ Subgroup.closure X, m * g = g * m := by
  have key : X ⊆ Subgroup.centralizer ({m} : Set G) := by
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    set z := m * x * m⁻¹ * x⁻¹ with hz
    have hzx : m * x * m⁻¹ = z * x := by rw [hz]; group
    have h1 : (m * x * m⁻¹) ^ n = 1 := by rw [conj_pow, hX x hx, mul_one, mul_inv_cancel]
    rw [hzx, (Commute.mul_pow (hZX z (h x hx) x hx) n), hX x hx, mul_one] at h1
    have h2 : m * x * m⁻¹ * x⁻¹ = 1 := hZ z (h x hx) h1
    calc x * m = (m * x * m⁻¹ * x⁻¹)⁻¹ * (m * x) := by group
      _ = m * x := by rw [h2, inv_one, one_mul]
  intro g hg
  have := (Subgroup.closure_le _).mpr key hg
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

theorem eq_one_or_eq_of_mem_zpowers {M : Type*} [Group M] {u z : M} (hu : u * u = 1)
    (hz : z ∈ Subgroup.zpowers u) : z = 1 ∨ z = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two, hu]
  rw [zpow_eq_zpow_emod k hu2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

end Q3L4

end CFSG.ClassicalInvolution.Q3.TA3
