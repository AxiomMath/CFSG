module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace LinearDegree

open Matrix

theorem pow_card_eq_zero_of_isNilpotent {k : Type*} [Field k] {n : Type*} [Fintype n]
    [DecidableEq n] {M : Matrix n n k} (hM : IsNilpotent M) : M ^ Fintype.card n = 0 := by
  have h2 : M.charpoly = Polynomial.X ^ Fintype.card n := by
    rw [← sub_eq_zero]
    exact (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM).eq_zero
  have := Matrix.aeval_self_charpoly M
  rw [h2] at this
  simpa using this

theorem pow_two_pow_eq_one_of_le {k : Type*} [Field k] [CharP k 2] {d : ℕ} (hd : 1 ≤ d)
    {x : GL (Fin d) k} {a : ℕ} (hx : x ^ (2 ^ a) = 1) {j : ℕ} (hj : d ≤ 2 ^ j) :
    x ^ (2 ^ j) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set X : Matrix (Fin d) (Fin d) k := (x : Matrix (Fin d) (Fin d) k)
  have hX : X ^ (2 ^ a) = 1 := by
    have := congrArg (fun g : GL (Fin d) k => (g : Matrix (Fin d) (Fin d) k)) hx
    simpa [X] using this
  have hnil : IsNilpotent (X - 1) := by
    refine ⟨2 ^ a, ?_⟩
    rw [sub_pow_char_pow_of_commute 2 a (Commute.one_right X), hX, one_pow, sub_self]
  have hd' := pow_card_eq_zero_of_isNilpotent hnil
  rw [Fintype.card_fin] at hd'
  have h0 : (X - 1) ^ (2 ^ j) = 0 := by
    rw [← Nat.sub_add_cancel hj, pow_add, hd', mul_zero]
  rw [sub_pow_char_pow_of_commute 2 j (Commute.one_right X), one_pow, sub_eq_zero] at h0
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  exact h0

end LinearDegree

open LinearDegree

theorem characteristic_two_linear_quotient_two_element_degree_bound
    {k : Type*} [Field k] [CharP k 2] {d r : ℕ} (hd : 1 ≤ d) (hr : 1 ≤ r)
    (H : Subgroup (GL (Fin d) k)) [Finite H] (N : Subgroup H) [N.Normal] (c : H ⧸ N)
    (hc : orderOf c = 2 ^ r) : 2 ^ (r - 1) < d := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  have hx : (h ^ m) ^ (2 ^ a) = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hcx : orderOf ((h ^ m : H) : H ⧸ N) = 2 ^ r := by
    rw [QuotientGroup.mk_pow, Nat.Coprime.orderOf_pow, hc]
    rw [hc]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  by_contra hlt
  push Not at hlt
  have h1 : ((h ^ m : H) : GL (Fin d) k) ^ (2 ^ (r - 1)) = 1 :=
    pow_two_pow_eq_one_of_le hd (a := a) (by rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]) hlt
  have h2 : ((h ^ m : H) : H ⧸ N) ^ (2 ^ (r - 1)) = 1 := by
    have : (h ^ m) ^ (2 ^ (r - 1)) = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h1]; rfl)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rw [hcx] at hdvd
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have : 2 ^ (r - 1) < 2 ^ r := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem characteristic_two_linear_odd_quotient_dihedral_degree_bound
    {k : Type*} [Field k] [CharP k 2] {d s : ℕ} (hd : 1 ≤ d) (hs : 2 ≤ s)
    (H : Subgroup (GL (Fin d) k)) [Finite H] (N : Subgroup H) [N.Normal]
    (hP : ∃ P : Sylow 2 (H ⧸ N),
      Nonempty ((P : Subgroup (H ⧸ N)) ≃* DihedralGroup (2 ^ (s - 1)))) :
    2 ^ (s - 2) < d ∧ s ≤ d := by
  obtain ⟨P, ⟨e⟩⟩ := hP
  have hne : NeZero (2 ^ (s - 1)) := ⟨by positivity⟩
  have hord : orderOf ((e.symm (DihedralGroup.r 1) : P) : H ⧸ N) = 2 ^ (s - 1) := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have h := characteristic_two_linear_quotient_two_element_degree_bound hd (by omega) H N _ hord
  have hs2 : s - 1 - 1 = s - 2 := by omega
  rw [hs2] at h
  refine ⟨h, ?_⟩
  have := Nat.lt_two_pow_self (n := s - 2)
  omega

end CFSG.ComponentClassification.UnbalancedGS
