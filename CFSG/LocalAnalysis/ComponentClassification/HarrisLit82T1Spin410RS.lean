module

public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Matrix
open scoped MatrixGroups

section Quaternion

variable {N : ℕ}

theorem quaternion_exists_mul_eq (hN : Even N) (g : QuaternionGroup N) :
    ∃ x y : QuaternionGroup N, x * x = QuaternionGroup.a N ∧ y * y = QuaternionGroup.a N ∧
      g = x * y := by
  obtain ⟨k, hk⟩ := hN
  rcases g with i | i
  · refine ⟨QuaternionGroup.xa 0, QuaternionGroup.xa (i - N), ?_, ?_, ?_⟩
    · rw [QuaternionGroup.xa_mul_xa]
      congr 1
      ring
    · rw [QuaternionGroup.xa_mul_xa]
      congr 1
      ring
    · rw [QuaternionGroup.xa_mul_xa]
      congr 1
      ring
  · refine ⟨QuaternionGroup.a (k : ZMod (2 * N)), QuaternionGroup.xa (i + k), ?_, ?_, ?_⟩
    · rw [QuaternionGroup.a_mul_a]
      congr 1
      rw [show ((N : ℕ) : ZMod (2 * N)) = ((k + k : ℕ) : ZMod (2 * N)) by rw [← hk]]
      push_cast
      ring
    · rw [QuaternionGroup.xa_mul_xa]
      congr 1
      ring
    · rw [QuaternionGroup.a_mul_xa]
      congr 1
      ring

theorem quaternion_xa_zero_mul_xa_one_ne (hN : 2 ≤ N) :
    QuaternionGroup.xa (0 : ZMod (2 * N)) * QuaternionGroup.xa 1 ≠
      QuaternionGroup.xa 1 * QuaternionGroup.xa 0 := by
  rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.xa_mul_xa]
  intro h
  have h' : ((N : ZMod (2 * N)) + 1 - 0) = (N : ZMod (2 * N)) + 0 - 1 :=
    QuaternionGroup.a.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * N)) = 0 := by
    push_cast
    linear_combination h'
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem quaternion_xa_mul_self (i : ZMod (2 * N)) :
    QuaternionGroup.xa i * QuaternionGroup.xa i = QuaternionGroup.a N := by
  rw [← pow_two, QuaternionGroup.xa_sq]

end Quaternion

section Sylow

variable {K : Type} [Field K] [Finite K]

theorem sylow_sl2_facts (hodd : Odd (Nat.card K)) (P : Sylow 2 SL(2, K)) :
    (∀ g ∈ (P : Subgroup SL(2, K)), ∃ x ∈ (P : Subgroup SL(2, K)), ∃ y ∈ (P : Subgroup SL(2, K)),
      x * x = -1 ∧ y * y = -1 ∧ g = x * y) ∧
    ∃ x ∈ (P : Subgroup SL(2, K)), ∃ y ∈ (P : Subgroup SL(2, K)),
      x * x = -1 ∧ y * y = -1 ∧ x * y ≠ y * x := by
  have h2 : (2 : K) ≠ 0 := Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  obtain ⟨n, hn3, ⟨e⟩⟩ := Semidihedral.OddFieldSL2.sylow_two_quaternion K hodd P
  set N := 2 ^ (n - 2) with hNdef
  have hNeven : Even N := by
    rw [hNdef]
    exact (Nat.even_pow' (by omega)).mpr even_two
  have hN2 : 2 ≤ N := by
    rw [hNdef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero N := ⟨by omega⟩
  have hw : (e.symm (QuaternionGroup.a N) : SL(2, K)) = -1 := by
    set w := e.symm (QuaternionGroup.xa 0) with hwdef
    have hww : e.symm (QuaternionGroup.a N) = w * w := by
      rw [hwdef, ← map_mul, quaternion_xa_mul_self]
    rw [hww]
    have hne : (w * w : (P : Subgroup SL(2, K))) ≠ 1 := by
      intro h
      have := congrArg e h
      rw [map_mul, hwdef, MulEquiv.apply_symm_apply, quaternion_xa_mul_self, map_one] at this
      have hN' : (N : ZMod (2 * N)) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      exact hN' (QuaternionGroup.a.inj (this.trans QuaternionGroup.one_def))
    have hsq : (w * w : (P : Subgroup SL(2, K))) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_mul, hwdef, MulEquiv.apply_symm_apply, quaternion_xa_mul_self, map_one,
        pow_two, QuaternionGroup.a_mul_a, ← QuaternionGroup.a_zero]
      congr 1
      rw [← two_mul]
      exact_mod_cast ZMod.natCast_self (2 * N)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf ((w * w : (P : Subgroup SL(2, K))) : SL(2, K)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime hsq hne
    exact (Semidihedral.OddFieldSL2.orderOf_eq_two_iff K h2 _).mp hord
  have hsq : ∀ u : QuaternionGroup N, u * u = QuaternionGroup.a N →
      (e.symm u : SL(2, K)) * (e.symm u : SL(2, K)) = -1 := by
    intro u hu
    rw [← Subgroup.coe_mul, ← map_mul, hu, hw]
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨u, v, hu, hv, huv⟩ := quaternion_exists_mul_eq hNeven (e ⟨g, hg⟩)
    refine ⟨e.symm u, (e.symm u).2, e.symm v, (e.symm v).2, hsq u hu, hsq v hv, ?_⟩
    rw [← Subgroup.coe_mul, ← map_mul, ← huv, MulEquiv.symm_apply_apply]
  · refine ⟨e.symm (QuaternionGroup.xa 0), (e.symm _).2, e.symm (QuaternionGroup.xa 1),
      (e.symm _).2, hsq _ (quaternion_xa_mul_self 0), hsq _ (quaternion_xa_mul_self 1),
      fun h => quaternion_xa_zero_mul_xa_one_ne hN2 ?_⟩
    have h' : e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.xa (1 : ZMod (2 * N))) =
        e.symm (QuaternionGroup.xa 1) * e.symm (QuaternionGroup.xa 0) := Subtype.ext h
    rw [← map_mul, ← map_mul] at h'
    exact e.symm.injective h'

end Sylow

section Matrices

variable {K : Type} [Field K]

theorem exists_eq_smul_one_add_smul_of_commute {a M : Matrix (Fin 2) (Fin 2) K}
    (ha : ∀ c : K, a ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) (h : M * a = a * M) :
    ∃ α β : K, M = α • (1 : Matrix (Fin 2) (Fin 2) K) + β • a := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : K, a = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two a⟩
  obtain ⟨x, y, z, w, rfl⟩ : ∃ x y z w : K, M = !![x, y; z, w] :=
    ⟨_, _, _, _, Matrix.eta_fin_two M⟩
  have h11 := congrFun (congrFun h 0) 0
  have h12 := congrFun (congrFun h 0) 1
  have h21 := congrFun (congrFun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h11 h12 h21
  by_cases hq : q = 0
  · by_cases hr : r = 0
    · have hps : p - s ≠ 0 := by
        intro hps
        apply ha p
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hq, hr, sub_eq_zero.mp hps]
      have hy : y = 0 := by
        have : y * (s - p) = 0 := by rw [hq] at h12; linear_combination h12
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (by linear_combination -h) hps
      have hz : z = 0 := by
        have : z * (p - s) = 0 := by rw [hr] at h21; linear_combination h21
        exact (mul_eq_zero.mp this).resolve_right hps
      refine ⟨x - (x - w) / (p - s) * p, (x - w) / (p - s), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq, hr, hy, hz]
      · field_simp
        ring
    · have hy : y = 0 := by
        have : y * r = 0 := by rw [hq] at h11; linear_combination h11
        exact (mul_eq_zero.mp this).resolve_right hr
      refine ⟨x - z / r * p, z / r, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq, hy]
      · field_simp
      · field_simp
        linear_combination h21
  · refine ⟨x - y / q * p, y / q, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · field_simp
    · field_simp
      linear_combination -h11
    · field_simp
      linear_combination -h12

variable [Finite K]

theorem eq_smul_one_of_commute_sylow_sl2 (hodd : Odd (Nat.card K)) (P : Sylow 2 SL(2, K))
    {M : Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ g ∈ (P : Subgroup SL(2, K)), M * (g : Matrix (Fin 2) (Fin 2) K) = g * M) :
    ∃ c : K, M = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h2 : (2 : K) ≠ 0 := Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  obtain ⟨-, x, hx, y, hy, hxx, -, hxy⟩ := sylow_sl2_facts hodd P
  have hxs : ∀ c : K, (x : Matrix (Fin 2) (Fin 2) K) ≠ c • 1 := by
    intro c hc
    have hdet : c ^ 2 = 1 := by
      have := x.2
      rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at this
      exact this
    have hsq : (x : Matrix (Fin 2) (Fin 2) K) * x = 1 := by
      rw [hc, smul_mul_smul_comm, Matrix.one_mul, ← pow_two, hdet, one_smul]
    have h1 : ((x * x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := hsq
    rw [hxx, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at h1
    apply h2
    have := congrFun (congrFun h1 0) 0
    simp at this
    linear_combination -this
  obtain ⟨α, β, hαβ⟩ := exists_eq_smul_one_add_smul_of_commute hxs (hM x hx)
  have hβ : β = 0 := by
    by_contra hβ
    apply hxy
    apply Subtype.ext
    have h := hM y hy
    rw [hαβ, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
      Matrix.one_mul, Matrix.mul_one] at h
    have h' : β • ((x : Matrix (Fin 2) (Fin 2) K) * y) = β • ((y : Matrix (Fin 2) (Fin 2) K) * x) :=
      add_left_cancel h
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact smul_right_injective _ hβ h'
  exact ⟨α, by rw [hαβ, hβ, zero_smul, add_zero]⟩

end Matrices

end CFSG.ComponentClassification.HarrisLit.T1
