module

public import CFSG.CharacterTheory.Wreathed.Generators
public import CFSG.CharacterTheory.Wreathed.QuaternionAtQuarterModulus
public import CFSG.CharacterTheory.Wreathed.CentralProduct

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

namespace Original

@[expose] def s (m : ℕ) : Wreath m := element m 1 0 0
@[expose] def t (m : ℕ) : Wreath m := element m 0 1 0
@[expose] def z (m : ℕ) : Wreath m := element m 0 0 1
@[expose] def a (m : ℕ) : Wreath m := s m * t m
@[expose] def x (m : ℕ) : Wreath m := a m ^ (m / 2)
@[expose] def x2 (m : ℕ) : Wreath m := s m ^ (m / 2)
@[expose] def r (m : ℕ) : Wreath m := s m * (t m)⁻¹
@[expose] def d (m : ℕ) : Wreath m := x2 m * z m
@[expose] def U (m : ℕ) : Subgroup (Wreath m) := Subgroup.closure {s m, t m}
@[expose] def Z (m : ℕ) : Subgroup (Wreath m) := Subgroup.zpowers (a m)
@[expose] def Y (m : ℕ) : Subgroup (Wreath m) := Subgroup.closure {r m, d m}
@[expose] def Q (m : ℕ) : Subgroup (Wreath m) :=
  Subgroup.closure {r m ^ (m / 4), d m}
@[expose] def V (m : ℕ) : Subgroup (Wreath m) := Subgroup.closure {a m, x2 m, z m}

@[simp] theorem a_eq (m : ℕ) : a m = element m 1 1 0 := by
  simp [a, s, t, element_base_mul]

@[simp] theorem r_eq (m : ℕ) : r m = element m 1 (-1) 0 := by
  simp [r, s, t, element_base_inv, element_base_mul]

@[simp] theorem x_eq (m : ℕ) : x m = element m (m / 2 : ℕ) (m / 2 : ℕ) 0 := by
  simp [x, element_base_pow, nsmul_eq_mul]

@[simp] theorem x2_eq (m : ℕ) : x2 m = element m (m / 2 : ℕ) 0 0 := by
  simp [x2, s, element_base_pow, nsmul_eq_mul]

@[simp] theorem d_eq (m : ℕ) : d m = element m (m / 2 : ℕ) 0 1 := by
  simp [d, z, element_base_mul]

@[simp] theorem U_eq (m : ℕ) : U m = baseSubgroup m := (base_eq_generated m).symm

theorem Z_eq (m : ℕ) (hm : 1 < m) : Z m = Subgroup.center (Wreath m) := by
  simpa [Z] using (center_eq_zpowers m hm).symm

theorem derived_eq (m : ℕ) : commutator (Wreath m) = Subgroup.zpowers (r m) := by
  simpa using derived_eq_zpowers m

@[expose] def firstHom (m : ℕ) : Multiplicative (ZMod m) →* Wreath m where
  toFun c := element m c.toAdd 0 0
  map_one' := by simp
  map_mul' c e := by
    change element m (c.toAdd + e.toAdd) 0 0 = _
    simp only [element_base_mul, zero_add]

theorem firstHom_injective (m : ℕ) : Function.Injective (firstHom m) := by
  intro c e h
  have hcoord := congrArg (fun g : Wreath m => (coordinateEquiv m g).1) h
  exact Multiplicative.toAdd.injective hcoord

theorem orderOf_s (m : ℕ) : orderOf (s m) = m := by
  change orderOf (firstHom m (Multiplicative.ofAdd (1 : ZMod m))) = m
  rw [orderOf_injective _ (firstHom_injective m)]
  exact ZMod.addOrderOf_one m

theorem orderOf_t (m : ℕ) : orderOf (t m) = m := by
  have hconj : (MulAut.conj (z m)) (s m) = t m := by
    change element m 0 0 1 * element m 1 0 0 * (element m 0 0 1)⁻¹ = _
    exact conjugate_base_by_swap m 1 0 0 0
  rw [← hconj, MulEquiv.orderOf_eq, orderOf_s]

theorem orderOf_a (m : ℕ) : orderOf (a m) = m := by
  rw [a_eq]
  change orderOf (diagonalHom m (Multiplicative.ofAdd (1 : ZMod m))) = m
  rw [orderOf_injective _ (diagonalHom_injective m)]
  exact ZMod.addOrderOf_one m

theorem orderOf_r (m : ℕ) : orderOf (r m) = m := by
  rw [r_eq]
  change orderOf (antiDiagonalHom m (Multiplicative.ofAdd (1 : ZMod m))) = m
  rw [orderOf_injective _ (antiDiagonalHom_injective m)]
  exact ZMod.addOrderOf_one m

theorem orderOf_z (m : ℕ) : orderOf (z m) = 2 :=
  (element_swap_involution_iff m 0 0).mpr (by simp)

theorem z_conjugates_s (m : ℕ) : z m * s m * (z m)⁻¹ = t m :=
  conjugate_base_by_swap m 1 0 0 0

theorem Y_atQuarter (l : ℕ) : Y (4 * l) = quaternionAtQuarterSubgroup l := by
  simp only [Y, r_eq, d_eq, show 4 * l / 2 = 2 * l by omega]
  exact (quaternionAtQuarter_eq_generated l).symm

theorem Q_atQuarter (l : ℕ) : Q (4 * l) = quaternionEightSubgroup l := by
  simp only [Q, r_eq, d_eq, show 4 * l / 4 = l by omega,
    show 4 * l / 2 = 2 * l by omega]
  exact (quaternionEight_range_eq_original_generators l).symm

theorem V_atQuarter (l : ℕ) : V (4 * l) = vSubgroup l := by
  simp only [V, a_eq, x2_eq, z, show 4 * l / 2 = 2 * l by omega]
  exact (v_eq_original_generators l).symm

theorem orderOf_x_atQuarter (l : ℕ) (hl : 0 < l) : orderOf (x (4 * l)) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [orderOf_eq_prime_iff]
  have hcoord : x (4 * l) = element (4 * l) (2 * l : ℕ) (2 * l : ℕ) 0 := by
    simp only [x_eq, show 4 * l / 2 = 2 * l by omega]
  rw [hcoord]
  constructor
  · rw [element_base_pow, two_nsmul, twice_quarter_add_self, element_zero]
  · rw [ne_eq, element_base_eq_one_iff]
    exact fun h => half_quarter_ne_zero l hl h.1

theorem orderOf_x2_atQuarter (l : ℕ) (hl : 0 < l) : orderOf (x2 (4 * l)) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  rw [orderOf_eq_prime_iff]
  have hcoord : x2 (4 * l) = element (4 * l) (2 * l : ℕ) 0 0 := by
    simp only [x2_eq, show 4 * l / 2 = 2 * l by omega]
  rw [hcoord]
  constructor
  · rw [element_base_pow, two_nsmul, twice_quarter_add_self, smul_zero, element_zero]
  · rw [ne_eq, element_base_eq_one_iff]
    exact fun h => half_quarter_ne_zero l hl h.1

theorem orderOf_d_atQuarter (l : ℕ) (hl : 0 < l) : orderOf (d (4 * l)) = 4 := by
  have hcoord : d (4 * l) = element (4 * l) (2 * l : ℕ) 0 1 := by
    simp only [d_eq, show 4 * l / 2 = 2 * l by omega]
  have hsquare : d (4 * l) ^ 2 = x (4 * l) := by
    rw [hcoord, element_swap_sq, x_eq]
    simp only [add_zero, show 4 * l / 2 = 2 * l by omega]
  have hne : d (4 * l) ^ 2 ≠ 1 := by
    rw [hsquare]
    intro h
    have ho := orderOf_x_atQuarter l hl
    rw [h, orderOf_one] at ho
    omega
  have hfour : d (4 * l) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by rfl, pow_mul, hsquare]
    simpa only [orderOf_x_atQuarter l hl] using pow_orderOf_eq_one (x (4 * l))
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hne hfour

end Original

end CFSG.Wreathed
