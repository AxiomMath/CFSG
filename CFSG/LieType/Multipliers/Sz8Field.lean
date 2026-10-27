module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.LieType.Multipliers.Sz8

@[ext]
structure F8 where
  c0 : ZMod 2
  c1 : ZMod 2
  c2 : ZMod 2

namespace F8

instance : DecidableEq F8 := fun a b =>
  decidable_of_iff (a.c0 = b.c0 ∧ a.c1 = b.c1 ∧ a.c2 = b.c2) F8.ext_iff.symm

instance : Fintype F8 :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2 × ZMod 2)
    ⟨fun p => ⟨p.1, p.2.1, p.2.2⟩, fun a => (a.c0, a.c1, a.c2), fun _ => rfl, fun _ => rfl⟩

instance : Zero F8 := ⟨⟨0, 0, 0⟩⟩
instance : Inhabited F8 := ⟨0⟩
instance : One F8 := ⟨⟨1, 0, 0⟩⟩
instance : Add F8 := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩⟩
instance : Neg F8 := ⟨fun a => ⟨-a.c0, -a.c1, -a.c2⟩⟩

instance : Mul F8 :=
  ⟨fun a b => ⟨a.c0 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1,
    a.c0 * b.c1 + a.c1 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1 + a.c2 * b.c2,
    a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + a.c2 * b.c2⟩⟩

private theorem zero_def : (0 : F8) = ⟨0, 0, 0⟩ := rfl
private theorem one_def : (1 : F8) = ⟨1, 0, 0⟩ := rfl
private theorem add_def (a b : F8) : a + b = ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩ := rfl
private theorem neg_def (a : F8) : -a = ⟨-a.c0, -a.c1, -a.c2⟩ := rfl
private theorem mul_def (a b : F8) : a * b = ⟨a.c0 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1,
    a.c0 * b.c1 + a.c1 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1 + a.c2 * b.c2,
    a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + a.c2 * b.c2⟩ := rfl

instance : CommRing F8 where
  add_assoc a b c := by ext <;> simp only [add_def] <;> ring
  zero_add a := by ext <;> simp only [add_def, zero_def] <;> ring
  add_zero a := by ext <;> simp only [add_def, zero_def] <;> ring
  add_comm a b := by ext <;> simp only [add_def] <;> ring
  neg_add_cancel a := by ext <;> simp only [add_def, neg_def, zero_def] <;> ring
  mul_assoc a b c := by ext <;> simp only [mul_def] <;> ring
  one_mul a := by ext <;> simp only [mul_def, one_def] <;> ring
  mul_one a := by ext <;> simp only [mul_def, one_def] <;> ring
  zero_mul a := by ext <;> simp only [mul_def, zero_def] <;> ring
  mul_zero a := by ext <;> simp only [mul_def, zero_def] <;> ring
  left_distrib a b c := by ext <;> simp only [mul_def, add_def] <;> ring
  right_distrib a b c := by ext <;> simp only [mul_def, add_def] <;> ring
  mul_comm a b := by ext <;> simp only [mul_def] <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem mul_pow_six {a : F8} (ha : a ≠ 0) : a * a ^ 6 = 1 := by
  revert a
  decide

end F8

local notation "GF" => GaloisField 2 (2 * 1 + 1)

private theorem card_gf : Nat.card GF = 8 := by
  rw [GaloisField.card 2 (2 * 1 + 1) (by norm_num)]
  norm_num

private theorem two_eq_zero : (2 : GF) = 0 := CharTwo.two_eq_zero

theorem exists_cube_eq_add_one : ∃ ω : GF, ω ^ 3 = ω + 1 := by
  classical
  have : Fintype GF := Fintype.ofFinite GF
  obtain ⟨x, hx0, hx1⟩ : ∃ x : GF, x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset GF) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_gf] at hle
    have := Finset.card_le_two (a := (0 : GF)) (b := 1)
    omega
  have h8 : x ^ 8 = x := by
    have h := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, card_gf] at h
  have h7 : x ^ 7 = 1 := by
    rw [show 8 = 7 + 1 from rfl, pow_succ] at h8
    exact (mul_eq_right₀ hx0).mp h8
  have hprod : (x - 1) * ((x ^ 3 + x + 1) * (x ^ 3 + x ^ 2 + 1)) = 0 := by
    linear_combination h7 + (x ^ 4 - x ^ 3) * two_eq_zero
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd (sub_eq_zero.mp h) hx1
  rcases mul_eq_zero.mp h with h | h
  · exact ⟨x, by linear_combination h - (x + 1) * two_eq_zero⟩
  · refine ⟨x⁻¹, ?_⟩
    have hxw : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    linear_combination (-x⁻¹ ^ 3) * h + x⁻¹ ^ 3 * two_eq_zero +
      (x⁻¹ * (x * x⁻¹ + 1) + (x ^ 2 * x⁻¹ ^ 2 + x * x⁻¹ + 1)) * hxw

noncomputable def omega : GF := exists_cube_eq_add_one.choose

theorem omega_cube : omega ^ 3 = omega + 1 := exists_cube_eq_add_one.choose_spec

noncomputable def F8.toGaloisField : F8 →+* GF where
  toFun a := algebraMap (ZMod 2) GF a.c0 + algebraMap (ZMod 2) GF a.c1 * omega +
    algebraMap (ZMod 2) GF a.c2 * omega ^ 2
  map_one' := by simp [F8.one_def]
  map_zero' := by simp [F8.zero_def]
  map_add' a b := by
    simp only [F8.add_def, map_add]
    ring
  map_mul' a b := by
    simp only [F8.mul_def, map_add, map_mul]
    linear_combination (-1 : GF) * (algebraMap (ZMod 2) GF a.c1 * algebraMap (ZMod 2) GF b.c2 +
      algebraMap (ZMod 2) GF a.c2 * algebraMap (ZMod 2) GF b.c1 +
      algebraMap (ZMod 2) GF a.c2 * algebraMap (ZMod 2) GF b.c2 * omega) * omega_cube

theorem F8.toGaloisField_injective : Function.Injective F8.toGaloisField := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have := congrArg F8.toGaloisField (F8.mul_pow_six h)
  rw [map_mul, ha, zero_mul, map_one] at this
  exact zero_ne_one this

theorem F8.toGaloisField_bijective : Function.Bijective F8.toGaloisField :=
  F8.toGaloisField_injective.bijective_of_nat_card_le (by
    rw [card_gf, Nat.card_eq_fintype_card]
    decide)

theorem F8.toGaloisField_surjective : Function.Surjective F8.toGaloisField :=
  F8.toGaloisField_bijective.2

end CFSG.LieType.Multipliers.Sz8
