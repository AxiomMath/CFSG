module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.CharacterTheory.SteinbergBY

@[ext] structure FieldFour where
  re : Bool
  im : Bool

namespace FieldFour

instance : DecidableEq FieldFour := fun x y =>
  decidable_of_iff (x.re = y.re ∧ x.im = y.im)
    ⟨fun h => FieldFour.ext h.1 h.2, fun h => ⟨congrArg re h, congrArg im h⟩⟩

@[expose] def equivProd : FieldFour ≃ Bool × Bool where
  toFun x := (x.re, x.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype FieldFour := Fintype.ofEquiv _ equivProd.symm

instance : Zero FieldFour := ⟨⟨false, false⟩⟩
instance : One FieldFour := ⟨⟨true, false⟩⟩
instance : Add FieldFour := ⟨fun x y => ⟨xor x.re y.re, xor x.im y.im⟩⟩
instance : Neg FieldFour := ⟨fun x => x⟩
instance : Sub FieldFour := ⟨fun x y => ⟨xor x.re y.re, xor x.im y.im⟩⟩
instance : Mul FieldFour :=
  ⟨fun x y => ⟨xor (x.re && y.re) (x.im && y.im),
    xor (xor (x.re && y.im) (x.im && y.re)) (x.im && y.im)⟩⟩
instance : Inv FieldFour := ⟨fun x => ⟨xor x.re x.im, x.im⟩⟩

instance : Field FieldFour where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  neg_add_cancel := by decide
  sub_eq_add_neg := by decide
  mul_comm := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := by decide
  inv_zero := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

theorem card_eq : Fintype.card FieldFour = 4 := by decide

theorem natCard_eq : Nat.card FieldFour = 4 := by
  rw [Nat.card_eq_fintype_card, card_eq]

instance : CharP FieldFour 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by decide)

@[expose] def ω : FieldFour := ⟨false, true⟩

@[expose] def ω₂ : FieldFour := ⟨true, true⟩

theorem ω_sq : ω ^ 2 = ω₂ := by decide

theorem ω₂_ne_zero : ω₂ ≠ 0 := by decide

theorem ω₂_ne_one : ω₂ ≠ 1 := by decide

theorem ω_ne_zero : ω ≠ 0 := by decide

theorem ω_ne_one : ω ≠ 1 := by decide

theorem ω_ne_ω₂ : ω ≠ ω₂ := by decide

@[expose] def frob : FieldFour →+* FieldFour where
  toFun x := ⟨xor x.re x.im, x.im⟩
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

theorem frob_apply (x : FieldFour) : frob x = x ^ 2 := by
  revert x
  decide

theorem frob_frob (x : FieldFour) : frob (frob x) = x := by
  revert x
  decide

theorem frob_ω : frob ω = ω₂ := by decide

theorem frob_ω₂ : frob ω₂ = ω := by decide

@[expose] def reZ (x : FieldFour) : ZMod 2 := if x.re then 1 else 0

@[expose] def imZ (x : FieldFour) : ZMod 2 := if x.im then 1 else 0

@[expose] def ofPrime : ZMod 2 →+* FieldFour where
  toFun a := ⟨decide (a = 1), false⟩
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

instance : Algebra (ZMod 2) FieldFour := ofPrime.toAlgebra

theorem algebraMap_eq : algebraMap (ZMod 2) FieldFour = ofPrime := rfl

theorem smul_eq_ofPrime_mul (a : ZMod 2) (x : FieldFour) : a • x = ofPrime a * x := rfl

theorem reZ_smul (a : ZMod 2) (x : FieldFour) : reZ (a • x) = a * reZ x := by
  rw [smul_eq_ofPrime_mul]
  revert a x
  decide

theorem imZ_smul (a : ZMod 2) (x : FieldFour) : imZ (a • x) = a * imZ x := by
  rw [smul_eq_ofPrime_mul]
  revert a x
  decide

@[expose] def reHom : FieldFour →ₗ[ZMod 2] ZMod 2 where
  toFun := reZ
  map_add' := by decide
  map_smul' := reZ_smul

theorem reHom_apply (x : FieldFour) : reHom x = reZ x := rfl

theorem reZ_ofPrime_mul (a : ZMod 2) (x : FieldFour) : reZ (ofPrime a * x) = a * reZ x := by
  revert a x
  decide

theorem reZ_ω_mul (x : FieldFour) : reZ (ω * x) = imZ x := by
  revert x
  decide

theorem eq_zero_of_reZ_imZ (x : FieldFour) (h₁ : reZ x = 0) (h₂ : imZ x = 0) : x = 0 := by
  revert x
  decide

theorem eq_ofPrime_add_ofPrime_mul (c : FieldFour) :
    c = ofPrime (reZ c + imZ c) + ofPrime (imZ c) * ω₂ := by
  revert c
  decide

theorem reZ_add (x y : FieldFour) : reZ (x + y) = reZ x + reZ y := by
  revert x y
  decide

theorem imZ_add (x y : FieldFour) : imZ (x + y) = imZ x + imZ y := by
  revert x y
  decide

theorem reZ_mul (x y : FieldFour) : reZ (x * y) = reZ x * reZ y + imZ x * imZ y := by
  revert x y
  decide

theorem imZ_mul (x y : FieldFour) :
    imZ (x * y) = reZ x * imZ y + imZ x * reZ y + imZ x * imZ y := by
  revert x y
  decide

section Embedding

variable {k : Type*} [Field k] [CharP k 2]

@[expose] noncomputable def toFieldOfRoot (ζ : k) (hζ : ζ ^ 2 + ζ + 1 = 0) : FieldFour →+* k where
  toFun x := ZMod.castHom (dvd_refl 2) k (reZ x) + ZMod.castHom (dvd_refl 2) k (imZ x) * ζ
  map_one' := by
    have h1 : reZ 1 = 1 := by decide
    have h0 : imZ 1 = 0 := by decide
    rw [h1, h0]
    simp
  map_zero' := by
    have h0 : reZ 0 = 0 := by decide
    have h0' : imZ 0 = 0 := by decide
    rw [h0, h0']
    simp
  map_add' x y := by
    rw [reZ_add, imZ_add, map_add, map_add]
    ring
  map_mul' x y := by
    rw [reZ_mul, imZ_mul]
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    simp only [map_add, map_mul]
    linear_combination (-(ZMod.castHom (dvd_refl 2) k (imZ x) *
      ZMod.castHom (dvd_refl 2) k (imZ y))) * hζ + (ZMod.castHom (dvd_refl 2) k (imZ x) *
        ZMod.castHom (dvd_refl 2) k (imZ y) * (1 + ζ)) * h2

variable (k) [IsAlgClosed k]

omit [CharP k 2] in
theorem exists_root_sq_add_self_add_one : ∃ ζ : k, ζ ^ 2 + ζ + 1 = 0 := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k)
    (by
      have h : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k).natDegree = 2 := by
        compute_degree!
      intro h0
      rw [Polynomial.degree_eq_natDegree (fun h1 => by simp [h1] at h), h] at h0
      exact absurd h0 (by decide))
  refine ⟨ζ, ?_⟩
  simpa [Polynomial.IsRoot] using hζ

@[expose] noncomputable def toField : FieldFour →+* k :=
  toFieldOfRoot (exists_root_sq_add_self_add_one k).choose
    (exists_root_sq_add_self_add_one k).choose_spec

end Embedding

end FieldFour

end CFSG.CharacterTheory.SteinbergBY
