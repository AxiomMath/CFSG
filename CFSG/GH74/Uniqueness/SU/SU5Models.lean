module

public import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.Uniqueness.SU.SU5F4

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open CFSG.GH74.GLS.Bg.TwoGroups

instance instDecidableEqUT3 {R : Type*} [CommRing R] [DecidableEq R] : DecidableEq (UT3 R) :=
  fun x y => decidable_of_iff (x.a = y.a ∧ x.b = y.b ∧ x.c = y.c) (by
    constructor
    · rintro ⟨h1, h2, h3⟩; exact UT3.ext h1 h2 h3
    · rintro rfl; exact ⟨rfl, rfl, rfl⟩)

@[expose] def ut3EquivProd (R : Type*) [CommRing R] : UT3 R ≃ R × R × R where
  toFun x := (x.a, x.b, x.c)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeUT3 {R : Type*} [CommRing R] [Fintype R] : Fintype (UT3 R) :=
  Fintype.ofEquiv _ (ut3EquivProd R).symm

@[expose] def ut3Congr {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    UT3 R ≃* UT3 R' where
  toFun x := ⟨e x.a, e x.b, e x.c⟩
  invFun x := ⟨e.symm x.a, e.symm x.b, e.symm x.c⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by ext <;> simp [UT3.mul_def]

abbrev L34Syl : Type := UT3 F4c

@[expose] def phiFun (g : L34Syl) : L34Syl :=
  ⟨F4c.sg g.b, F4c.sg g.a, F4c.sg g.a * F4c.sg g.b + F4c.sg g.c⟩

theorem phiFun_mul : ∀ g h : L34Syl, phiFun (g * h) = phiFun g * phiFun h := by decide +kernel

theorem phiFun_phiFun : ∀ g : L34Syl, phiFun (phiFun g) = g := by decide +kernel

@[expose] def phi : MulAut L34Syl where
  toFun := phiFun
  invFun := phiFun
  left_inv := phiFun_phiFun
  right_inv := phiFun_phiFun
  map_mul' := phiFun_mul

theorem phi_mul_phi : phi * phi = 1 := MulEquiv.ext (fun g => phiFun_phiFun g)

@[expose] def psi : Multiplicative (ZMod 2) →* MulAut L34Syl where
  toFun e := if e = 1 then 1 else phi
  map_one' := by simp
  map_mul' := by
    intro a b
    have h : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
    rcases h a with rfl | rfl <;> rcases h b with rfl | rfl
    · simp
    · simp
    · simp
    · have h2 : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
      rw [h2]
      have h1 : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
      simp only [h1, ite_false, ite_true]
      exact phi_mul_phi.symm

abbrev J2Syl : Type := L34Syl ⋊[psi] Multiplicative (ZMod 2)

instance instDecidableEqJ2Syl : DecidableEq J2Syl := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) (by
    constructor
    · rintro ⟨h1, h2⟩; exact SemidirectProduct.ext h1 h2
    · rintro rfl; exact ⟨rfl, rfl⟩)

instance instFintypeJ2Syl : Fintype J2Syl := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

theorem card_L34Syl : Nat.card L34Syl = 64 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem card_J2Syl : Nat.card J2Syl = 128 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

namespace J2Syl

@[expose] def x0 : J2Syl := ⟨1, Multiplicative.ofAdd 1⟩

@[expose] def z0 : J2Syl := ⟨⟨0, 0, 1⟩, 1⟩

end J2Syl

@[expose] def IsL34Type (P : Type*) [Group P] : Prop := Nonempty (P ≃* SylSL3_4)

@[expose] def IsJ2Type (S : Type*) [Group S] : Prop := Nonempty (S ≃* J2Syl)

theorem isL34Type_iff {P : Type*} [Group P] : IsL34Type P ↔ Nonempty (P ≃* L34Syl) :=
  ⟨fun ⟨e⟩ => ⟨e.trans (ut3Congr F4c.equivGF.symm)⟩,
    fun ⟨e⟩ => ⟨e.trans (ut3Congr F4c.equivGF)⟩⟩

end CFSG.GH74.Uniqueness.SU.SU5
