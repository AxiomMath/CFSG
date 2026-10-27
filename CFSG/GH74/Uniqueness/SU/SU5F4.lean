module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

inductive F4c : Type
  | z0 : F4c
  | z1 : F4c
  | w : F4c
  | w2 : F4c
  deriving DecidableEq

namespace F4c

instance : Fintype F4c := ⟨{z0, z1, w, w2}, by intro x; cases x <;> decide⟩

instance : Zero F4c := ⟨z0⟩

instance : One F4c := ⟨z1⟩

@[expose] def add : F4c → F4c → F4c
  | z0, y => y
  | z1, z0 => z1
  | z1, z1 => z0
  | z1, w => w2
  | z1, w2 => w
  | w, z0 => w
  | w, z1 => w2
  | w, w => z0
  | w, w2 => z1
  | w2, z0 => w2
  | w2, z1 => w
  | w2, w => z1
  | w2, w2 => z0

@[expose] def mul : F4c → F4c → F4c
  | z0, _ => z0
  | _, z0 => z0
  | z1, y => y
  | y, z1 => y
  | w, w => w2
  | w, w2 => z1
  | w2, w => z1
  | w2, w2 => w

@[expose] def inv : F4c → F4c
  | z0 => z0
  | z1 => z1
  | w => w2
  | w2 => w

instance : Add F4c := ⟨add⟩

instance : Mul F4c := ⟨mul⟩

instance : Neg F4c := ⟨fun a => a⟩

instance : Inv F4c := ⟨inv⟩

instance : CommRing F4c where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := by decide
  add_comm := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide

instance : Field F4c where
  exists_pair_ne := ⟨z0, z1, by decide⟩
  mul_inv_cancel := by decide
  inv_zero := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

theorem card_eq : Fintype.card F4c = 4 := by decide

@[expose] def sg (a : F4c) : F4c := a * a

theorem sg_add : ∀ a b : F4c, sg (a + b) = sg a + sg b := by decide

theorem sg_mul : ∀ a b : F4c, sg (a * b) = sg a * sg b := by decide

theorem sg_sg : ∀ a : F4c, sg (sg a) = a := by decide

noncomputable def equivGF : F4c ≃+* GaloisField 2 2 :=
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  FiniteField.ringEquivOfCardEq (by
    rw [card_eq, Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
    norm_num)

end F4c

end CFSG.GH74.Uniqueness.SU.SU5
