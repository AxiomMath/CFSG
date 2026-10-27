module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sz32

@[ext]
structure F32 where
  c0 : ZMod 2
  c1 : ZMod 2
  c2 : ZMod 2
  c3 : ZMod 2
  c4 : ZMod 2

namespace F32

instance instDecidableEq : DecidableEq F32 := fun a b =>
  decidable_of_iff (a.c0 = b.c0 ∧ a.c1 = b.c1 ∧ a.c2 = b.c2 ∧ a.c3 = b.c3 ∧ a.c4 = b.c4)
    F32.ext_iff.symm

@[expose] def toProd (a : F32) : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 :=
  (a.c0, a.c1, a.c2, a.c3, a.c4)

instance instFintype : Fintype F32 :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)
    ⟨fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩, toProd, fun _ => rfl, fun _ => rfl⟩

instance instZero : Zero F32 := ⟨⟨0, 0, 0, 0, 0⟩⟩
instance instInhabited : Inhabited F32 := ⟨0⟩
instance instOne : One F32 := ⟨⟨1, 0, 0, 0, 0⟩⟩
@[expose] def add (a b : F32) : F32 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4⟩

instance instNeg : Neg F32 := ⟨fun a => ⟨-a.c0, -a.c1, -a.c2, -a.c3, -a.c4⟩⟩

@[expose] def mul (a b : F32) : F32 :=
  ⟨a.c0 * b.c0 + (a.c1 * b.c4 + a.c2 * b.c3 + a.c3 * b.c2 + a.c4 * b.c1) + a.c4 * b.c4,
   (a.c0 * b.c1 + a.c1 * b.c0) + (a.c2 * b.c4 + a.c3 * b.c3 + a.c4 * b.c2),
   (a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0) +
     (a.c1 * b.c4 + a.c2 * b.c3 + a.c3 * b.c2 + a.c4 * b.c1) +
     (a.c3 * b.c4 + a.c4 * b.c3) + a.c4 * b.c4,
   (a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0) +
     (a.c2 * b.c4 + a.c3 * b.c3 + a.c4 * b.c2) + a.c4 * b.c4,
   (a.c0 * b.c4 + a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1 + a.c4 * b.c0) +
     (a.c3 * b.c4 + a.c4 * b.c3)⟩

instance instAdd : Add F32 := ⟨add⟩
instance instMul : Mul F32 := ⟨mul⟩

private theorem zero_def : (0 : F32) = ⟨0, 0, 0, 0, 0⟩ := rfl
private theorem one_def : (1 : F32) = ⟨1, 0, 0, 0, 0⟩ := rfl
private theorem add_def (a b : F32) :
    a + b = ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4⟩ := rfl
private theorem neg_def (a : F32) : -a = ⟨-a.c0, -a.c1, -a.c2, -a.c3, -a.c4⟩ := rfl
private theorem mul_def (a b : F32) :
    a * b = ⟨a.c0 * b.c0 + (a.c1 * b.c4 + a.c2 * b.c3 + a.c3 * b.c2 + a.c4 * b.c1) +
        a.c4 * b.c4,
     (a.c0 * b.c1 + a.c1 * b.c0) + (a.c2 * b.c4 + a.c3 * b.c3 + a.c4 * b.c2),
     (a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0) +
       (a.c1 * b.c4 + a.c2 * b.c3 + a.c3 * b.c2 + a.c4 * b.c1) +
       (a.c3 * b.c4 + a.c4 * b.c3) + a.c4 * b.c4,
     (a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0) +
       (a.c2 * b.c4 + a.c3 * b.c3 + a.c4 * b.c2) + a.c4 * b.c4,
     (a.c0 * b.c4 + a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1 + a.c4 * b.c0) +
       (a.c3 * b.c4 + a.c4 * b.c3)⟩ := rfl

instance instCommRing : CommRing F32 where
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

theorem mul_pow_thirty {a : F32} (ha : a ≠ 0) : a * a ^ 30 = 1 := by
  revert a
  decide +kernel

instance instInv : Inv F32 := ⟨fun a => a ^ 30⟩

instance instField : Field F32 where
  mul_inv_cancel _ ha := mul_pow_thirty ha
  inv_zero := by decide +kernel
  exists_pair_ne := ⟨0, 1, by decide⟩
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

theorem card_eq : Fintype.card F32 = 32 := by
  rw [Fintype.card_congr (Equiv.symm ⟨fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩,
    toProd, fun _ => rfl, fun _ => rfl⟩)]
  simp

instance instFinite : Finite F32 := Finite.of_fintype F32

theorem natCard_eq : Nat.card F32 = 2 ^ (2 * 2 + 1) := by
  rw [Nat.card_eq_fintype_card, card_eq]
  norm_num

theorem two_eq_zero : (2 : F32) = 0 := by decide +kernel

noncomputable def ringEquiv (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ (2 * 2 + 1)) :
    F ≃+* F32 :=
  haveI : Fintype F := Fintype.ofFinite F
  FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hF, card_eq]
    norm_num)

end F32

end CFSG.AGLEmbedding.KFactProofs.Sz32
