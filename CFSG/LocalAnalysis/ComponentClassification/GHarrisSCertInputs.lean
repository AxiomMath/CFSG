module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.ComponentClassification.GHarris.SCert

@[expose] def dmul : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5],
    ![3, 2, 1, 0, 7, 6, 5, 4], ![4, 5, 7, 6, 0, 1, 3, 2], ![5, 4, 6, 7, 1, 0, 2, 3],
    ![6, 7, 5, 4, 2, 3, 1, 0], ![7, 6, 4, 5, 3, 2, 0, 1]]

@[expose] def dinv : Fin 8 → Fin 8 := ![0, 1, 2, 3, 4, 5, 7, 6]

@[expose] def me : Fin 8 → Fin 3 → Fin 3 → ZMod 4 :=
  ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![1, 0, 3], ![0, 3, 2], ![0, 0, 3]],
    ![![1, 1, 3], ![0, 1, 2], ![0, 2, 1]], ![![1, 3, 2], ![0, 3, 0], ![0, 2, 3]],
    ![![3, 0, 0], ![0, 1, 1], ![0, 0, 3]], ![![3, 0, 1], ![0, 3, 1], ![0, 0, 1]],
    ![![3, 1, 2], ![0, 1, 3], ![0, 2, 1]], ![![3, 3, 1], ![0, 3, 3], ![0, 2, 3]]]

theorem dmul_assoc : ∀ a b c : Fin 8, dmul (dmul a b) c = dmul a (dmul b c) := by
  decide

theorem dmul_zero_left : ∀ b : Fin 8, dmul 0 b = b := by decide

theorem dmul_dinv : ∀ a : Fin 8, dmul (dinv a) a = 0 := by decide

theorem me_dmul : ∀ (a b : Fin 8) (i k : Fin 3),
    me (dmul a b) i k = me a i 0 * me b 0 k + me a i 1 * me b 1 k + me a i 2 * me b 2 k := by
  decide

theorem me_zero : ∀ i k : Fin 3, me 0 i k = if i = k then 1 else 0 := by decide

@[ext] structure SE where
  d : Fin 8
  v0 : ZMod 4
  v1 : ZMod 4
  v2 : ZMod 4

namespace SE

instance instDecidableEq : DecidableEq SE := fun a b =>
  decidable_of_iff (a.d = b.d ∧ a.v0 = b.v0 ∧ a.v1 = b.v1 ∧ a.v2 = b.v2) (by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact SE.ext h1 h2 h3 h4
    · rintro rfl
      exact ⟨rfl, rfl, rfl, rfl⟩)

@[expose] def act (d : Fin 8) (i : Fin 3) (b : SE) : ZMod 4 :=
  me d i 0 * b.v0 + me d i 1 * b.v1 + me d i 2 * b.v2

@[expose] def mul (a b : SE) : SE :=
  ⟨dmul a.d b.d, a.v0 + act a.d 0 b, a.v1 + act a.d 1 b, a.v2 + act a.d 2 b⟩

@[expose] def inv (a : SE) : SE :=
  ⟨dinv a.d, -act (dinv a.d) 0 a, -act (dinv a.d) 1 a, -act (dinv a.d) 2 a⟩

instance : One SE := ⟨⟨0, 0, 0, 0⟩⟩
instance : Mul SE := ⟨mul⟩
instance : Inv SE := ⟨inv⟩

theorem one_def : (1 : SE) = ⟨0, 0, 0, 0⟩ := rfl
theorem mul_def (a b : SE) : a * b = mul a b := rfl
theorem inv_def (a : SE) : a⁻¹ = inv a := rfl

theorem act_mul (a b c : SE) (i : Fin 3) :
    act (dmul a.d b.d) i c = act a.d i ⟨0, act b.d 0 c, act b.d 1 c, act b.d 2 c⟩ := by
  simp only [act, me_dmul]
  ring

theorem mul_assoc' (a b c : SE) : a * b * c = a * (b * c) := by
  show mul (mul a b) c = mul a (mul b c)
  simp only [mul, act_mul]
  congr 1
  · exact dmul_assoc a.d b.d c.d
  all_goals
    simp only [act]
    ring

theorem one_mul' (a : SE) : 1 * a = a := by
  show mul ⟨0, 0, 0, 0⟩ a = a
  simp only [mul, act, me_zero, dmul_zero_left]
  congr 1 <;> simp

theorem inv_mul_cancel' (a : SE) : a⁻¹ * a = 1 := by
  show mul (inv a) a = ⟨0, 0, 0, 0⟩
  simp only [mul, inv, dmul_dinv]
  congr 1 <;> simp only [act] <;> ring

instance instGroup : Group SE := Group.ofLeftAxioms mul_assoc' one_mul' inv_mul_cancel'

@[expose] def equivProd : SE ≃ Fin 8 × ZMod 4 × ZMod 4 × ZMod 4 where
  toFun s := (s.d, s.v0, s.v1, s.v2)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype SE := Fintype.ofEquiv _ equivProd.symm

@[expose] def gen : Fin 9 → SE :=
  ![SE.mk 0 2 0 0, SE.mk 0 1 0 0, SE.mk 0 3 0 2, SE.mk 0 1 2 2, SE.mk 2 0 2 0, SE.mk 3 2 2 0,
    SE.mk 1 0 1 0, SE.mk 3 0 2 1, SE.mk 4 0 2 0]

@[expose] def invRep : Fin 9 → SE :=
  ![gen 0, gen 2 * gen 3, gen 2 * gen 1, gen 4 * gen 5, gen 2 * gen 5, gen 6, gen 7, gen 8,
    gen 8 * gen 1]

@[expose] def invRepCent : Fin 9 → ℕ := ![512, 256, 128, 64, 32, 64, 32, 32, 32]

end SE

end CFSG.ComponentClassification.GHarris.SCert
