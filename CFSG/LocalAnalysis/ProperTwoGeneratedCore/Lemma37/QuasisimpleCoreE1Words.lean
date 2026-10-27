module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Count
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

@[expose] def c3Inv (v : Fin 64) : Fin 64 := c3Mul (c3Mul v v) v

@[expose] def c3Conj (v w : Fin 64) : Fin 64 := c3Mul (c3Mul v w) (c3Inv v)

theorem c3Mul_zero_right : ∀ v : Fin 64, c3Mul v 0 = v := by decide

theorem c3Mul_c3Inv : ∀ v : Fin 64, c3Mul v (c3Inv v) = 0 := by decide

theorem c3Mul_c3Inv_mul : ∀ v w : Fin 64, c3Mul v (c3Mul (c3Inv v) w) = w := by decide +kernel

theorem c3Inv_mul_mul : ∀ v w : Fin 64, c3Mul (c3Inv v) (c3Mul v w) = w := by decide +kernel

theorem c3_exponent_four : ∀ v : Fin 64, c3Mul (c3Mul v v) (c3Mul v v) = 0 := by decide

@[expose] def e1OuterRep (v : Fin 64) : Fin 64 := if v.val / 2 % 2 = 0 then 1 else 3

theorem c3_outer_conj : ∀ v : Fin 64, v.val % 2 = 1 → c3Mul v v = 0 →
    ∃ w : Fin 64, w.val % 4 = 0 ∧ c3Conj w (e1OuterRep v) = v := by decide +kernel

@[expose] def e1Gen (gf gef : Bool) (v : Fin 64) : Bool :=
  decide (v = 0) || (decide (c3Mul v v = 0) &&
    if v.val % 2 = 0 then decide (c3GenW v) else if v.val / 2 % 2 = 0 then gf else gef)

theorem e1Gen_one : ∀ gf gef : Bool, e1Gen gf gef 1 = gf := by decide

theorem e1Gen_three : ∀ gf gef : Bool, e1Gen gf gef 3 = gef := by decide

theorem mul_self_of_e1Gen : ∀ (gf gef : Bool) (v : Fin 64), e1Gen gf gef v = true →
    c3Mul v v = 0 := by decide +kernel

theorem e1Gen_even_iff : ∀ (gf gef : Bool) (v : Fin 64), v.val % 2 = 0 →
    (e1Gen gf gef v = true ↔ v = 0 ∨ c3GenW v) := by decide +kernel

theorem e1Gen_outer : ∀ (gf gef : Bool) (v : Fin 64), v.val % 2 = 1 → c3Mul v v = 0 →
    e1Gen gf gef v = e1Gen gf gef (e1OuterRep v) := by decide +kernel

@[expose] def e1R (v : Fin 64) : Prop := v.val / 16 % 2 = v.val / 4 % 2

instance : DecidablePred e1R := fun v => by unfold e1R; infer_instance

theorem e1R_zero : e1R 0 := by decide

theorem e1R_forty : e1R 40 := by decide

theorem e1R_mul : ∀ v w : Fin 64, e1R v → e1R w → e1R (c3Mul v w) := by decide +kernel

theorem card_e1R : (Finset.univ.filter e1R).card = 32 := by decide

theorem e1R_center_iff : ∀ v : Fin 64, e1R v →
    ((∀ w : Fin 64, e1R w → c3Mul v w = c3Mul w v) ↔ v = 0 ∨ v = 40) := by decide +kernel

theorem e1R_mul_self : ∀ v : Fin 64, e1R v → c3Mul v v = 0 ∨ c3Mul v v = 40 := by decide

theorem e1R_comm : ∀ v w : Fin 64, e1R v → e1R w →
    c3Mul v w = c3Mul w v ∨ c3Mul v w = c3Mul (c3Mul w v) 40 := by decide +kernel

theorem e1R_nine : e1R 9 ∧ c3Mul 9 9 = 40 := by decide

@[expose] def e1Sing (v : Fin 64) : Prop := e1R v ∧ c3Mul v v = 0 ∧ v ≠ 0 ∧ v ≠ 40

instance : DecidablePred e1Sing := fun v => by unfold e1Sing; infer_instance

theorem card_e1R_involution :
    (Finset.univ.filter fun v : Fin 64 => e1R v ∧ c3Mul v v = 0 ∧ v ≠ 0).card = 19 := by decide

theorem card_e1Sing : (Finset.univ.filter e1Sing).card = 18 := by decide

theorem e1Sing_mul_forty : ∀ v : Fin 64, e1Sing v → e1Sing (c3Mul v 40) ∧ c3Mul v 40 ≠ v := by
  decide

theorem e1Gen_mul_forty : ∀ (gf gef : Bool) (v : Fin 64), e1Sing v →
    e1Gen gf gef (c3Mul v 40) = e1Gen gf gef v := by decide +kernel

@[expose] def e1Pt (v : Fin 64) : Prop := e1Sing v ∧ v.val / 32 % 2 = 0

instance : DecidablePred e1Pt := fun v => by unfold e1Pt; infer_instance

theorem card_e1Sing_e1Gen : ∀ gf gef : Bool,
    (Finset.univ.filter fun v : Fin 64 => e1Sing v ∧ e1Gen gf gef v = true).card =
      4 + 4 * (gf.toNat + gef.toNat) := by decide +kernel

@[expose] def e1E (v : Fin 64) : Prop :=
  v.val / 16 % 2 = 0 ∧ v.val / 4 % 2 = 0 ∧ v.val % 2 = 0

instance : DecidablePred e1E := fun v => by unfold e1E; infer_instance

theorem e1E_eq_mul : ∀ v : Fin 64, e1E v → v = c3Mul (c3Mul (if v.val / 32 % 2 = 0 then 0 else 32)
    (if v.val / 8 % 2 = 0 then 0 else 8)) (if v.val / 2 % 2 = 0 then 0 else 2) := by decide

theorem e1E_gens : e1E 32 ∧ e1E 8 ∧ e1E 2 ∧ e1E 40 := by decide

theorem e1E_zero : e1E 0 := by decide

theorem e1E_mul : ∀ v w : Fin 64, e1E v → e1E w → e1E (c3Mul v w) := by decide +kernel

theorem card_e1E : (Finset.univ.filter e1E).card = 8 := by decide

theorem e1R_of_e1E : ∀ v : Fin 64, e1E v → e1R v := by decide

theorem e1E_mul_self : ∀ v : Fin 64, e1E v → c3Mul v v = 0 := by decide

theorem e1E_comm : ∀ v w : Fin 64, e1E v → e1E w → c3Mul v w = c3Mul w v := by decide +kernel

theorem e1E_conj : ∀ s t : Fin 64, e1E t → e1E (c3Conj s t) := by decide +kernel

theorem e1E_of_comm : ∀ s : Fin 64, (∀ t : Fin 64, e1E t → c3Mul s t = c3Mul t s) → e1E s := by
  decide +kernel

theorem e1Gen_e1E : ∀ (gf gef : Bool) (v : Fin 64), e1E v → v ≠ 0 → v ≠ 40 →
    e1Gen gf gef v = false ∧ e1Gen gf gef (c3Mul v 40) = false := by decide +kernel

theorem e1E_of_e1R_typeD : ∀ v : Fin 64, e1R v → c3Mul v v = 0 → e1Gen true true v = false →
    e1E v := by decide +kernel

theorem e1E_of_typeD : ∀ v : Fin 64, c3Mul v v = 0 → e1Gen true true v = false →
    e1Gen true true (c3Mul v 40) = false → e1E v := by decide +kernel

theorem e1E_conj_outer : ∀ s t : Fin 64, s.val % 2 = 1 → c3Mul s s = 0 → e1E t →
    c3Conj s t = t ∨ c3Conj s t = c3Mul t 40 := by decide +kernel

theorem e1_transvection_iff : ∀ v : Fin 64, v.val % 2 = 0 →
    ((c3Conj v 32 = 32 ∧ c3Conj v 8 = 8 ∧ c3Conj v 2 = 42) ↔
      (v.val / 16 % 2 = 1 ∧ v.val / 4 % 2 = 1)) := by decide +kernel

theorem e1_transvection_conj : ∀ v t : Fin 64, v.val % 2 = 0 → v.val / 16 % 2 = 1 →
    v.val / 4 % 2 = 1 → e1E t → c3Conj v t = if t.val / 2 % 2 = 0 then t else c3Mul t 40 := by
  decide +kernel

@[expose] def e1PQ (v : Fin 64) : Prop := v.val % 4 = 0 ∧ v ≠ 0 ∧ ¬ c3GenW v

instance : DecidablePred e1PQ := fun v => by unfold e1PQ; infer_instance

theorem e1PQ_mul_self : ∀ v : Fin 64, e1PQ (c3Mul v v) → v.val % 4 = 2 := by decide

theorem card_e1PQ_mul_self :
    (Finset.univ.filter fun v : Fin 64 => e1PQ (c3Mul v v)).card = 8 ∧ e1PQ (c3Mul 6 6) := by
  decide

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
