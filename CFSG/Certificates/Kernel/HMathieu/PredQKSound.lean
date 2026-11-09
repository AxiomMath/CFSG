module

public import Certificates.Data.Kernel.HMathieu.PredQK
public import CFSG.Certificates.Kernel.HMathieu.PredSound
public import CFSG.Certificates.Kernel.HMathieu.MatSearch

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Loop CFSG.KC.Enum CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat

theorem bltQ (a b : Nat) : Nat.blt a b = decide (a < b) := by
  by_cases h : a < b
  · simp [h]
  · rw [decide_eq_false h]
    exact Bool.eq_false_iff.mpr fun h' => h (by simpa using h')

theorem bleQ (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  by_cases h : a ≤ b
  · simp [h]
  · rw [decide_eq_false h]
    exact Bool.eq_false_iff.mpr fun h' => h (by simpa using h')

theorem beqQ (a b : Nat) : Nat.beq a b = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · rw [decide_eq_false h]
    exact Bool.eq_false_iff.mpr fun h' => h (by simpa using h')

theorem shlQ (y : Nat) : Nat.shiftLeft 1 y = 2 ^ y :=
  (Nat.shiftLeft_eq 1 y).trans (Nat.one_mul _)

theorem actMK_eq (cs : List Nat) (m : Nat) : actMK cs m = actM cs m := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih =>
    change Nat.xor (Bool.rec (motive := fun _ => Nat) 0 c (Nat.beq (Nat.land m 1) 1))
      (actMK cs (Nat.shiftRight m 1)) = _
    have h1 : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m
    have h2 : Nat.shiftRight m 1 = m / 2 := Nat.shiftRight_eq_div_pow m 1
    rw [h1, h2, ih, actM, beqQ]
    by_cases h : m % 2 = 1
    · rw [if_pos h, decide_eq_true h]
      rfl
    · rw [if_neg h, decide_eq_false h]
      rfl

theorem fixLstQ_eq (M F : List Nat) : fixLstQ M F = F.filter fun m => actM M m == m := by
  induction F with
  | nil => rfl
  | cons f F ih =>
    change Bool.rec (motive := fun _ => List Nat) (fixLstQ M F) (f :: fixLstQ M F)
      (Nat.beq (actMK M f) f) = _
    rw [ih, List.filter_cons, actMK_eq, beqQ]
    by_cases h : actM M f = f
    · rw [decide_eq_true h, if_pos (by simp [h])]
    · rw [decide_eq_false h, if_neg (by simpa using h)]

theorem lenK_eq {α : Type} (l : List α) : lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.succ (lenK l) = _
    rw [ih, List.length_cons]

theorem lAllK_eq {α : Type} (l : List α) (f : α → Bool) : lAllK l f = l.all f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => Bool) false (lAllK l f) (f x) = _
    rw [ih, List.all_cons]
    cases f x <;> rfl

theorem nAllK_eq (n : Nat) (f : Nat → Bool) : nAllK n f = (List.range n).all f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (nAllK n f) (f n) = _
    rw [ih, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
    cases f n <;> simp

theorem strictB_eqQ (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem quadK_eq (n : Nat) (Ms : List (List Nat)) : quadK n Ms = quadBasisOK n actM Ms := by
  unfold quadK quadBasisOK
  rw [lAllK_eq]
  refine congrArg _ (funext fun s => ?_)
  rw [lAllK_eq]
  refine congrArg _ (funext fun t => ?_)
  rw [nAllK_eq]
  refine congrArg _ (funext fun j => ?_)
  rw [strictB_eqQ, actMK_eq, actMK_eq, shlQ, beqQ]
  by_cases h : actM s (Nat.xor (actM t (2 ^ j)) (2 ^ j)) = Nat.xor (actM t (2 ^ j)) (2 ^ j)
  · rw [decide_eq_true h]
    exact (beq_iff_eq.mpr h).symm
  · rw [decide_eq_false h]
    exact (beq_eq_false_iff_ne.mpr h).symm

theorem cmpQK_eq (n : Nat) (strict : Bool) {k : Nat} (hk : 0 < k) (c : Nat) :
    cmpQK n strict k c = if strict then decide (2 * k < n - Nat.log 2 c)
      else decide (2 * k ≤ n - Nat.log 2 c) := by
  have e2 : Nat.mul 2 k = 2 * k := rfl
  have es : Nat.sub n (2 * k) = n - 2 * k := rfl
  cases strict
  · change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool)
      (Nat.blt c (Nat.shiftLeft 1 (Nat.succ (Nat.sub n (Nat.mul 2 k))))) true (Nat.beq c 0))
      (Nat.ble (Nat.mul 2 k) n) = _
    rw [if_neg Bool.false_ne_true, e2, es, shlQ, bltQ, bleQ, beqQ]
    by_cases h1 : 2 * k ≤ n
    · rw [decide_eq_true h1]
      by_cases hc : c = 0
      · rw [decide_eq_true hc]
        subst hc
        exact (decide_eq_true (by rw [Nat.log_zero_right]; omega)).symm
      · rw [decide_eq_false hc]
        have key := Nat.log_lt_iff_lt_pow (b := 2) (by norm_num) (x := Nat.succ (n - 2 * k)) hc
        by_cases hl : Nat.log 2 c < Nat.succ (n - 2 * k)
        · rw [decide_eq_true (key.mp hl)]
          exact (decide_eq_true (by omega)).symm
        · rw [decide_eq_false (mt key.mpr hl)]
          exact (decide_eq_false (by omega)).symm
    · rw [decide_eq_false h1]
      exact (decide_eq_false (by omega)).symm
  · change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool)
      (Nat.blt c (Nat.shiftLeft 1 (Nat.sub n (Nat.mul 2 k)))) true (Nat.beq c 0))
      (Nat.blt (Nat.mul 2 k) n) = _
    rw [if_pos rfl, e2, es, shlQ, bltQ, bltQ, beqQ]
    by_cases h1 : 2 * k < n
    · rw [decide_eq_true h1]
      by_cases hc : c = 0
      · rw [decide_eq_true hc]
        subst hc
        exact (decide_eq_true (by rw [Nat.log_zero_right]; omega)).symm
      · rw [decide_eq_false hc]
        have key := Nat.log_lt_iff_lt_pow (b := 2) (by norm_num) (x := n - 2 * k) hc
        by_cases hl : Nat.log 2 c < n - 2 * k
        · rw [decide_eq_true (key.mp hl)]
          exact (decide_eq_true (by omega)).symm
        · rw [decide_eq_false (mt key.mpr hl)]
          exact (decide_eq_false (by omega)).symm
    · rw [decide_eq_false h1]
      exact (decide_eq_false (by omega)).symm

theorem predQK_eq (n : Nat) (strict : Bool) (Ms : List (List Nat)) :
    predQK n strict Ms (fixMasks n actM Ms) = predQ n actM strict Ms := by
  cases Ms with
  | nil => rfl
  | cons M Ms =>
    change Bool.rec (motive := fun _ => Bool) true
      (cmpQK n strict (lenK (M :: Ms)) (lenK (fixMasks n actM (M :: Ms)))) (quadK n (M :: Ms)) = _
    rw [quadK_eq, lenK_eq, lenK_eq, cmpQK_eq n strict (by simp)]
    unfold predQ
    cases quadBasisOK n actM (M :: Ms) <;> simp

theorem gAllR_fixK (m : Nat) (M : List (List Nat))
    (pred : List Nat → List Nat → List (List Nat) × List Nat → Bool) (k : Nat) (l S : List Nat)
    (c : Nat) (st : List (List Nat) × List Nat) (rs : List (Nat × Nat)) (x : Nat) :
    gAllR m (fun st y => (M.getD y [] :: st.1, st.2.filter fun f => actM (M.getD y []) f == f))
        pred k l S c st rs x =
      gAllR m (fun st y => (M.getD y [] :: st.1, fixLstQ (M.getD y []) st.2))
        pred k l S c st rs x := by
  have h : (fun (st : List (List Nat) × List Nat) (y : Nat) =>
      (M.getD y [] :: st.1, st.2.filter fun f => actM (M.getD y []) f == f)) =
      fun st y => (M.getD y [] :: st.1, fixLstQ (M.getD y []) st.2) :=
    funext fun st => funext fun y => by rw [fixLstQ_eq]
  rw [h]

section Search

open CFSG.QuasithinUnique.Setup.X1

variable {P : Type} [Group P] [DecidableEq P]

theorem forallGreedyAll_predQ {R : List P} {D : List (Nat × Nat)}
    (T : GTabs R (cmD D) (mkD D)) (hD : D.length = R.length) {posF : P → Nat}
    (hpos : ∀ x, posF x = R.idxOf x) (act : P → Nat → Nat) (M : List (List Nat))
    (hM : ∀ k ≤ R.length, act (el R k) = actM (M.getD k [])) (n : Nat) (strict : Bool) (k : Nat)
    (hK : gAllR R.length (fun st y => (M.getD y [] :: st.1, fixLstQ (M.getD y []) st.2))
      (fun _ _ st => predQK n strict st.1 st.2) k [] [R.length] (2 ^ R.length - 1)
      ([], List.range (2 ^ n)) D 0 = true) :
    forallGreedyAll posF R (predQ n act strict) k [] = true := by
  have hel : ∀ x ∈ R, act x = actM (M.getD (R.idxOf x) []) := by
    intro x hx
    rw [← hM _ (idxOf_le x), el_idxOf (Or.inl hx)]
  refine forallGreedyAll_fix T hD hpos M n (predQ n act strict)
    (fun _ _ st => predQK n strict st.1 st.2) (fun l hl _ => ?_) k
    ((gAllR_fixK _ _ _ _ _ _ _ _ _ _).trans hK)
  rw [predQ_map n (fun x => M.getD (R.idxOf x) []) strict fun x hx => hel x (hl x hx)]
  exact (predQK_eq n strict _).symm

end Search

end CFSG.KC.HMathieu

end
