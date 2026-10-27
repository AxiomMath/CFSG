module

public import Certificates.Data.Kernel.MonsterB.FischerBT
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.FischerB

def Full : Nat → BT → Prop
  | 0, .lf _ => True
  | d + 1, .nd l r => Full d l ∧ Full d r
  | _, _ => False

theorem getB_lf (v i : Nat) : getB (.lf v) i = v := rfl

theorem getB_nd (l r : BT) (i : Nat) :
    getB (.nd l r) i = if i % 2 = 1 then getB r (i / 2) else getB l (i / 2) := by
  change Bool.rec (motive := fun _ => Nat) (getB l (Nat.shiftRight i 1))
    (getB r (Nat.shiftRight i 1)) (Nat.beq (Nat.land i 1) 1) = _
  have h1 : Nat.shiftRight i 1 = i / 2 := by
    change i >>> 1 = _
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  have h2 : Nat.land i 1 = i % 2 := Nat.and_one_is_mod i
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> rw [h] <;> rfl

theorem setB_lf (w i v : Nat) : setB (.lf w) i v = .lf v := rfl

theorem setB_nd (l r : BT) (i v : Nat) :
    setB (.nd l r) i v = if i % 2 = 1 then .nd l (setB r (i / 2) v) else .nd (setB l (i / 2) v) r := by
  change Bool.rec (motive := fun _ => BT) (BT.nd (setB l (Nat.shiftRight i 1) v) r)
    (BT.nd l (setB r (Nat.shiftRight i 1) v)) (Nat.beq (Nat.land i 1) 1) = _
  have h1 : Nat.shiftRight i 1 = i / 2 := by
    change i >>> 1 = _
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  have h2 : Nat.land i 1 = i % 2 := Nat.and_one_is_mod i
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> rw [h] <;> rfl

theorem getB_mkB (c : Nat) : ∀ (d i : Nat), getB (mkB c d) i = c
  | 0, _ => rfl
  | d + 1, i => by
    change getB (.nd (mkB c d) (mkB c d)) i = c
    rw [getB_nd]
    split_ifs <;> exact getB_mkB c d _

theorem full_mkB (c : Nat) : ∀ d, Full d (mkB c d)
  | 0 => trivial
  | d + 1 => ⟨full_mkB c d, full_mkB c d⟩

theorem full_setB : ∀ (d : Nat) (T : BT) (i v : Nat), Full d T → Full d (setB T i v)
  | 0, .lf _, _, _, _ => trivial
  | d + 1, .nd l r, i, v, ⟨hl, hr⟩ => by
    rw [setB_nd]
    split_ifs
    · exact ⟨hl, full_setB d r _ v hr⟩
    · exact ⟨full_setB d l _ v hl, hr⟩
  | 0, .nd _ _, _, _, h => absurd h id
  | _ + 1, .lf _, _, _, h => absurd h id

theorem getB_setB : ∀ (d : Nat) (T : BT) (i v j : Nat), Full d T → i < 2 ^ d → j < 2 ^ d →
    getB (setB T i v) j = if i = j then v else getB T j
  | 0, .lf w, i, v, j, _, hi, hj => by
    have : i = 0 := by simpa using hi
    have : j = 0 := by simpa using hj
    subst_vars
    rfl
  | d + 1, .nd l r, i, v, j, ⟨hl, hr⟩, hi, hj => by
    have hi2 : i / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    have hj2 : j / 2 < 2 ^ d := by rw [pow_succ] at hj; omega
    rw [setB_nd]
    rcases Nat.mod_two_eq_zero_or_one i with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one j with h' | h'
    · rw [if_neg (show ¬ i % 2 = 1 by omega), getB_nd, if_neg (show ¬ j % 2 = 1 by omega),
        getB_setB d l _ v _ hl hi2 hj2, getB_nd, if_neg (show ¬ j % 2 = 1 by omega)]
      by_cases e : i = j
      · rw [if_pos (show i / 2 = j / 2 by omega), if_pos e]
      · rw [if_neg (show ¬ i / 2 = j / 2 by omega), if_neg e]
    · rw [if_neg (show ¬ i % 2 = 1 by omega), getB_nd, if_pos h', if_neg (show ¬ i = j by omega),
        getB_nd, if_pos h']
    · rw [if_pos h, getB_nd, if_neg (show ¬ j % 2 = 1 by omega), if_neg (show ¬ i = j by omega),
        getB_nd, if_neg (show ¬ j % 2 = 1 by omega)]
    · rw [if_pos h, getB_nd, if_pos h', getB_setB d r _ v _ hr hi2 hj2, getB_nd, if_pos h']
      by_cases e : i = j
      · rw [if_pos (show i / 2 = j / 2 by omega), if_pos e]
      · rw [if_neg (show ¬ i / 2 = j / 2 by omega), if_neg e]
  | 0, .nd _ _, _, _, _, h, _, _ => absurd h id
  | _ + 1, .lf _, _, _, _, h, _, _ => absurd h id

theorem getT_eq (T : BT) (i : Nat) : getT T i = if i < 2048 then getB T i else 0 := by
  unfold getT
  by_cases h : i < 2048
  · have hb : Nat.blt i 2048 = true := by rw [Nat.blt_eq]; exact h
    rw [hb, if_pos h]
  · have hb : Nat.blt i 2048 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      exact h
    rw [hb, if_neg h]

theorem setT_eq (T : BT) (i v : Nat) : setT T i v = if i < 2048 then setB T i v else T := by
  unfold setT
  by_cases h : i < 2048
  · have hb : Nat.blt i 2048 = true := by rw [Nat.blt_eq]; exact h
    rw [hb, if_pos h]
  · have hb : Nat.blt i 2048 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      exact h
    rw [hb, if_neg h]

def RArr (a : Array Nat) (T : BT) : Prop := a.size = 2048 ∧ Full 11 T ∧ ∀ j, a[j]! = getT T j

theorem rArr_replicate (c : Nat) : RArr (Array.replicate 2048 c) (mkB c 11) := by
  refine ⟨Array.size_replicate, full_mkB c 11, fun j => ?_⟩
  rw [getT_eq, getB_mkB]
  by_cases h : j < 2048
  · rw [if_pos h, getElem!_pos _ j (by simpa using h), Array.getElem_replicate]
  · rw [if_neg h, getElem!_neg _ j (by simpa using h)]
    rfl

theorem rArr_get {a : Array Nat} {T : BT} (h : RArr a T) (j : Nat) : a[j]! = getT T j := h.2.2 j

theorem rArr_set {a : Array Nat} {T : BT} (h : RArr a T) (i v : Nat) :
    RArr (a.set! i v) (setT T i v) := by
  obtain ⟨hs, hf, hg⟩ := h
  by_cases hi : i < 2048
  · refine ⟨by rw [Array.size_set!, hs], by rw [setT_eq, if_pos hi]; exact full_setB 11 T i v hf,
      fun j => ?_⟩
    rw [setT_eq, if_pos hi, getT_eq]
    by_cases hj : j < 2048
    · rw [if_pos hj, getB_setB 11 T i v j hf hi hj]
      by_cases e : i = j
      · subst e
        rw [if_pos rfl, Array.getElem!_set!_self _ _ _ (by rw [hs]; exact hi)]
      · rw [if_neg e, Array.getElem!_set!_ne _ _ _ _ e, hg j, getT_eq, if_pos hj]
    · rw [if_neg hj, Array.getElem!_set!_ne _ _ _ _ (by omega), hg j, getT_eq, if_neg hj]
  · have ha : a.set! i v = a := by
      rw [Array.set!_eq_setIfInBounds]
      exact Array.setIfInBounds_eq_of_size_le (by omega)
    rw [ha, setT_eq, if_neg hi]
    exact ⟨hs, hf, hg⟩

theorem forIn_rel {α β : Type} (R : α → β → Prop) (n : Nat) (f : Nat → α → Id (ForInStep α))
    (g : Nat → β → Id (ForInStep β)) (a : α) (b : β) (h0 : R a b)
    (hs : ∀ i < n, ∀ a b, R a b →
      ∃ a' b', f i a = ForInStep.yield a' ∧ g i b = ForInStep.yield b' ∧ R a' b') :
    R (forIn [:n] a f) (forIn [:n] b g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have key : ∀ (l : List Nat), (∀ i ∈ l, i < n) → ∀ a b, R a b →
      R (forIn l a f) (forIn l b g) := by
    intro l
    induction l with
    | nil => intro _ a b h; exact h
    | cons i l ih =>
      intro hl a b h
      obtain ⟨a', b', hf, hg, h'⟩ := hs i (hl i List.mem_cons_self) a b h
      rw [List.forIn_cons, List.forIn_cons, hf, hg]
      exact ih (fun j hj => hl j (List.mem_cons_of_mem i hj)) a' b' h'
  exact key _ (fun i hi => by
    rw [List.mem_range'_1] at hi
    omega) a b h0

end CFSG.KC.FischerB

end
