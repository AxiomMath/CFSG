module

public import Certificates.Data.Kernel.MonsterB.FischerElim
public import Aesop.BuiltinRules
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.FischerE

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def InvPair (n K : Nat) (F G : Nat → Nat → Nat) : Prop :=
  ∀ k < K, ∀ y < n, F k y < n ∧ G k (F k y) = y ∧ G k y < n ∧ F k (G k y) = y

theorem wordL_cons (F : Nat → Nat → Nat) (j : Nat) (w : List Nat) (y : Nat) :
    wordL F (j :: w) y = F j (wordL F w y) := rfl

theorem invWordL_cons (G : Nat → Nat → Nat) (j : Nat) (w : List Nat) (x : Nat) :
    invWordL G (j :: w) x = invWordL G w (G j x) := rfl

variable {n K : Nat} {F G : Nat → Nat → Nat}

theorem wordL_lt (h : InvPair n K F G) : ∀ w : List Nat, (∀ j ∈ w, j < K) → ∀ y < n,
    wordL F w y < n
  | [], _, _, hy => hy
  | j :: w, hw, y, hy => by
    rw [wordL_cons]
    exact (h j (hw j List.mem_cons_self) _
      (wordL_lt h w (fun k hk => hw k (List.mem_cons_of_mem j hk)) y hy)).1

theorem invWordL_lt (h : InvPair n K F G) : ∀ w : List Nat, (∀ j ∈ w, j < K) → ∀ x < n,
    invWordL G w x < n
  | [], _, _, hx => hx
  | j :: w, hw, x, hx => by
    rw [invWordL_cons]
    exact invWordL_lt h w (fun k hk => hw k (List.mem_cons_of_mem j hk)) _
      (h j (hw j List.mem_cons_self) x hx).2.2.1

theorem invWord_word (h : InvPair n K F G) : ∀ w : List Nat, (∀ j ∈ w, j < K) → ∀ y < n,
    invWordL G w (wordL F w y) = y
  | [], _, _, _ => rfl
  | j :: w, hw, y, hy => by
    have hw' : ∀ k ∈ w, k < K := fun k hk => hw k (List.mem_cons_of_mem j hk)
    rw [wordL_cons, invWordL_cons,
      (h j (hw j List.mem_cons_self) _ (wordL_lt h w hw' y hy)).2.1]
    exact invWord_word h w hw' y hy

theorem word_invWord (h : InvPair n K F G) : ∀ w : List Nat, (∀ j ∈ w, j < K) → ∀ x < n,
    wordL F w (invWordL G w x) = x
  | [], _, _, _ => rfl
  | j :: w, hw, x, hx => by
    have hw' : ∀ k ∈ w, k < K := fun k hk => hw k (List.mem_cons_of_mem j hk)
    have hj := h j (hw j List.mem_cons_self) x hx
    rw [invWordL_cons, wordL_cons, word_invWord h w hw' _ hj.2.2.1]
    exact hj.2.2.2

theorem invCand_eq_foldl' (n : Nat) (t : Array Nat) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem invCand_get {t : Array Nat} {s : Nat → Nat} (h1 : ∀ i < n, t[i]! < n ∧ s t[i]! = i)
    (h2 : ∀ x < n, s x < n ∧ t[s x]! = x) {x : Nat} (hx : x < n) : (invCand n t)[x]! = s x := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := (h1 k (by omega)).1
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          have a := (h1 i (by omega)).2
          have b := (h1 k (by omega)).2
          rw [e] at a
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  obtain ⟨-, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl']
  have hs := h2 x hx
  have e := hi (s x) hs.1
  rw [hs.2] at e
  exact e

end CFSG.KC.FischerE

end
