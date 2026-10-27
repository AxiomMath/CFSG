module

public import Certificates.Data.Kernel.SporSch.LyMat
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.SporSch.LyLoop

open CFSG.KC.Enum CFSG.KS

theorem forIn_list_spec {β : Type} (R : Nat → β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    ∀ k a (init : β), a + k ≤ E → R a init → R (a + k) (forIn (List.range' a k) init f)
  | 0, _, _, _, h => h
  | k + 1, a, init, hE, h => by
    obtain ⟨b', hb, hR⟩ := hf a init (by omega) h
    rw [List.range'_succ, List.forIn_cons, hb]
    have e : a + (k + 1) = a + 1 + k := by omega
    rw [e]
    exact forIn_list_spec R E f hf k (a + 1) b' (by omega) hR

theorem forIn_range_spec {β : Type} (R : Nat → β → Prop) (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) (h0 : R 0 init)
    (hf : ∀ j b, j < n → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    R n (forIn (m := Id) [:n] init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have e : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [e]
  have := forIn_list_spec R n f hf n 0 init (by omega) h0
  rw [Nat.zero_add] at this
  exact this

theorem strictN_eqP (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eqB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_eqP (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eqP (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem nIf_eqP (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem foldBlk_eqP (b : Nat) (f : Nat → Nat → Nat) (len s : Nat) :
    foldBlk b f len s = (List.range len).foldr (fun l s => f (b + l) s) s := by
  induction len generalizing s with
  | zero => rfl
  | succ len ih =>
    have e : foldBlk b f (len + 1) s = foldBlk b f len (f (b + len) s) :=
      strictN_eqP (f (b + len) s) (foldBlk b f len)
    rw [e, ih, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]

theorem foldr_range_addP (f : Nat → Nat → Nat) (t a b : Nat) :
    (List.range (a + b)).foldr f t = (List.range a).foldr f ((List.range b).foldr
      (fun l s => f (a + l) s) t) := by
  rw [List.range_add, List.foldr_append, List.foldr_map]

theorem foldN_eqP (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = (List.range n).foldr f s := by
  have hsl : ∀ a, Nat.shiftLeft a 6 = 64 * a := fun a => by
    change a <<< 6 = _
    rw [Nat.shiftLeft_eq]
    omega
  have hG : ∀ q t, Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q t =
      (List.range (64 * q)).foldr f t := by
    intro q
    induction q with
    | zero => intro t; rfl
    | succ q ih =>
      intro t
      have e : Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
          (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
          (q + 1) t = Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
          (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q
          (foldBlk (Nat.shiftLeft q 6) f 64 t) := strictN_eqP _ _
      rw [e, ih, foldBlk_eqP, hsl, Nat.mul_add, Nat.mul_one, foldr_range_addP]
  have e : foldN n f s = Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
      (Nat.shiftRight n 6) (foldBlk (Nat.shiftLeft (Nat.shiftRight n 6) 6) f (Nat.land n 63) s) :=
    rfl
  have hsr : Nat.shiftRight n 6 = n / 64 := by
    change n >>> 6 = _
    rw [Nat.shiftRight_eq_div_pow]
  have hla : Nat.land n 63 = n % 64 := by
    change n &&& 63 = _
    have h63 : (63 : Nat) = 2 ^ 6 - 1 := rfl
    rw [h63, Nat.and_two_pow_sub_one_eq_mod]
  rw [e, hG, foldBlk_eqP, hsl, hsr, hla, ← foldr_range_addP, Nat.div_add_mod]

theorem foldr_rev_eq_foldlP (g : Nat → Nat → Nat) (n : Nat) : ∀ s : Nat,
    (List.range n).foldr (fun i s => g (n - 1 - i) s) s
      = (List.range n).foldl (fun s i => g i s) s := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    have hf : (fun (x : Nat) (y : Nat) => g (n + 1 - 1 - Nat.succ x) y)
        = (fun (x : Nat) (y : Nat) => g (n - 1 - x) y) := by
      funext x y
      congr 1
      omega
    have hr : (List.range (n + 1)).foldr (fun i s => g (n + 1 - 1 - i) s) s =
        g (n + 1 - 1 - 0) ((List.range n).foldr (fun x y => g (n + 1 - 1 - Nat.succ x) y) s) := by
      rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    rw [hr, hf, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih s,
      Nat.sub_zero, Nat.add_sub_cancel]

theorem foldUp_eqP (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldUp n f s = (List.range n).foldl (fun s i => f i s) s :=
  (foldN_eqP n (fun i s => f (Nat.sub (Nat.sub n (nat_lit 1)) i) s) s).trans
    (foldr_rev_eq_foldlP f n s)

theorem fold_absorb {α : Type} (f : α → Nat → Nat) (F : Nat)
    (hA : ∀ x s, s ≤ F → s ≤ f x s ∧ f x s ≤ F) (hB : ∀ x, f x F = F) :
    ∀ (l : List α) (s : Nat), s ≤ F → s ≤ l.foldl (fun s x => f x s) s ∧
      l.foldl (fun s x => f x s) s ≤ F ∧ (s = F → l.foldl (fun s x => f x s) s = F)
  | [], s, h => ⟨le_refl s, h, id⟩
  | x :: l, s, h => by
    obtain ⟨h1, h2⟩ := hA x s h
    obtain ⟨i1, i2, i3⟩ := fold_absorb f F hA hB l (f x s) h2
    rw [List.foldl_cons]
    exact ⟨Nat.le_trans h1 i1, i2, fun hs => by rw [hs, hB] at i3 ⊢; exact i3 rfl⟩

theorem sortB_spec {E SO SOI : Nat → Nat} {c i : Nat}
    (h : CFSG.KS.SporSch.LyM.sortB E SO SOI c i = true) :
    SO i < c ∧ SOI (SO i) = i ∧ (i + 1 < c → E (SO i) < E (SO (i + 1))) := by
  have e : CFSG.KS.SporSch.LyM.sortB E SO SOI c i = (Nat.blt (SO i) c && (Nat.beq (SOI (SO i)) i &&
      Bool.rec (motive := fun _ => Bool) true (Nat.blt (E (SO i)) (E (SO (Nat.succ i))))
        (Nat.blt (Nat.succ i) c))) := by
    unfold CFSG.KS.SporSch.LyM.sortB
    rw [strictB_eqB, bAnd_eqP, bAnd_eqP]
  rw [e, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Eq.mp Nat.blt_eq h1, Nat.eq_of_beq_eq_true h2, fun hi => ?_⟩
  have hb : Nat.blt (Nat.succ i) c = true := Eq.mpr Nat.blt_eq hi
  rw [hb] at h3
  exact Eq.mp Nat.blt_eq h3

theorem sortB_inj {E SO SOI : Nat → Nat} {c : Nat}
    (h : ∀ i < c, CFSG.KS.SporSch.LyM.sortB E SO SOI c i = true) :
    ∀ a < c, ∀ b < c, E a = E b → a = b := by
  have hs := fun i (hi : i < c) => sortB_spec (h i hi)
  have mono : ∀ i j, i < j → j < c → E (SO i) < E (SO j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have step := (hs j (by omega)).2.2 hj
      rcases Nat.lt_or_ge i j with h' | h'
      · exact Nat.lt_trans (ih h' (by omega)) step
      · have : i = j := by omega
        subst this
        exact step
  let g : Fin c → Fin c := fun i => ⟨SO i.val, (hs i.val i.isLt).1⟩
  have ginj : Function.Injective g := by
    intro i i' e
    have e' : SO i.val = SO i'.val := congrArg Fin.val e
    apply Fin.ext
    rw [← (hs i.val i.isLt).2.1, ← (hs i'.val i'.isLt).2.1, e']
  have gsurj := Finite.surjective_of_injective ginj
  intro a ha b hb hab
  obtain ⟨i, hi⟩ := gsurj ⟨a, ha⟩
  obtain ⟨i', hi'⟩ := gsurj ⟨b, hb⟩
  have ea : SO i.val = a := congrArg Fin.val hi
  have eb : SO i'.val = b := congrArg Fin.val hi'
  rcases Nat.lt_trichotomy i.val i'.val with hlt | heq | hgt
  · have := mono _ _ hlt i'.isLt
    rw [ea, eb, hab] at this
    exact absurd this (Nat.lt_irrefl _)
  · rw [← ea, ← eb, heq]
  · have := mono _ _ hgt i.isLt
    rw [ea, eb, hab] at this
    exact absurd this (Nat.lt_irrefl _)

theorem ofFn_getP {α : Type} [Inhabited α] (P : Nat → α) {n i : Nat} (h : i < n) :
    (Array.ofFn (n := n) fun j => P j.val)[i]! = P i := by
  rw [getElem!_pos (Array.ofFn (n := n) fun j => P j.val) i (by simpa using h), Array.getElem_ofFn]

theorem ofFn_push {α : Type} (P : Nat → α) (n : Nat) :
    (Array.ofFn (n := n) fun j => P j.val).push (P n) = Array.ofFn (n := n + 1) fun j => P j.val := by
  apply Array.ext
  · simp
  · intro i h1 h2
    rw [Array.getElem_ofFn]
    by_cases hi : i < n
    · rw [Array.getElem_push_lt (by simpa using hi), Array.getElem_ofFn]
    · have : i = n := by simp at h2; omega
      subst this
      simp [Array.getElem_push]

end CFSG.KS.SporSch.LyLoop

end
