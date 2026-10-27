module

public import Certificates.Data.CFSGNative.Fi23.Tr
public import CFSG.Certificates.Kernel.Fi23Tr.Bits
import CFSG.Certificates.Kernel.Fi22LH.Loops
import CFSG.Certificates.Kernel.Fi22LH.TreeSpec

public section

namespace CFSG.KS.Fi23Tr

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.KS.Fi22LH

abbrev BSt := Array PBits × Std.HashMap PBits Nat × Table × Table

@[expose] def CInv (z : PBits) (alpha beta : Table) (S0 : PBits) (s : BSt) : Prop :=
  0 < s.1.size ∧ s.1[0]! = S0 ∧ s.2.2.1.size = s.1.size ∧ s.2.2.2.size = s.1.size ∧
    (∀ i < s.1.size, ∀ j < s.1.size, s.1[i]! = s.1[j]! → i = j) ∧
    (∀ k < s.1.size, s.2.1.get? s.1[k]! = some k) ∧
    (∀ B : PBits, (∀ k < s.1.size, s.1[k]! ≠ B) → s.2.1.get? B = none) ∧
    (∀ k, 0 < k → k < s.1.size → ap s.2.2.1 k < k ∧
      ((ap s.2.2.2 k = 1 ∧ s.1[k]! = pImg z alpha s.1[ap s.2.2.1 k]!) ∨
        (ap s.2.2.2 k = 2 ∧ s.1[k]! = pImg z beta s.1[ap s.2.2.1 k]!)))

@[expose] def ins (X : PBits) (h : Nat) (lv : UInt32) (s : BSt) : BSt × Nat :=
  match s.2.1.get? X with
  | some j => (s, j)
  | none => ((s.1.push X, s.2.1.insert X s.1.size, s.2.2.1.push (UInt32.ofNat h), s.2.2.2.push lv),
      s.1.size)

theorem ap_push_lt' {a : Table} {x : UInt32} {k : Nat} (hk : k < a.size) :
    ap (a.push x) k = ap a k := by
  unfold ap
  rw [get!_push_lt _ _ hk]

theorem ap_push_eq'' (a : Table) (x : UInt32) : ap (a.push x) a.size = x.toNat := by
  unfold ap
  rw [get!_push_eq]

theorem toNat_ofNat' {x : Nat} (hx : x < 2 ^ 32) : (UInt32.ofNat x).toNat = x := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hx]

theorem ap_push_of {a : Table} {x : UInt32} {k : Nat} (hk : a.size = k) :
    ap (a.push x) k = x.toNat := by
  subst hk
  exact ap_push_eq'' a x

theorem get!_push_of {α : Type} [Inhabited α] {a : Array α} {x : α} {k : Nat} (hk : a.size = k) :
    (a.push x)[k]! = x := by
  subst hk
  exact get!_push_eq a x

theorem ins_spec {z : PBits} {alpha beta : Table} {S0 X : PBits} {h : Nat} {lv : UInt32}
    {s : BSt} (H : CInv z alpha beta S0 s) (hh : h < s.1.size) (h32 : s.1.size + 1 < 2 ^ 32)
    (hX : (lv.toNat = 1 ∧ X = pImg z alpha s.1[h]!) ∨ (lv.toNat = 2 ∧ X = pImg z beta s.1[h]!)) :
    CInv z alpha beta S0 (ins X h lv s).1 ∧ (ins X h lv s).2 < (ins X h lv s).1.1.size ∧
      (ins X h lv s).1.1[(ins X h lv s).2]! = X ∧ s.1.size ≤ (ins X h lv s).1.1.size ∧
      (ins X h lv s).1.1.size ≤ s.1.size + 1 ∧
      ∀ k < s.1.size, (ins X h lv s).1.1[k]! = s.1[k]! := by
  obtain ⟨sets, tbl, par, lab⟩ := s
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := H
  dsimp only at *
  unfold ins
  dsimp only
  split
  · rename_i j hj
    have hmem : ∃ k < sets.size, sets[k]! = X := by
      refine Classical.byContradiction fun hn => ?_
      rw [c7 X (fun k hk e => hn ⟨k, hk, e⟩)] at hj
      exact absurd hj (by simp)
    obtain ⟨k, hk, e⟩ := hmem
    have := c6 k hk
    rw [e, hj] at this
    cases this
    dsimp only
    exact ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8⟩, hk, e, Nat.le_refl _, by omega, fun _ _ => rfl⟩
  · rename_i hj
    have hnew : ∀ k < sets.size, sets[k]! ≠ X := by
      intro k hk e
      rw [← e, c6 k hk] at hj
      exact absurd hj (by simp)
    have hpush : ∀ k < sets.size + 1, (sets.push X)[k]! = if k < sets.size then sets[k]! else X := by
      intro k hk
      by_cases hk' : k < sets.size
      · rw [if_pos hk', get!_push_lt _ _ hk']
      · rw [if_neg hk', get!_push_of (by omega)]
    refine ⟨⟨by simp, ?_, by simp [c3], by simp [c4], fun i hi j hj e => ?_, fun k hk => ?_,
      fun B hB => ?_, fun k hk0 hk => ?_⟩, by simp, by rw [get!_push_eq], by simp, by simp,
      fun k hk => get!_push_lt _ _ hk⟩
    · rw [get!_push_lt _ _ c1, c2]
    · rw [Array.size_push] at hi hj
      rw [hpush i hi, hpush j hj] at e
      by_cases hi' : i < sets.size <;> by_cases hj' : j < sets.size
      · rw [if_pos hi', if_pos hj'] at e
        exact c5 i hi' j hj' e
      · rw [if_pos hi', if_neg hj'] at e
        exact absurd e (hnew i hi')
      · rw [if_neg hi', if_pos hj'] at e
        exact absurd e.symm (hnew j hj')
      · omega
    · rw [Array.size_push] at hk
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hpush k hk]
      by_cases hk' : k < sets.size
      · rw [if_pos hk']
        have : (X == sets[k]!) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun e => hnew k hk' e.symm
        rw [this]
        exact c6 k hk'
      · have ek : k = sets.size := by omega
        rw [if_neg hk', beq_self_eq_true, ek]
        rfl
    · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      have hXB : (X == B) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        apply hB sets.size (by simp)
        rw [get!_push_eq, e]
      rw [hXB]
      exact c7 B fun k hk => by
        have := hB k (by simp; omega)
        rwa [get!_push_lt _ _ hk] at this
    · rw [Array.size_push] at hk
      rcases Nat.lt_or_ge k sets.size with hk' | hk'
      · rw [ap_push_lt' (by rw [c3]; exact hk'), ap_push_lt' (by rw [c4]; exact hk'),
          get!_push_lt _ _ hk']
        obtain ⟨p1, p2⟩ := c8 k hk0 hk'
        refine ⟨p1, ?_⟩
        rw [get!_push_lt _ _ (by omega)]
        exact p2
      · have e : k = sets.size := by omega
        subst e
        rw [ap_push_of c3, ap_push_of c4, get!_push_eq, toNat_ofNat' (by omega),
          get!_push_lt _ _ hh]
        exact ⟨hh, hX⟩

abbrev FSt := Array PBits × Std.HashMap PBits Nat × Table × Table × Table × Table

@[expose] def body (z : PBits) (alpha beta : Table) (h : Nat) (s : FSt) : Id (ForInStep FSt) :=
  if h < s.1.size then
    let r1 := ins (pImg z alpha s.1[h]!) h 1 (s.1, s.2.1, s.2.2.2.2.1, s.2.2.2.2.2)
    let r2 := ins (pImg z beta s.1[h]!) h 2 r1.1
    pure (.yield (r2.1.1, r2.1.2.1, s.2.2.1.push (UInt32.ofNat r1.2),
      s.2.2.2.1.push (UInt32.ofNat r2.2), r2.1.2.2.1, r2.1.2.2.2))
  else pure (.done s)

theorem trBFS_eq (z : PBits) (alpha beta : Table) (S0 : PBits) (limit : Nat) :
    trBFS z alpha beta S0 limit =
      let s := (forIn (m := Id) [0:limit] ((#[S0], (∅ : Std.HashMap PBits Nat).insert S0 0, #[], #[],
        #[0], #[0]) : FSt) (body z alpha beta))
      ⟨s.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2, s.2.1⟩ := by
  unfold trBFS
  simp only [Id.run]
  refine (congrArg (fun F => (forIn (m := Id) [0:limit] ((#[S0], (∅ : Std.HashMap PBits Nat).insert S0 0,
    #[], #[], #[0], #[0]) : FSt) F >>= fun (s : FSt) => (pure (⟨s.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1,
      s.2.2.2.2.2, s.2.1⟩ : TrOrb) : Id TrOrb))) (funext fun h => funext fun s => ?_)).trans rfl
  unfold body ins
  by_cases hh : h < s.1.size
  · simp only [hh, if_true]
    cases ha : s.2.1.get? (pImg z alpha s.1[h]!) with
    | some j =>
      simp only
      cases hb : s.2.1.get? (pImg z beta s.1[h]!) with
      | some j' => rfl
      | none => rfl
    | none =>
      simp only
      cases hb : (s.2.1.insert (pImg z alpha s.1[h]!) s.1.size).get? (pImg z beta s.1[h]!) with
      | some j' => rfl
      | none => rfl
  · simp only [hh, if_false]

@[expose] def TInv (z : PBits) (alpha beta : Table) (q : Nat) (s : FSt) : Prop :=
  s.2.2.1.size = q ∧ s.2.2.2.1.size = q ∧ ∀ k < q, ap s.2.2.1 k < s.1.size ∧
    pImg z alpha s.1[k]! = s.1[ap s.2.2.1 k]! ∧ ap s.2.2.2.1 k < s.1.size ∧
    pImg z beta s.1[k]! = s.1[ap s.2.2.2.1 k]!

theorem trBFS_spec (z : PBits) (alpha beta : Table) (S0 : PBits) (limit : Nat)
    (hlim : 2 * limit + 1 < 2 ^ 32) :
    let o := trBFS z alpha beta S0 limit
    0 < o.sets.size ∧ o.sets[0]! = S0 ∧ o.par.size = o.sets.size ∧ o.lab.size = o.sets.size ∧
      (∀ i < o.sets.size, ∀ j < o.sets.size, o.sets[i]! = o.sets[j]! → i = j) ∧
      (∀ k < o.sets.size, o.tbl.get? o.sets[k]! = some k) ∧
      (∀ B : PBits, (∀ k < o.sets.size, o.sets[k]! ≠ B) → o.tbl.get? B = none) ∧
      (∀ k, 0 < k → k < o.sets.size → ap o.par k < k ∧
        ((ap o.lab k = 1 ∧ o.sets[k]! = pImg z alpha o.sets[ap o.par k]!) ∨
          (ap o.lab k = 2 ∧ o.sets[k]! = pImg z beta o.sets[ap o.par k]!))) ∧
      (o.sets.size ≤ limit → o.pa.size = o.sets.size ∧ o.pb.size = o.sets.size ∧
        ∀ k < o.sets.size, ap o.pa k < o.sets.size ∧ pImg z alpha o.sets[k]! = o.sets[ap o.pa k]! ∧
          ap o.pb k < o.sets.size ∧ pImg z beta o.sets[k]! = o.sets[ap o.pb k]!) := by
  rw [trBFS_eq]
  intro o
  let P : FSt → BSt := fun s => (s.1, s.2.1, s.2.2.2.2.1, s.2.2.2.2.2)
  suffices H : CInv z alpha beta S0 (P (forIn (m := Id) [0:limit] ((#[S0],
      (∅ : Std.HashMap PBits Nat).insert S0 0, #[], #[], #[0], #[0]) : FSt) (body z alpha beta))) ∧
      ((forIn (m := Id) [0:limit] ((#[S0], (∅ : Std.HashMap PBits Nat).insert S0 0, #[], #[], #[0],
        #[0]) : FSt) (body z alpha beta)).1.size ≤ limit →
        TInv z alpha beta (forIn (m := Id) [0:limit] ((#[S0], (∅ : Std.HashMap PBits Nat).insert S0 0,
          #[], #[], #[0], #[0]) : FSt) (body z alpha beta)).1.size
          (forIn (m := Id) [0:limit] ((#[S0], (∅ : Std.HashMap PBits Nat).insert S0 0, #[], #[], #[0],
            #[0]) : FSt) (body z alpha beta))) by
    obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7, c8⟩, ht⟩ := H
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, ht⟩
  refine range_loop (fun q (s : FSt) => CInv z alpha beta S0 (P s) ∧ q ≤ s.1.size ∧
      s.1.size ≤ 2 * q + 1 ∧ TInv z alpha beta q s)
    (fun s => CInv z alpha beta S0 (P s) ∧ (s.1.size ≤ limit → TInv z alpha beta s.1.size s))
    _ limit _ ?_ ?_ ?_
  · rintro q s hq ⟨hC, hqs, hsz, hT⟩
    unfold body
    by_cases hlt : q < s.1.size
    · rw [if_pos hlt]
      change CInv z alpha beta S0 _ ∧ _
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ins_spec (lv := 1) hC hlt (by dsimp only [P]; omega)
        (Or.inl ⟨rfl, rfl⟩)
      dsimp only [P] at a1 a2 a3 a4 a5 a6 hC ⊢
      generalize hr1 : ins (pImg z alpha s.1[q]!) q 1 (s.1, s.2.1, s.2.2.2.2.1, s.2.2.2.2.2) = r1
        at a1 a2 a3 a4 a5 a6 ⊢
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := ins_spec (lv := 2) (X := pImg z beta s.1[q]!) (h := q) a1
        (by omega) (by omega) (Or.inr ⟨rfl, by rw [a6 q hlt]⟩)
      generalize hr2 : ins (pImg z beta s.1[q]!) q 2 r1.1 = r2 at b1 b2 b3 b4 b5 b6 ⊢
      obtain ⟨t1, t2, t3⟩ := hT
      refine ⟨b1, Nat.lt_of_lt_of_le hlt (Nat.le_trans a4 b4), Nat.le_trans b5 (by omega), by rw [Array.size_push, t1], by rw [Array.size_push, t2],
        fun k hk => ?_⟩
      try dsimp only
      rcases Nat.lt_or_ge k q with hk' | hk'
      · rw [ap_push_lt' (by rw [t1]; exact hk'), ap_push_lt' (by rw [t2]; exact hk')]
        obtain ⟨u1, u2, u3, u4⟩ := t3 k hk'
        refine ⟨by omega, ?_, by omega, ?_⟩
        · rw [b6 k (by omega), a6 k (by omega), u2, b6 _ (by omega), a6 _ u1]
        · rw [b6 k (by omega), a6 k (by omega), u4, b6 _ (by omega), a6 _ u3]
      · have ek : k = q := by omega
        subst ek
        rw [ap_push_of t1, toNat_ofNat' (by omega), ap_push_of t2, toNat_ofNat' (by omega)]
        refine ⟨by omega, ?_, b2, ?_⟩
        · rw [b6 _ (by omega), a6 k hlt, b6 _ a2, a3]
        · rw [b6 _ (by omega), a6 k hlt, b3]
    · rw [if_neg hlt]
      have e : q = s.1.size := by omega
      exact ⟨hC, fun _ => e ▸ hT⟩
  · rintro s ⟨hC, hqs, -, hT⟩
    refine ⟨hC, fun h => ?_⟩
    have e : s.1.size = limit := by omega
    rw [e]
    exact hT
  · dsimp only [P]
    refine ⟨⟨by simp, rfl, rfl, rfl, fun i hi j hj _ => ?_, fun k hk => ?_,
      fun B hB => ?_, fun k hk0 hk => ?_⟩, by simp, by simp, rfl, rfl,
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    · have hi' : i < 1 := hi
      have hj' : j < 1 := hj
      omega
    · have hk' : k < 1 := hk
      have : k = 0 := by omega
      subst this
      change ((∅ : Std.HashMap PBits Nat).insert S0 0).get? S0 = some 0
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]
    · change ((∅ : Std.HashMap PBits Nat).insert S0 0).get? B = none
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      have : (S0 == B) = false := by
        rw [beq_eq_false_iff_ne]
        exact hB 0 (by simp)
      rw [this]
      exact Std.HashMap.getElem?_empty
    · have hk' : k < 1 := hk
      omega

end CFSG.KS.Fi23Tr
