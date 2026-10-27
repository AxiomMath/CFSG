module

public import Certificates.Data.Census
public import Certificates.Data.Kernel.GilmanCensus.Twin
import all Certificates.Data.Census

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

theorem forIn_yield {β : Type} (g : β → Nat → β) (f : Nat → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g b a)) :
    ∀ (l : List Nat) (init : β), forIn (m := Id) l init f = l.foldl g init
  | [], _ => rfl
  | a :: l, init => by
    rw [List.forIn_cons, hf]
    exact forIn_yield g f hf l (g init a)

theorem getElem!_eq_getD_toList (v : Array Nat) (i : Nat) : v[i]! = v.toList.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases v[i]? <;> rfl

theorem foldl_range'_succ {β : Type} (f : β → Nat → β) (k n : Nat) (s : β) :
    (List.range' (k + 1) n).foldl f s = (List.range' k n).foldl (fun s i => f s (i + 1)) s := by
  induction n generalizing k s with
  | zero => rfl
  | succ n ih =>
    simp only [List.range'_succ, List.foldl_cons]
    exact ih (k + 1) _

theorem sum_range'_dotS : ∀ (a b : List Nat) (s : Nat),
    (List.range' 0 a.length).foldl (fun s i => s + a.getD i 0 * b.getD i 0) s = s + dotS a b
  | [], _, s => by simp [dotS]
  | x :: xs, b, s => by
    rw [List.length_cons, List.range'_succ, List.foldl_cons, foldl_range'_succ]
    have e : ∀ i, (x :: xs).getD (i + 1) 0 * b.getD (i + 1) 0 = xs.getD i 0 * b.tail.getD i 0 := by
      intro i
      cases b <;> simp
    simp only [e]
    rw [sum_range'_dotS xs b.tail]
    cases b with
    | nil => simp [dotS]
    | cons y ys => simp [dotS]; omega

theorem dot3_eq (v w : Array Nat) : dot3 v w = dot3K v.toList w.toList := by
  unfold dot3 dot3K
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  change (Id.run (forIn (m := Id) (List.range' 0 v.size) 0
    (fun i s => pure (ForInStep.yield (s + v[i]! * w[i]!))))) % 3 = _
  rw [List.forIn_pure_yield_eq_foldl]
  simp only [Id.run_pure, getElem!_eq_getD_toList]
  have h := sum_range'_dotS v.toList w.toList 0
  rw [Array.length_toList, Nat.zero_add] at h
  rw [h]

theorem firstNZ_eq (v : Array Nat) : firstNZ v = firstNZK v.toList := by
  unfold firstNZ
  rw [← Array.forIn_toList]
  generalize v.toList = l
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.forIn_cons]
    by_cases h : (x % 3 != 0) = true
    · simp only [h, ↓reduceIte, firstNZK]
      rfl
    · simp only [h, ↓reduceIte, firstNZK, Bool.false_eq_true]
      exact ih

theorem line3_eq (v : Array Nat) : (line3 v).toList = line3K v.toList := by
  unfold line3 line3K
  rw [Array.toList_map, firstNZ_eq]

theorem loop_unfold {β : Type} (f : Unit → β → Id (ForInStep β)) (b : β) :
    forIn (m := Id) Lean.Loop.mk b f =
      (match f () b with | .done v => v | .yield v => forIn (m := Id) Lean.Loop.mk v f) :=
  Lean.Loop.forIn_eq_of_monadTail

@[expose] def bitsBody (_ : Unit) (s : Array Nat × Nat) : Id (ForInStep (Array Nat × Nat)) :=
  if (s.2 != 0) = true then
    pure (ForInStep.yield (s.1.push (s.2 ^^^ (s.2 &&& (s.2 - 1))).log2,
      s.2 ^^^ (s.2 ^^^ (s.2 &&& (s.2 - 1)))))
  else pure (ForInStep.done (s.1, s.2))

theorem bitsOf_run (m : Nat) :
    bitsOf m = (Id.run (forIn (m := Id) Lean.Loop.mk (#[], m) bitsBody)).1 := by
  unfold bitsOf
  rfl

theorem two_pow_lt_succ (i : Nat) : 2 ^ i < 2 ^ (i + 1) :=
  Nat.pow_lt_pow_succ (by decide)

theorem low_odd (i k : Nat) :
    (2 ^ (i + 1) * k + 2 ^ i) ^^^ ((2 ^ (i + 1) * k + 2 ^ i) &&& (2 ^ (i + 1) * k + 2 ^ i - 1)) =
      2 ^ i := by
  have h0 := Nat.one_le_two_pow (n := i)
  have hn1 : 2 ^ (i + 1) * k + 2 ^ i - 1 = 2 ^ (i + 1) * k + (2 ^ i - 1) := by omega
  have hb1 := two_pow_lt_succ i
  have hb2 : 2 ^ i - 1 < 2 ^ (i + 1) := by omega
  rw [hn1]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hb1,
    Nat.testBit_two_pow_mul_add _ hb2, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h1 : j < i + 1 <;> by_cases h2 : i = j <;> simp [h1, h2] <;> omega

theorem xor_low (i k : Nat) : (2 ^ (i + 1) * k + 2 ^ i) ^^^ 2 ^ i = 2 ^ (i + 1) * k := by
  have hb1 := two_pow_lt_succ i
  apply Nat.eq_of_testBit_eq
  intro j
  have e : 2 ^ (i + 1) * k = 2 ^ (i + 1) * k + 0 := rfl
  conv => rhs; rw [e]
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hb1,
    Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos (i + 1)), Nat.testBit_two_pow]
  by_cases h1 : j < i + 1 <;> by_cases h2 : i = j <;> simp [h1, h2] <;> omega

theorem bits_loop : ∀ (f i a : Nat) (out : Array Nat), a < 2 ^ f →
    (Id.run (forIn (m := Id) Lean.Loop.mk (out, 2 ^ i * a) bitsBody)).1 =
      out ++ (bitsA f i a).toArray := by
  intro f
  induction f with
  | zero =>
    intro i a out h
    have ha : a = 0 := by simpa using h
    subst ha
    rw [loop_unfold]
    simp [bitsBody, bitsA] <;> rfl
  | succ f ih =>
    intro i a out h
    by_cases ha : a = 0
    · subst ha
      rw [loop_unfold]
      simp [bitsBody, bitsA] <;> rfl
    obtain ⟨k, hk | hk⟩ : ∃ k, a = 2 * k ∨ a = 2 * k + 1 :=
      ⟨a / 2, by rcases Nat.mod_two_eq_zero_or_one a with h | h <;> omega⟩
    · have e : 2 ^ i * a = 2 ^ (i + 1) * k := by rw [hk, Nat.pow_succ, Nat.mul_assoc]
      rw [e, ih (i + 1) k out (by rw [Nat.pow_succ] at h; omega)]
      have hb : bitsA (f + 1) i a = bitsA f (i + 1) k := by
        simp only [bitsA]
        have h1 : (a == 0) = false := by simpa using ha
        have h2 : a % 2 = 0 := by omega
        have h3 : a / 2 = k := by omega
        simp [h1, h2, h3]
      rw [hb]
    · have e : 2 ^ i * a = 2 ^ (i + 1) * k + 2 ^ i := by
        rw [hk, Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
      rw [e, loop_unfold]
      have hne : ((2 ^ (i + 1) * k + 2 ^ i) != 0) = true := by
        have := Nat.two_pow_pos i
        simp only [bne_iff_ne, ne_eq]
        omega
      simp only [bitsBody, hne, ↓reduceIte, low_odd, xor_low, Nat.log2_two_pow]
      change (Id.run (forIn (m := Id) Lean.Loop.mk (out.push i, 2 ^ (i + 1) * k) bitsBody)).1 = _
      rw [ih (i + 1) k (out.push i) (by rw [Nat.pow_succ] at h; omega)]
      have hb : bitsA (f + 1) i a = i :: bitsA f (i + 1) k := by
        simp only [bitsA]
        have h1 : (a == 0) = false := by simpa using ha
        have h2 : a % 2 = 1 := by omega
        have h3 : a / 2 = k := by omega
        simp [h1, h2, h3]
      rw [hb]
      simp

theorem bitsOf_eq (m : Nat) (h : m < 2 ^ 128) : bitsOf m = (bitsK m).toArray := by
  rw [bitsOf_run]
  have := bits_loop 128 0 m #[] h
  rw [Nat.pow_zero, Nat.one_mul] at this
  rw [this]
  simp [bitsK]

theorem popc_eq (m : Nat) (h : m < 2 ^ 128) : popc m = popcK m := by
  rw [popc, bitsOf_eq m h, popcK, List.size_toArray]

theorem foldl_first_some (P : Nat → Bool) (l : List Nat) (x : Nat) :
    l.foldl (fun q i => if (q.isNone && P i) = true then some i else q) (some x) = some x := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa using ih

theorem foldl_first (P : Nat → Bool) (l : List Nat) :
    l.foldl (fun q i => if (q.isNone && P i) = true then some i else q) none = l.find? P := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : P a = true
    · simp only [List.foldl_cons, Option.isNone_none, Bool.true_and, h, ↓reduceIte,
        List.find?_cons]
      exact foldl_first_some P l a
    · simp only [Bool.not_eq_true] at h
      simp only [List.foldl_cons, Option.isNone_none, Bool.true_and, h, Bool.false_eq_true,
        ↓reduceIte, List.find?_cons]
      exact ih

theorem foldl_rows {α : Type} [Inhabited α] (p : Nat → α → Bool) (g : α → α) (R : Array α) :
    (List.range' 0 R.size).foldl
        (fun S i => if p i S[i]! = true then S.set! i (g S[i]!) else S) R =
      R.mapIdx (fun i r => if p i r = true then g r else r) := by
  have key : ∀ n a (S : Array α), a + n = R.size → S.size = R.size →
      (∀ i (hi : i < R.size), S[i]! = if i < a then (if p i R[i] = true then g R[i] else R[i])
        else R[i]) →
      (List.range' a n).foldl
        (fun S i => if p i S[i]! = true then S.set! i (g S[i]!) else S) S =
      R.mapIdx (fun i r => if p i r = true then g r else r) := by
    intro n
    induction n with
    | zero =>
      intro a S ha hs hS
      simp only [List.range'_zero, List.foldl_nil]
      apply Array.ext
      · simp [hs]
      · intro i h1 h2
        have := hS i (by omega)
        rw [getElem!_pos S i h1, if_pos (by omega)] at this
        rw [Array.getElem_mapIdx]
        exact this
    | succ n ih =>
      intro a S ha hs hS
      rw [List.range'_succ, List.foldl_cons]
      have hSa := hS a (by omega)
      rw [if_neg (by omega)] at hSa
      apply ih (a + 1) _ (by omega)
      · split <;> simp [hs]
      · intro i hi
        rw [hSa]
        by_cases hia : i = a
        · subst hia
          by_cases hp : p i R[i] = true
          · rw [if_pos hp, Array.set!_eq_setIfInBounds,
              getElem!_pos _ i (by simp [hs]; omega), Array.getElem_setIfInBounds_self]
            simp [hp]
          · rw [if_neg hp]
            have := hS i hi
            simp [hp, this]
        · have e : (if p a R[a] = true then S.set! a (g R[a]) else S)[i]! = S[i]! := by
            split
            · rw [Array.set!_eq_setIfInBounds, getElem!_pos _ i (by simp [hs]; omega),
                getElem!_pos S i (by omega), Array.getElem_setIfInBounds_ne (by omega) (Ne.symm hia)]
            · rfl
          rw [e, hS i hi]
          by_cases hlt : i < a
          · have h2 : i < a + 1 := by omega
            simp only [hlt, h2, ↓reduceIte]
          · have h2 : ¬i < a + 1 := by omega
            simp only [hlt, h2, ↓reduceIte]
  exact key R.size 0 R (by omega) rfl (fun i hi => by rw [getElem!_pos R i hi]; simp)

theorem foldl_rows' {α : Type} [Inhabited α] (p : Nat → α → Bool) (g : α → α) (R : Array α)
    (n : Nat) (hn : n = R.size) :
    (List.range' 0 n).foldl
        (fun S i => if p i S[i]! = true then S.set! i (g S[i]!) else S) R =
      R.mapIdx (fun i r => if p i r = true then g r else r) := by
  subst hn
  exact foldl_rows p g R

theorem idBind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem forIn_ifs {β : Type} (p : Nat → β → Bool) (h : Nat → β → β) (l : List Nat) (R : β) :
    forIn (m := Id) l R
        (fun i S => if p i S = true then pure (ForInStep.yield (h i S))
          else pure (ForInStep.yield S)) =
      l.foldl (fun S i => if p i S = true then h i S else S) R :=
  forIn_yield (fun S i => if p i S = true then h i S else S) _ (fun i S => by split <;> rfl) l R

@[expose] def elimRow (nc : Nat) (rowk r : Array Nat) (j : Nat) : Array Nat :=
  Array.ofFn (n := nc) fun c => (r[c.val]! + 3 - r[j]! * rowk[c.val]! % 3) % 3

@[expose] def rrM (nc m j : Nat) (s : Array (Array Nat) × Array Nat × Nat) :
    Array (Array Nat) × Array Nat × Nat :=
  if s.2.2 < m then
    match (List.range' s.2.2 (m - s.2.2)).find? (fun i => s.1[i]![j]! != 0) with
    | none => s
    | some qq =>
      let R1 := (s.1.set! s.2.2 s.1[qq]!).set! qq s.1[s.2.2]!
      let R2 := R1.set! s.2.2 (R1[s.2.2]!.map fun x => x * R1[s.2.2]![j]! % 3)
      ((List.range' 0 m).foldl (fun S i => if (i != s.2.2 && S[i]![j]! != 0) = true then
        S.set! i (elimRow nc R2[s.2.2]! S[i]! j) else S) R2, s.2.1.push j, s.2.2 + 1)
  else s

@[expose] def rrFold (rows : Array (Array Nat)) (nc : Nat) : Array (Array Nat) × Array Nat × Nat :=
  (List.range' 0 nc).foldl (fun s j => rrM nc rows.size j s) (rows.map (·.map (· % 3)), #[], 0)

theorem rowRed3_fold (rows : Array (Array Nat)) (nc : Nat) :
    rowRed3 rows nc =
      ((rrFold rows nc).1.extract 0 (rrFold rows nc).2.2, (rrFold rows nc).2.1) := by
  unfold rowRed3
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Array.size_map]
  rw [forIn_yield (fun s j => rrM nc rows.size j s)]
  · rfl
  · intro j s
    unfold rrM
    split
    · rw [forIn_yield (fun q i => if (q.isNone && s.1[i]![j]! != 0) = true then some i else q)
        _ (fun i q => by split <;> rfl), foldl_first, idBind]
      cases List.find? (fun i => s.1[i]![j]! != 0) (List.range' s.2.2 (rows.size - s.2.2)) with
      | none => rfl
      | some qq =>
        dsimp only
        rw [idBind, forIn_ifs]
        rfl
    · rfl

@[expose] def LL (R : Array (Array Nat)) : List (List Nat) := R.toList.map Array.toList

theorem getRow (R : Array (Array Nat)) (i : Nat) : (R[i]!).toList = (LL R).getD i [] := by
  rw [LL, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList, getElem!_def]
  cases R[i]? <;> rfl

theorem getEnt (R : Array (Array Nat)) (i j : Nat) : R[i]![j]! = ((LL R).getD i []).getD j 0 := by
  rw [getElem!_eq_getD_toList, getRow]

theorem LL_set (R : Array (Array Nat)) (i : Nat) (a : Array Nat) :
    LL (R.set! i a) = (LL R).set i a.toList := by
  rw [LL, LL, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, List.map_set]

theorem length_LL (R : Array (Array Nat)) : (LL R).length = R.size := by
  simp [LL]

theorem find_shift {α : Type} (P : List α → Bool) (F : Nat → Bool) :
    ∀ (rest above : List (List α)), (∀ i, F i = P ((above ++ rest).getD i [])) →
    (List.range' above.length rest.length).find? F =
      (rest.findIdx? P).map (above.length + ·)
  | [], _, _ => rfl
  | r :: tl, above, hF => by
    rw [List.length_cons, List.range'_succ, List.find?_cons, List.findIdx?_cons]
    have h0 : F above.length = P r := by
      rw [hF, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
      simp
    rw [h0]
    by_cases hp : P r = true
    · simp [hp]
    · have ih := find_shift P F tl (above ++ [r]) (fun i => by rw [hF]; simp)
      rw [List.length_append, List.length_singleton] at ih
      simp only [Bool.not_eq_true] at hp
      simp only [hp, ih, Option.map_map, Bool.false_eq_true, ↓reduceIte]
      congr 1
      funext x
      simp only [Function.comp_apply]
      omega

theorem findIn_spec {α : Type} (P : List α → Bool) (r0 : List α) : ∀ tl : List (List α),
    findIn P r0 tl = (tl.findIdx? P).map fun u => (tl.getD u [], tl.set u r0)
  | [] => rfl
  | r :: tl => by
    rw [findIn, List.findIdx?_cons]
    by_cases hp : P r = true
    · simp [hp]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, findIn_spec P r0 tl, Option.map_map, Bool.false_eq_true, ↓reduceIte]
      congr 1

theorem pickQ_spec {α : Type} (P : List α → Bool) (rest : List (List α)) :
    pickQ P rest = (rest.findIdx? P).map fun t =>
      (rest.getD t [], ((rest.set 0 (rest.getD t [])).set t (rest.getD 0 [])).tail) := by
  cases rest with
  | nil => rfl
  | cons r0 tl =>
    rw [pickQ, List.findIdx?_cons]
    by_cases hp : P r0 = true
    · simp [hp]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, findIn_spec, Option.map_map, Bool.false_eq_true, ↓reduceIte]
      congr 1

theorem getD_lt {α : Type} (l : List α) (d : α) {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem findIdx?_lt {α : Type} (P : List α → Bool) : ∀ (l : List (List α)) (t : Nat),
    l.findIdx? P = some t → t < l.length
  | [], _, h => by simp at h
  | r :: tl, t, h => by
    rw [List.findIdx?_cons] at h
    by_cases hp : P r = true
    · simp only [hp, ↓reduceIte, Option.some.injEq] at h
      simp [← h]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases hu : tl.findIdx? P with
      | none => simp [hu] at h
      | some u =>
        simp only [hu, Option.map_some, Option.some.injEq] at h
        have := findIdx?_lt P tl u hu
        simp only [List.length_cons]
        omega

theorem swap_head {α : Type} (rest : List (List α)) (t : Nat) (ht : t < rest.length) :
    (rest.set 0 (rest.getD t [])).set t (rest.getD 0 []) =
      rest.getD t [] :: ((rest.set 0 (rest.getD t [])).set t (rest.getD 0 [])).tail := by
  cases rest with
  | nil => simp at ht
  | cons r0 tl =>
    cases t with
    | zero => simp
    | succ u => simp [List.set]

theorem mem_swap {α : Type} (rest : List (List α)) (t : Nat) (r : List α)
    (h : r ∈ (rest.set 0 (rest.getD t [])).set t (rest.getD 0 [])) (ht : t < rest.length) :
    r ∈ rest := by
  have hne : rest ≠ [] := by
    intro h0
    simp [h0] at ht
  rcases List.mem_or_eq_of_mem_set h with h1 | h1
  · rcases List.mem_or_eq_of_mem_set h1 with h2 | h2
    · exact h2
    · rw [h2, getD_lt _ _ ht]
      exact List.getElem_mem ht
  · rw [h1, getD_lt _ _ (List.length_pos_iff.mpr hne)]
    exact List.getElem_mem _

theorem elimRow_toList (nc : Nat) (rowk r : Array Nat) (j : Nat) (hr : r.size = nc)
    (hk : rowk.size = nc) :
    (elimRow nc rowk r j).toList = subRow (r.toList.getD j 0) r.toList rowk.toList := by
  apply List.ext_getElem
  · simp [elimRow, subRow, hr, hk]
  · intro c h1 h2
    simp only [elimRow, Array.toList_ofFn, List.getElem_ofFn, subRow, List.getElem_zipWith]
    have hc : c < nc := by simpa [elimRow] using h1
    rw [getElem!_eq_getD_toList, getElem!_eq_getD_toList, getElem!_eq_getD_toList,
      getD_lt r.toList 0 (i := c) (by simp [hr, hc]),
      getD_lt rowk.toList 0 (i := c) (by simp [hk, hc])]

theorem LL_mapIdx (R : Array (Array Nat)) (g : Nat → Array Nat → Array Nat)
    (g' : Nat → List Nat → List Nat) (h : ∀ i (hi : i < R.size), (g i R[i]).toList = g' i R[i].toList) :
    LL (R.mapIdx g) = (LL R).mapIdx g' := by
  apply List.ext_getElem
  · simp [LL]
  · intro i h1 h2
    simp only [LL, Array.toList_mapIdx, List.getElem_map, List.getElem_mapIdx]
    have hi : i < R.size := by simpa [LL] using h1
    simp only [Array.getElem_toList]
    exact h i hi

theorem mapIdx_elim (A B : List (List Nat)) (x : List Nat) (Q : List Nat → Bool)
    (e : List Nat → List Nat) :
    (A ++ x :: B).mapIdx (fun i r => if (i != A.length && Q r) = true then e r else r) =
      A.map (fun r => if Q r = true then e r else r) ++
        x :: B.map (fun r => if Q r = true then e r else r) := by
  rw [List.mapIdx_append, List.mapIdx_cons]
  congr 1
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      have : ¬i = A.length := by simp at h1; omega
      simp [this]
  · congr 1
    · simp
    · apply List.ext_getElem
      · simp
      · intro i h1 h2
        have : (i + 1 + A.length != A.length) = true := by simp
        simp [this]

@[expose] def RRInv (nc m : Nat) (s : Array (Array Nat) × Array Nat × Nat)
    (st : List (List Nat) × List (List Nat) × List Nat) : Prop :=
  LL s.1 = st.1 ++ st.2.1 ∧ s.2.2 = st.1.length ∧ s.2.1.toList = st.2.2 ∧ s.1.size = m ∧
    ∀ r ∈ st.1 ++ st.2.1, r.length = nc

theorem getD_app {α : Type} (A B : List α) (t : Nat) (d : α) :
    (A ++ B).getD (A.length + t) d = B.getD t d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_app0 {α : Type} (A B : List α) (d : α) : (A ++ B).getD A.length d = B.getD 0 d := by
  simpa using getD_app A B 0 d

theorem set_app {α : Type} (A B : List α) (t : Nat) (x : α) :
    (A ++ B).set (A.length + t) x = A ++ B.set t x := by
  rw [List.set_append_right _ _ (by omega)]
  simp

theorem set_app0 {α : Type} (A B : List α) (x : α) : (A ++ B).set A.length x = A ++ B.set 0 x := by
  simpa using set_app A B 0 x

theorem length_subRow (t : Nat) (a b : List Nat) (n : Nat) (ha : a.length = n) (hb : b.length = n) :
    (subRow t a b).length = n := by
  simp [subRow, ha, hb]

theorem rr_step (nc m j : Nat) (s : Array (Array Nat) × Array Nat × Nat)
    (st : List (List Nat) × List (List Nat) × List Nat) (h : RRInv nc m s st) :
    RRInv nc m (rrM nc m j s) (rr3Step j st) := by
  obtain ⟨R, piv, k⟩ := s
  obtain ⟨A, rest, pv⟩ := st
  obtain ⟨hL, hk, hp, hm, hsz⟩ := h
  dsimp only at hL hk hp hm hsz
  subst hk
  have hlen : m = A.length + rest.length := by
    rw [← hm, ← length_LL, hL, List.length_append]
  have hF : (List.range' A.length (m - A.length)).find? (fun i => R[i]![j]! != 0) =
      (rest.findIdx? (fun r => r.getD j 0 != 0)).map (A.length + ·) := by
    rw [show m - A.length = rest.length by omega]
    exact find_shift _ _ rest A (fun i => by rw [getEnt, hL])
  unfold rrM rr3Step
  dsimp only
  rw [pickQ_spec]
  by_cases hlt : A.length < m
  · rw [if_pos hlt, hF]
    cases ht : rest.findIdx? (fun r => r.getD j 0 != 0) with
    | none => exact ⟨hL, rfl, hp, hm, hsz⟩
    | some t =>
      have htl := findIdx?_lt _ rest t ht
      dsimp only [Option.map_some]
      have hne : rest ≠ [] := by
        intro h0
        simp [h0] at htl
      have hR1 : LL ((R.set! A.length R[A.length + t]!).set! (A.length + t) R[A.length]!) =
          A ++ rest.getD t [] ::
            ((rest.set 0 (rest.getD t [])).set t (rest.getD 0 [])).tail := by
        rw [LL_set, LL_set, getRow, getRow, hL, getD_app, getD_app0, set_app0,
          set_app, swap_head rest t htl, List.tail_cons]
      generalize hR1d : (R.set! A.length R[A.length + t]!).set! (A.length + t) R[A.length]! = R1
        at hR1
      generalize hW : ((rest.set 0 (rest.getD t [])).set t (rest.getD 0 [])).tail = W at hR1 ⊢
      generalize hpd : rest.getD t [] = p at hR1 ⊢
      have hpmem : p ∈ rest := by
        rw [← hpd, getD_lt _ _ htl]
        exact List.getElem_mem htl
      have hWmem : ∀ r ∈ W, r ∈ rest := by
        intro r hr
        rw [← hW] at hr
        exact mem_swap rest t r (List.mem_of_mem_tail hr) htl
      have hR1k : (R1[A.length]!).toList = p := by
        rw [getRow, hR1, getD_app0]
        rfl
      have hR1kj : R1[A.length]![j]! = p.getD j 0 := by
        rw [getElem!_eq_getD_toList, hR1k]
      rw [hR1kj]
      generalize hpk : p.map (fun x => x * p.getD j 0 % 3) = pk
      have hR2 : LL (R1.set! A.length (R1[A.length]!.map fun x => x * p.getD j 0 % 3)) =
          A ++ pk :: W := by
        rw [LL_set, hR1, set_app0, Array.toList_map, hR1k, hpk]
        rfl
      generalize hR2d : R1.set! A.length (R1[A.length]!.map fun x => x * p.getD j 0 % 3) = R2
        at hR2
      have hrows : ∀ r ∈ A ++ pk :: W, r.length = nc := by
        intro r hr
        rcases List.mem_append.mp hr with h1 | h1
        · exact hsz r (List.mem_append_left _ h1)
        · rcases List.mem_cons.mp h1 with h2 | h2
          · rw [h2, ← hpk, List.length_map]
            exact hsz p (List.mem_append_right _ hpmem)
          · exact hsz r (List.mem_append_right _ (hWmem r h2))
      have hWlen : W.length + 1 = rest.length := by
        rw [← hW, List.length_tail, List.length_set, List.length_set]
        have := List.length_pos_iff.mpr hne
        omega
      have hm2 : m = R2.size := by
        rw [← length_LL, hR2, List.length_append, List.length_cons]
        omega
      have hR2k : (R2[A.length]!).toList = pk := by
        rw [getRow, hR2, getD_app0]
        rfl
      have hpkl : pk.length = nc := hrows pk (by simp)
      have e := foldl_rows' (fun i (r : Array Nat) => (i != A.length && r[j]! != 0))
        (fun r => elimRow nc R2[A.length]! r j) R2 m hm2
      rw [e]
      have hLL := LL_mapIdx R2 (fun i r => if (i != A.length && r[j]! != 0) = true then
          elimRow nc R2[A.length]! r j else r)
        (fun i r => if (i != A.length && r.getD j 0 != 0) = true then subRow (r.getD j 0) r pk
          else r) (fun i hi => by
            have hri : R2[i].toList.length = nc := by
              apply hrows
              rw [← hR2]
              simp [LL]
            rw [getElem!_eq_getD_toList]
            split
            · rw [elimRow_toList nc _ _ j (by simpa using hri)
                (by rw [← Array.length_toList, hR2k, hpkl]), hR2k]
            · rfl)
      rw [hR2, mapIdx_elim] at hLL
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hLL]
        simp
      · simp
      · rw [Array.toList_push, hp]
      · rw [Array.size_mapIdx, hm2]
      · intro r hr
        simp only [List.append_assoc, List.singleton_append] at hr
        rcases List.mem_append.mp hr with h1 | h1
        · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp h1
          have := hrows r' (List.mem_append_left _ hr')
          split
          · exact length_subRow _ _ _ _ this hpkl
          · exact this
        · rcases List.mem_cons.mp h1 with h2 | h2
          · rw [h2]
            exact hpkl
          · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp h2
            have := hrows r' (by simp [hr'])
            split
            · exact length_subRow _ _ _ _ this hpkl
            · exact this
  · rw [if_neg hlt]
    have h0 : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    exact ⟨hL, rfl, hp, hm, hsz⟩

theorem rr_fold (nc m : Nat) : ∀ (l : List Nat) s st, RRInv nc m s st →
    RRInv nc m (l.foldl (fun s j => rrM nc m j s) s) (l.foldl (fun st j => rr3Step j st) st)
  | [], _, _, h => h
  | j :: l, s, st, h => rr_fold nc m l _ _ (rr_step nc m j s st h)

theorem LL_extract (R : Array (Array Nat)) (k : Nat) : LL (R.extract 0 k) = (LL R).take k := by
  simp [LL, List.map_take]

theorem rowRed3_eq (rows : Array (Array Nat)) (nc : Nat) (h : ∀ r ∈ rows.toList, r.size = nc) :
    LL (rowRed3 rows nc).1 = (rowRed3K (LL rows) nc).1 ∧
      (rowRed3 rows nc).2.toList = (rowRed3K (LL rows) nc).2 := by
  have h0 : RRInv nc rows.size (rows.map (·.map (· % 3)), #[], 0)
      ([], (LL rows).map (·.map (· % 3)), []) := by
    refine ⟨?_, rfl, rfl, by simp, ?_⟩
    · simp [LL]
    · intro r hr
      simp only [List.nil_append, LL, List.map_map, List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      simp [h a ha]
  have hI := rr_fold nc rows.size (List.range' 0 nc) _ _ h0
  rw [rowRed3_fold, rrFold, rowRed3K, List.range_eq_range']
  obtain ⟨hL, hk, hp, -, -⟩ := hI
  refine ⟨?_, hp⟩
  rw [LL_extract, hL, hk, List.take_left]

theorem rank3_eq (rows : Array (Array Nat)) (nc : Nat) (h : ∀ r ∈ rows.toList, r.size = nc) :
    rank3 rows nc = rank3K (LL rows) nc := by
  rw [rank3, rank3K, ← (rowRed3_eq rows nc h).2, Array.length_toList]

theorem rr3Step_piv (j : Nat) (st : List (List Nat) × List (List Nat) × List Nat)
    (h1 : st.2.2.Nodup) (h2 : ∀ x ∈ st.2.2, x < j) (h3 : st.1.length = st.2.2.length) :
    (rr3Step j st).2.2.Nodup ∧ (∀ x ∈ (rr3Step j st).2.2, x < j + 1) ∧
      (rr3Step j st).1.length = (rr3Step j st).2.2.length := by
  unfold rr3Step
  split
  · exact ⟨h1, fun x hx => by have := h2 x hx; omega, h3⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨h1, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      have := h2 a ha
      omega
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have := h2 x hx
        omega
      · simp at hx
        omega
    · simp [h3]

theorem rr3_piv_fold : ∀ (n a : Nat) (st : List (List Nat) × List (List Nat) × List Nat),
    st.2.2.Nodup → (∀ x ∈ st.2.2, x < a) → st.1.length = st.2.2.length →
    ((List.range' a n).foldl (fun st j => rr3Step j st) st).2.2.Nodup ∧
      (∀ x ∈ ((List.range' a n).foldl (fun st j => rr3Step j st) st).2.2, x < a + n) ∧
      ((List.range' a n).foldl (fun st j => rr3Step j st) st).1.length =
        ((List.range' a n).foldl (fun st j => rr3Step j st) st).2.2.length
  | 0, a, st, h1, h2, h3 => ⟨h1, fun x hx => by have := h2 x hx; omega, h3⟩
  | n + 1, a, st, h1, h2, h3 => by
    rw [List.range'_succ, List.foldl_cons]
    obtain ⟨g1, g2, g3⟩ := rr3Step_piv a st h1 h2 h3
    obtain ⟨r1, r2, r3⟩ := rr3_piv_fold n (a + 1) _ g1 g2 g3
    exact ⟨r1, fun x hx => by have := r2 x hx; omega, r3⟩

theorem rr3_piv (rows : List (List Nat)) (nc : Nat) :
    (rowRed3K rows nc).2.Nodup ∧ (∀ x ∈ (rowRed3K rows nc).2, x < nc) ∧
      (rowRed3K rows nc).1.length = (rowRed3K rows nc).2.length := by
  rw [rowRed3K, List.range_eq_range']
  obtain ⟨r1, r2, r3⟩ := rr3_piv_fold nc 0 ([], rows.map (·.map (· % 3)), [])
    List.nodup_nil (by simp) rfl
  exact ⟨r1, fun x hx => by have := r2 x hx; omega, r3⟩

@[expose] def nullInner (R : Array (Array Nat)) (piv : Array Nat) (d j : Nat) : Array Nat :=
  (List.range' 0 piv.size).foldl (fun v i => v.set! piv[i]! ((3 - R[i]![j]!) % 3))
    ((Array.ofFn (n := d) fun _ => 0).set! j 1)

theorem null3_fold (rows : Array (Array Nat)) (d : Nat) :
    null3 rows d = (List.range' 0 d).foldl (fun out j =>
      if (!(rowRed3 rows d).2.contains j) = true then
        out.push (nullInner (rowRed3 rows d).1 (rowRed3 rows d).2 d j) else out) #[] := by
  unfold null3
  generalize rowRed3 rows d = rp
  obtain ⟨R, piv⟩ := rp
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield (fun out j => if (!piv.contains j) = true then
    out.push (nullInner R piv d j) else out) _ ?_]
  · rfl
  · intro j out
    split
    · rw [idBind, List.forIn_pure_yield_eq_foldl]
      rfl
    · rfl

theorem foldl_set_getD (ps : List (Nat × Nat)) (hps : (ps.map (·.1)).Nodup) :
    ∀ (v : Array Nat) (c : Nat), c < v.size →
      (ps.foldl (fun v q => v.set! q.1 q.2) v)[c]! =
        match ps.find? (fun q => q.1 == c) with
        | some q => q.2
        | none => v[c]! := by
  induction ps with
  | nil => intro v c _; rfl
  | cons q ps ih =>
    intro v c hc
    simp only [List.map_cons, List.nodup_cons] at hps
    rw [List.foldl_cons, ih hps.2 _ c (by simp [hc]), List.find?_cons]
    by_cases hq : q.1 = c
    · have hnone : ps.find? (fun q => q.1 == c) = none := by
        rw [List.find?_eq_none]
        intro x hx
        have : x.1 ≠ c := by
          intro h
          exact hps.1 (List.mem_map.mpr ⟨x, hx, by rw [h, hq]⟩)
        simpa using this
      rw [hnone]
      simp only [hq, beq_self_eq_true]
      rw [Array.set!_eq_setIfInBounds, getElem!_pos _ c (by simp [hc]),
        Array.getElem_setIfInBounds_self]
    · have hb : (q.1 == c) = false := by simpa using hq
      simp only [hb]
      cases ps.find? (fun q => q.1 == c) with
      | some q' => rfl
      | none =>
        rw [Array.set!_eq_setIfInBounds, getElem!_pos _ c (by simp [hc]), getElem!_pos v c hc,
          Array.getElem_setIfInBounds_ne hc hq]

theorem size_foldl_set (ps : List (Nat × Nat)) :
    ∀ v : Array Nat, (ps.foldl (fun v q => v.set! q.1 q.2) v).size = v.size := by
  induction ps with
  | nil => intro v; rfl
  | cons q ps ih => intro v; rw [List.foldl_cons, ih]; simp

theorem nullInner_eq (R : Array (Array Nat)) (piv : Array Nat) (d j : Nat)
    (hnd : piv.toList.Nodup) (hlt : ∀ x ∈ piv.toList, x < d) (hR : R.size = piv.size)
    (hj : j < d) (hjp : j ∉ piv.toList) :
    (nullInner R piv d j).toList = (List.range d).map (nullEnt (LL R) piv.toList j) := by
  have hps : (List.range' 0 piv.size).map (fun i => (piv[i]!, (3 - R[i]![j]!) % 3)) =
      (List.zip piv.toList (LL R)).map (fun p => (p.1, (3 - p.2.getD j 0) % 3)) := by
    apply List.ext_getElem
    · simp [LL, hR]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range', List.getElem_zip, Nat.zero_add,
        Nat.one_mul]
      have hi : i < piv.size := by simpa using h1
      have hiL : i < (LL R).length := by simp [LL, hR, hi]
      rw [getEnt, getD_lt (LL R) [] hiL, getElem!_pos piv i hi]
      rfl
  have hkeys : ((List.range' 0 piv.size).map (fun i => (piv[i]!, (3 - R[i]![j]!) % 3))).map
      (·.1) = piv.toList := by
    rw [hps, List.map_map]
    apply List.ext_getElem
    · simp [LL, hR]
    · intro i h1 h2
      simp
  have hv0 : ((Array.ofFn (n := d) fun _ => (0 : Nat)).set! j 1).size = d := by simp
  have hfold : nullInner R piv d j =
      ((List.range' 0 piv.size).map (fun i => (piv[i]!, (3 - R[i]![j]!) % 3))).foldl
        (fun v q => v.set! q.1 q.2) ((Array.ofFn (n := d) fun _ => 0).set! j 1) := by
    rw [List.foldl_map]
    rfl
  apply List.ext_getElem
  · rw [Array.length_toList, hfold, size_foldl_set, hv0, List.length_map, List.length_range]
  · intro c h1 h2
    have hc : c < d := by simpa using h2
    rw [List.getElem_map, List.getElem_range]
    have e1 : (nullInner R piv d j).toList[c] = (nullInner R piv d j)[c]! := by
      rw [Array.getElem_toList, getElem!_pos _ c (by simpa using h1)]
    rw [e1, hfold]
    rw [foldl_set_getD _ (by rw [hkeys]; exact hnd) _ c (by rw [hv0]; exact hc), hps,
      List.find?_map]
    unfold nullEnt
    cases hf : (List.zip piv.toList (LL R)).find? (fun p => p.1 == c) with
    | some p =>
      have : (List.find? ((fun q => q.1 == c) ∘ fun p => (p.1, (3 - p.2.getD j 0) % 3))
          (List.zip piv.toList (LL R))) = some p := by
        rw [← hf]
        rfl
      rw [this]
      rfl
    | none =>
      have : (List.find? ((fun q => q.1 == c) ∘ fun p => (p.1, (3 - p.2.getD j 0) % 3))
          (List.zip piv.toList (LL R))) = none := by
        rw [← hf]
        rfl
      rw [this]
      dsimp only [Option.map_none]
      rw [Array.set!_eq_setIfInBounds, getElem!_pos _ c (by simp [hc])]
      by_cases hcj : c = j
      · subst hcj
        simp
      · rw [Array.getElem_setIfInBounds_ne (by simp [hc]) (Ne.symm hcj)]
        simp [hcj]

theorem foldl_push_filterMap {β : Type} (c : Nat → Bool) (f : Nat → β) :
    ∀ (l : List Nat) (acc : Array β),
      (l.foldl (fun out j => if c j = true then out.push (f j) else out) acc).toList =
        acc.toList ++ l.filterMap (fun j => if c j = true then some (f j) else none)
  | [], acc => by simp
  | j :: l, acc => by
    rw [List.foldl_cons, foldl_push_filterMap c f l, List.filterMap_cons]
    by_cases h : c j = true
    · simp [h]
    · simp [h]

theorem filterMap_congr' {α β : Type} (f g : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x (by simp),
      filterMap_congr' f g l (fun y hy => h y (by simp [hy]))]

theorem null3_eq (rows : Array (Array Nat)) (d : Nat) (h : ∀ r ∈ rows.toList, r.size = d) :
    LL (null3 rows d) = null3K (LL rows) d := by
  obtain ⟨hR, hP⟩ := rowRed3_eq rows d h
  obtain ⟨hnd, hlt, hlen⟩ := rr3_piv (LL rows) d
  rw [null3_fold, null3K, LL, foldl_push_filterMap, List.range_eq_range']
  simp only [Array.toList_empty, List.nil_append, List.map_filterMap]
  apply filterMap_congr'
  intro j hj
  have hjd : j < d := by simpa using hj
  rw [← hP, Array.contains_toList]
  by_cases hc : (rowRed3 rows d).2.contains j = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.map_none]
  · have hjp : j ∉ (rowRed3 rows d).2.toList := by simpa using hc
    have hsz : (rowRed3 rows d).1.size = (rowRed3 rows d).2.size := by
      rw [← length_LL, hR, ← Array.length_toList, hP, hlen]
    simp only [hc, Bool.not_false, ↓reduceIte, Option.map_some, Bool.false_eq_true]
    rw [nullInner_eq _ _ d j (by rw [hP]; exact hnd) (by rw [hP]; exact hlt) hsz hjd hjp, hR,
      List.range_eq_range']


end Certificates.GilmanCensusK

end
