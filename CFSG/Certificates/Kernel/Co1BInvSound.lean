module

public import CFSG.Certificates.Kernel.Co1BTrSound
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KC.F2W

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native

@[expose] def pivotOf (M : Array Nat) (c : Nat) : Nat :=
  (List.range' c (24 - c)).foldl (fun p r => if p == 24 && (M[r]!).testBit c then r else p) 24

@[expose] def elimRow (c rp : Nat) (M : Array Nat) (r : Nat) : Array Nat :=
  if (r != c && (M[r]!).testBit c) = true then M.set! r (M[r]! ^^^ rp) else M

@[expose] def stepCol (M : Array Nat) (c : Nat) : Array Nat :=
  if pivotOf M c < 24 then
    (List.range' 0 24).foldl (elimRow c M[pivotOf M c]!)
      ((M.set! (pivotOf M c) M[c]!).set! c M[pivotOf M c]!)
  else M

@[expose] def startOf (X : Array Nat) : Array Nat :=
  Array.ofFn (n := 24) fun i => ((X[i.val]?.getD 0) % 2 ^ 24) ||| (1 <<< (24 + i.val))

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then pure (ForInStep.yield a) else pure (ForInStep.yield b) : Id (ForInStep β)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem inv_eq_model (X : Array Nat) : CFSG.Sporadic.Co1Schreier.Native.inv X =
    ((List.range' 0 24).foldl stepCol (startOf X)).map (· >>> 24) := by
  simp only [CFSG.Sporadic.Co1Schreier.Native.inv, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind,
    Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero]
  rfl

@[expose] def xs (f : Nat → Bool) (n : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun k b => f k ^^ b) n

theorem xs_succ (f : Nat → Bool) (n : Nat) : xs f (n + 1) = (f n ^^ xs f n) := rfl

theorem xs_congr {f g : Nat → Bool} : ∀ n, (∀ k < n, f k = g k) → xs f n = xs g n
  | 0, _ => rfl
  | n + 1, h => by rw [xs_succ, xs_succ, xs_congr n fun k hk => h k (by omega), h n (by omega)]

theorem xs_xor (f g : Nat → Bool) : ∀ n, xs (fun k => f k ^^ g k) n = (xs f n ^^ xs g n)
  | 0 => rfl
  | n + 1 => by
    rw [xs_succ, xs_succ, xs_succ, xs_xor f g n]
    cases f n <;> cases g n <;> cases xs f n <;> cases xs g n <;> rfl

theorem xs_and_left (b : Bool) (f : Nat → Bool) : ∀ n, xs (fun k => b && f k) n = (b && xs f n)
  | 0 => by cases b <;> rfl
  | n + 1 => by
    rw [xs_succ, xs_succ, xs_and_left b f n]
    cases b <;> simp

theorem xs_false : ∀ n, xs (fun _ => false) n = false
  | 0 => rfl
  | n + 1 => by rw [xs_succ, xs_false n]; rfl

theorem xs_comm (f : Nat → Nat → Bool) (m : Nat) : ∀ n,
    xs (fun j => xs (fun k => f j k) m) n = xs (fun k => xs (fun j => f j k) n) m
  | 0 => (xs_false m).symm
  | n + 1 => by
    rw [xs_succ, xs_comm f m n, ← xs_xor]
    rfl

theorem xs_single (a : Nat) (b : Bool) : ∀ n, xs (fun j => decide (j = a) && b) n = (decide (a < n) && b)
  | 0 => by simp [xs]
  | n + 1 => by
    rw [xs_succ, xs_single a b n]
    by_cases h : n = a
    · subst h
      simp
    · by_cases h' : a < n
      · simp [h, h', show a < n + 1 by omega]
      · simp [h, h', show ¬ a < n + 1 by omega]

@[expose] def rw' (X : Array Nat) (k : Nat) : Nat := X[k]?.getD 0

@[expose] def dot (a v : Nat) : Bool := xs (fun j => a.testBit j && v.testBit j) 24

@[expose] def colv (X : Array Nat) (u : Nat) : Nat :=
  (List.range 24).foldl (fun acc k => if dot (rw' X k) u then acc ||| (1 <<< k) else acc) 0

theorem testBit_colv (X : Array Nat) (u k : Nat) :
    (colv X u).testBit k = (decide (k < 24) && dot (rw' X k) u) :=
  testBit_ofBitsFold _ k 24

theorem colv_lt (X : Array Nat) (u : Nat) : colv X u < 2 ^ 24 :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by rw [testBit_colv]; simp [Nat.not_lt.2 hk]

theorem testBit_vm (X : Array Nat) (v j : Nat) :
    (vecMulN 24 X v).testBit j = xs (fun k => v.testBit k && (rw' X k).testBit j) 24 := by
  rw [vecMulN, foldl_range_xor (rw' X) (fun k => X[k]?.getD 0) v.testBit 24 fun _ _ => rfl,
    testBit_condRec]
  rfl

theorem vm_lt {X : Array Nat} (hX : ∀ k, rw' X k < 2 ^ 24) (v : Nat) : vecMulN 24 X v < 2 ^ 24 :=
  Nat.lt_pow_two_of_testBit _ fun j hj => by
    rw [testBit_vm]
    refine (xs_congr 24 fun k _ => ?_).trans (xs_false 24)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hX k) (Nat.pow_le_pow_right (by omega) hj)),
      Bool.and_false]

theorem xor_and (a b c : Bool) : ((a ^^ b) && c) = ((a && c) ^^ (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem vm_xor (X : Array Nat) (a b : Nat) :
    vecMulN 24 X (a ^^^ b) = vecMulN 24 X a ^^^ vecMulN 24 X b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_vm, testBit_vm, testBit_vm, ← xs_xor]
  exact xs_congr 24 fun k _ => by rw [Nat.testBit_xor, xor_and]

theorem dot_xor (a b v : Nat) : dot (a ^^^ b) v = (dot a v ^^ dot b v) := by
  rw [dot, dot, dot, ← xs_xor]
  exact xs_congr 24 fun k _ => by rw [Nat.testBit_xor, xor_and]

theorem vm_one {X : Array Nat} {r : Nat} (hr : r < 24) : vecMulN 24 X (1 <<< r) = rw' X r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_vm]
  rw [xs_congr (g := fun k => decide (k = r) && (rw' X r).testBit j) 24 fun k _ => by
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : k = r
    · subst h
      simp
    · simp [h, Ne.symm h]]
  rw [xs_single]
  simp [hr]

theorem dot_vm (X : Array Nat) (a u : Nat) : dot (vecMulN 24 X a) u = dot a (colv X u) := by
  rw [dot, dot]
  have h1 : ∀ j, ((vecMulN 24 X a).testBit j && u.testBit j) =
      xs (fun k => a.testBit k && ((rw' X k).testBit j && u.testBit j)) 24 := by
    intro j
    rw [testBit_vm, Bool.and_comm, ← xs_and_left]
    exact xs_congr 24 fun k _ => by cases a.testBit k <;> cases u.testBit j <;> simp
  rw [xs_congr 24 fun j _ => h1 j, xs_comm]
  refine xs_congr 24 fun k hk => ?_
  rw [xs_and_left, testBit_colv]
  simp [hk, dot]

theorem dot_one {k v : Nat} (hk : k < 24) : dot (1 <<< k) v = v.testBit k := by
  rw [dot, xs_congr (g := fun j => decide (j = k) && v.testBit k) 24 fun j _ => by
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : j = k
    · subst h
      simp
    · simp [h, Ne.symm h]]
  rw [xs_single]
  simp [hk]

theorem map_rw' (X : Array Nat) (g : Nat → Nat) (hg : g 0 = 0) (k : Nat) :
    rw' (X.map g) k = g (rw' X k) := by
  rw [rw', rw', Array.getElem?_map]
  cases X[k]? <;> simp [hg]

theorem vm_zero (X : Array Nat) : vecMulN 24 X 0 = 0 :=
  Nat.eq_of_testBit_eq fun j => by
    rw [testBit_vm, Nat.zero_testBit]
    exact (xs_congr 24 fun k _ => by rw [Nat.zero_testBit, Bool.false_and]).trans (xs_false 24)

theorem vm_assoc (X Y : Array Nat) (a : Nat) :
    vecMulN 24 Y (vecMulN 24 X a) = vecMulN 24 (mulRows 24 X Y) a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_vm, testBit_vm]
  have h1 : ∀ l, ((vecMulN 24 X a).testBit l && (rw' Y l).testBit j) =
      xs (fun k => a.testBit k && ((rw' X k).testBit l && (rw' Y l).testBit j)) 24 := by
    intro l
    rw [testBit_vm, Bool.and_comm, ← xs_and_left]
    exact xs_congr 24 fun k _ => by
      cases a.testBit k <;> cases (rw' Y l).testBit j <;> simp
  rw [xs_congr 24 fun l _ => h1 l, xs_comm]
  refine xs_congr 24 fun k _ => ?_
  rw [xs_and_left, mulRows, map_rw' X _ (vm_zero Y), testBit_vm]

theorem vm_id {a : Nat} (ha : a < 2 ^ 24) : vecMulN 24 (idRows 24) a = a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_vm]
  have hrow : ∀ k < 24, rw' (idRows 24) k = 1 <<< k := fun k hk => by
    simp [rw', idRows, hk]
  by_cases hj : j < 24
  · rw [xs_congr (g := fun k => decide (k = j) && a.testBit j) 24 fun k hk => by
      rw [hrow k hk, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases h : k = j
      · subst h
        simp
      · simp [h]]
    rw [xs_single]
    simp [hj]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))]
    refine (xs_congr 24 fun k hk => ?_).trans (xs_false 24)
    rw [hrow k hk, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right
    omega

theorem get_set {M : Array Nat} (hM : M.size = 24) {i j : Nat} (hj : j < 24) (v : Nat) :
    (M.set! i v)[j]! = if i = j then v else M[j]! := by
  have hj' : j < M.size := by omega
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (M.setIfInBounds i v) j (by simp [hj']),
    Array.getElem_setIfInBounds hj', getElem!_pos M j hj']

theorem size_set (M : Array Nat) (i v : Nat) : (M.set! i v).size = M.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem lo_xor (a b : Nat) : (a ^^^ b) % 2 ^ 24 = a % 2 ^ 24 ^^^ b % 2 ^ 24 :=
  Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow]
    cases decide (j < 24) <;> rfl

theorem hi_xor (a b : Nat) : (a ^^^ b) >>> 24 = (a >>> 24) ^^^ (b >>> 24) :=
  Nat.eq_of_testBit_eq fun j => by simp [Nat.testBit_xor]

@[expose] def Good (X M : Array Nat) : Prop :=
  M.size = 24 ∧ (∀ r < 24, M[r]! < 2 ^ 48 ∧ M[r]! % 2 ^ 24 = vecMulN 24 X (M[r]! >>> 24)) ∧
    ∀ v < 2 ^ 24, (∀ r < 24, dot (M[r]! >>> 24) v = false) → v = 0

@[expose] def Col (M : Array Nat) (c : Nat) : Prop := ∀ c' < c, ∀ r < 24, M[r]!.testBit c' = decide (r = c')

theorem good_xor {X M : Array Nat} (hG : Good X M) {r c : Nat} (hr : r < 24) (hc : c < 24) (hrc : r ≠ c) :
    Good X (M.set! r (M[r]! ^^^ M[c]!)) := by
  obtain ⟨hs, hrow, hinj⟩ := hG
  refine ⟨by rw [size_set, hs], fun s hs' => ?_, fun v hv h => hinj v hv fun s hs' => ?_⟩
  · rw [get_set hs hs']
    split
    · obtain ⟨b1, l1⟩ := hrow r hr
      obtain ⟨b2, l2⟩ := hrow c hc
      exact ⟨Nat.xor_lt_two_pow b1 b2, by rw [lo_xor, l1, l2, hi_xor, vm_xor]⟩
    · exact hrow s hs'
  · have hcs := h c hc
    rw [get_set hs hc, ite_eq_right hrc] at hcs
    by_cases hsr : s = r
    · subst hsr
      have := h s hs'
      rw [get_set hs hs', ite_eq_left rfl, hi_xor, dot_xor, hcs] at this
      simpa using this
    · have := h s hs'
      rwa [get_set hs hs', ite_eq_right (Ne.symm hsr)] at this

theorem good_swap {X M : Array Nat} (hG : Good X M) {p c : Nat} (hp : p < 24) (hc : c < 24) :
    Good X ((M.set! p M[c]!).set! c M[p]!) := by
  obtain ⟨hs, hrow, hinj⟩ := hG
  have hs1 : (M.set! p M[c]!).size = 24 := by rw [size_set, hs]
  have hget : ∀ s < 24, ((M.set! p M[c]!).set! c M[p]!)[s]! =
      if c = s then M[p]! else if p = s then M[c]! else M[s]! := fun s hs' => by
    rw [get_set hs1 hs', get_set hs hs']
  refine ⟨by rw [size_set, hs1], fun s hs' => ?_, fun v hv h => hinj v hv fun t ht => ?_⟩
  · rw [hget s hs']
    split
    · exact hrow p hp
    · split
      · exact hrow c hc
      · exact hrow s hs'
  · by_cases htp : t = p
    · subst htp
      have := h c hc
      rwa [hget c hc, ite_eq_left rfl] at this
    · by_cases htc : t = c
      · subst htc
        have := h p hp
        rwa [hget p hp, ite_eq_right htp, ite_eq_left rfl] at this
      · have := h t ht
        rwa [hget t ht, ite_eq_right (Ne.symm htc), ite_eq_right (Ne.symm htp)] at this

theorem pivot_spec (M : Array Nat) (c : Nat) :
    (pivotOf M c < 24 → c ≤ pivotOf M c ∧ M[pivotOf M c]!.testBit c = true) ∧
      (¬ pivotOf M c < 24 → ∀ r, c ≤ r → r < 24 → M[r]!.testBit c = false) := by
  have key : ∀ (L : List Nat) (q : Nat), (q = 24 ∨ (c ≤ q ∧ q < 24 ∧ M[q]!.testBit c = true)) →
      (∀ x ∈ L, c ≤ x ∧ x < 24) →
      ((L.foldl (fun p r => if (p == 24 && (M[r]!).testBit c) = true then r else p) q = 24 ∨
        (c ≤ L.foldl (fun p r => if (p == 24 && (M[r]!).testBit c) = true then r else p) q ∧
          L.foldl (fun p r => if (p == 24 && (M[r]!).testBit c) = true then r else p) q < 24 ∧
          M[L.foldl (fun p r => if (p == 24 && (M[r]!).testBit c) = true then r else p) q]!.testBit c =
            true)) ∧
        (L.foldl (fun p r => if (p == 24 && (M[r]!).testBit c) = true then r else p) q = 24 →
          q = 24 ∧ ∀ x ∈ L, M[x]!.testBit c = false)) := by
    intro L
    induction L with
    | nil => intro q hq _; exact ⟨hq, fun h => ⟨h, fun _ hx => absurd hx List.not_mem_nil⟩⟩
    | cons x L ih =>
      intro q hq hL
      rw [List.foldl_cons]
      have hx := hL x List.mem_cons_self
      have hL' : ∀ y ∈ L, c ≤ y ∧ y < 24 := fun y hy => hL y (List.mem_cons_of_mem _ hy)
      by_cases hb : (q == 24 && (M[x]!).testBit c) = true
      · rw [ite_eq_left hb]
        have hb' := Bool.and_eq_true_iff.1 hb
        obtain ⟨h1, h2⟩ := ih x (Or.inr ⟨hx.1, hx.2, hb'.2⟩) hL'
        refine ⟨h1, fun h => ?_⟩
        have := (h2 h).1
        omega
      · rw [ite_eq_right hb]
        obtain ⟨h1, h2⟩ := ih q hq hL'
        refine ⟨h1, fun h => ⟨(h2 h).1, fun y hy => ?_⟩⟩
        rcases List.mem_cons.1 hy with rfl | hy'
        · have hq24 := (h2 h).1
          subst hq24
          simpa using hb
        · exact (h2 h).2 y hy'
  have hL : ∀ x ∈ List.range' c (24 - c), c ≤ x ∧ x < 24 := fun x hx => by
    rw [List.mem_range'_1] at hx
    omega
  obtain ⟨h1, h2⟩ := key (List.range' c (24 - c)) 24 (Or.inl rfl) hL
  refine ⟨fun hp => ?_, fun hp r hr1 hr2 => ?_⟩
  · rcases h1 with h | h
    · rw [pivotOf] at hp
      omega
    · exact ⟨h.1, h.2.2⟩
  · have h24 : pivotOf M c = 24 := by
      rcases h1 with h | h
      · exact h
      · exact absurd h.2.1 hp
    exact (h2 h24).2 r (by rw [List.mem_range'_1]; omega)

theorem elim_spec {X : Array Nat} {c rp : Nat} (hc : c < 24) (hrc : rp.testBit c = true)
    (hrl : ∀ c' < c, rp.testBit c' = false) : ∀ n ≤ 24, ∀ M : Array Nat, Good X M → M[c]! = rp →
    Col M c → Good X ((List.range' 0 n).foldl (elimRow c rp) M) ∧
      ((List.range' 0 n).foldl (elimRow c rp) M)[c]! = rp ∧ Col ((List.range' 0 n).foldl (elimRow c rp) M) c ∧
      ∀ r < n, r ≠ c → ((List.range' 0 n).foldl (elimRow c rp) M)[r]!.testBit c = false := by
  intro n
  induction n with
  | zero => intro _ M hG hMc hC; exact ⟨hG, hMc, hC, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ n ih =>
    intro hn M hG hMc hC
    obtain ⟨hG1, hc1, hC1, hz1⟩ := ih (by omega) M hG hMc hC
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    generalize (List.range' 0 n).foldl (elimRow c rp) M = M1 at hG1 hc1 hC1 hz1
    have hs := hG1.1
    rw [elimRow]
    by_cases hb : (n != c && (M1[n]!).testBit c) = true
    · rw [ite_eq_left hb]
      have hb' := Bool.and_eq_true_iff.1 hb
      have hnc : n ≠ c := by simpa using hb'.1
      have hn24 : n < 24 := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := good_xor hG1 hn24 hc hnc
        rwa [hc1] at this
      · rw [get_set hs hc, ite_eq_right hnc, hc1]
      · intro c' hc' r hr
        rw [get_set hs hr]
        split
        · rename_i hnr
          subst hnr
          rw [Nat.testBit_xor, hC1 c' hc' n hr, hrl c' hc', Bool.xor_false]
        · exact hC1 c' hc' r hr
      · intro r hr hrc'
        by_cases hrn : r = n
        · subst hrn
          rw [get_set hs hn24, ite_eq_left rfl, Nat.testBit_xor, hb'.2, hrc]
          rfl
        · rw [get_set hs (by omega), ite_eq_right (Ne.symm hrn)]
          exact hz1 r (by omega) hrc'
    · rw [ite_eq_right hb]
      refine ⟨hG1, hc1, hC1, fun r hr hrc' => ?_⟩
      by_cases hrn : r = n
      · subst hrn
        simpa [hrc'] using hb
      · exact hz1 r (by omega) hrc'

theorem no_pivot_false {X M : Array Nat} (hXinj : ∀ u < 2 ^ 24, colv X u = 0 → u = 0)
    (hG : Good X M) {c : Nat} (hc : c < 24) (hC : Col M c)
    (hn : ∀ r, c ≤ r → r < 24 → M[r]!.testBit c = false) : False := by
  obtain ⟨hs, hrow, hinj⟩ := hG
  let g : Nat → Bool := fun k => decide (k = c) || (decide (k < c) && M[k]!.testBit c)
  let u : Nat := (List.range 24).foldl (fun acc k => if g k then acc ||| (1 <<< k) else acc) 0
  have hu : ∀ k, u.testBit k = (decide (k < 24) && g k) := fun k => testBit_ofBitsFold g k 24
  have hult : u < 2 ^ 24 :=
    Nat.lt_pow_two_of_testBit _ fun k hk => by rw [hu]; simp [Nat.not_lt.2 hk]
  have hdot : ∀ r < 24, dot (M[r]! >>> 24) (colv X u) = false := by
    intro r hr
    rw [← dot_vm, ← (hrow r hr).2, dot]
    rw [xs_congr (g := fun j => (decide (j = c) && M[r]!.testBit c) ^^
        (decide (j = r) && (decide (r < c) && M[r]!.testBit c))) 24 fun j hj => by
      rw [Nat.testBit_mod_two_pow, hu]
      simp only [hj, decide_true, Bool.true_and, g]
      by_cases hjc : j = c
      · subst hjc
        have : ¬ (j = r ∧ r < j) := by omega
        by_cases hjr : j = r
        · subst hjr
          simp
        · simp [hjr]
      · by_cases hjc' : j < c
        · rw [hC j hjc' r hr]
          by_cases hjr : j = r
          · subst hjr
            simp [hjc, hjc']
          · simp [hjc, Ne.symm hjr, hjr]
        · have hjr : ¬ (j = r ∧ r < c) := by omega
          simp only [hjc, hjc', decide_false, Bool.false_or, Bool.false_and, Bool.and_false,
            Bool.false_xor]
          by_cases hjr' : j = r
          · subst hjr'
            simp [hjc']
          · simp [hjr']]
    rw [xs_xor, xs_single, xs_single]
    by_cases hrc : r < c
    · simp [hc, hr, hrc]
    · rw [hn r (by omega) hr]
      simp
  have h0 := hXinj u hult (hinj _ (colv_lt X u) hdot)
  have := hu c
  rw [h0, Nat.zero_testBit] at this
  simp [hc, g] at this

theorem good_start {X : Array Nat} (hX : ∀ k, rw' X k < 2 ^ 24) : Good X (startOf X) := by
  have hs : (startOf X).size = 24 := by simp [startOf]
  have hget : ∀ r < 24, (startOf X)[r]! = rw' X r % 2 ^ 24 ||| (1 <<< (24 + r)) := fun r hr => by
    rw [getElem!_pos _ r (by rw [hs]; exact hr)]
    simp [startOf, rw']
  have hlo : ∀ r < 24, (startOf X)[r]! % 2 ^ 24 = rw' X r := fun r hr => by
    rw [hget r hr]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.one_shiftLeft,
      Nat.testBit_two_pow]
    by_cases hj : j < 24
    · simp [hj]
      omega
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hX r) (Nat.pow_le_pow_right (by omega) (by omega)))]
      simp [hj]
  have hhi : ∀ r < 24, (startOf X)[r]! >>> 24 = 1 <<< r := fun r hr => by
    rw [hget r hr]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.one_shiftLeft,
      Nat.testBit_two_pow, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp
  refine ⟨hs, fun r hr => ⟨?_, ?_⟩, fun v hv h => ?_⟩
  · rw [hget r hr]
    have h1 : rw' X r % 2 ^ 24 < 2 ^ 48 := by
      have := Nat.mod_lt (rw' X r) (Nat.two_pow_pos 24)
      omega
    have h2 : 1 <<< (24 + r) < 2 ^ 48 := by
      rw [Nat.one_shiftLeft]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    exact Nat.or_lt_two_pow h1 h2
  · rw [hlo r hr, hhi r hr, vm_one hr]
  · apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.zero_testBit]
    by_cases hk : k < 24
    · have := h k hk
      rwa [hhi k hk, dot_one hk] at this
    · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))

theorem col_zero (M : Array Nat) : Col M 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem step_spec {X : Array Nat} (hXinj : ∀ u < 2 ^ 24, colv X u = 0 → u = 0) {M : Array Nat}
    (hG : Good X M) {c : Nat} (hc : c < 24) (hC : Col M c) : Good X (stepCol M c) ∧ Col (stepCol M c) (c + 1) := by
  obtain ⟨hp1, hp2⟩ := pivot_spec M c
  rw [stepCol]
  by_cases hp : pivotOf M c < 24
  · simp only [hp, ↓reduceIte]
    obtain ⟨hcp, hbit⟩ := hp1 hp
    generalize pivotOf M c = p at hp hcp hbit
    have hs := hG.1
    have hs1 : (M.set! p M[c]!).size = 24 := by rw [size_set, hs]
    have hget : ∀ s < 24, ((M.set! p M[c]!).set! c M[p]!)[s]! =
        if c = s then M[p]! else if p = s then M[c]! else M[s]! := fun s hs' => by
      rw [get_set hs1 hs', get_set hs hs']
    have hrl : ∀ c' < c, M[p]!.testBit c' = false := fun c' hc' => by
      rw [hC c' hc' p hp]
      simp
      omega
    have hC1 : Col ((M.set! p M[c]!).set! c M[p]!) c := by
      intro c' hc' r hr
      rw [hget r hr]
      split
      · rename_i hcr
        subst hcr
        rw [hrl c' hc']
        simp
        omega
      · split
        · rename_i _ hpr
          subst hpr
          rw [hC c' hc' c hc]
          simp
          omega
        · exact hC c' hc' r hr
    obtain ⟨hG2, hc2, hC2, hz2⟩ := elim_spec hc hbit hrl 24 le_rfl _ (good_swap hG hp hc)
      (by rw [hget c hc]; simp only [↓reduceIte]) hC1
    refine ⟨hG2, fun c' hc' r hr => ?_⟩
    by_cases hcc : c' = c
    · subst hcc
      by_cases hrc : r = c'
      · subst hrc
        rw [hc2, hbit]
        simp
      · rw [hz2 r hr hrc]
        simp [hrc]
    · exact hC2 c' (by omega) r hr
  · exact (no_pivot_false hXinj hG hc hC (hp2 hp)).elim

theorem fold_spec {X : Array Nat} (hX : ∀ k, rw' X k < 2 ^ 24)
    (hXinj : ∀ u < 2 ^ 24, colv X u = 0 → u = 0) : ∀ n ≤ 24,
    Good X ((List.range' 0 n).foldl stepCol (startOf X)) ∧
      Col ((List.range' 0 n).foldl stepCol (startOf X)) n := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨good_start hX, col_zero _⟩
  | succ n ih =>
    intro hn
    obtain ⟨hG, hC⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    exact step_spec hXinj hG (by omega) hC

theorem rw'_id {k : Nat} (hk : k < 24) : rw' (idRows 24) k = 1 <<< k := by simp [rw', idRows, hk]

theorem colv_inj {X Y : Array Nat} (hXY : mulRows 24 X Y = idRows 24) :
    ∀ u < 2 ^ 24, colv X u = 0 → u = 0 := by
  have hsurj : ∀ v < 2 ^ 24, colv X (colv Y v) = v := by
    intro v hv
    apply Nat.eq_of_testBit_eq
    intro k
    rw [testBit_colv]
    by_cases hk : k < 24
    · rw [← dot_vm, ← map_rw' X _ (vm_zero Y), ← mulRows, hXY, rw'_id hk, dot_one hk]
      simp [hk]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))]
      simp [hk]
  let f : Fin (2 ^ 24) → Fin (2 ^ 24) := fun u => ⟨colv X u.val, colv_lt X u.val⟩
  have hf : Function.Surjective f := fun v => ⟨⟨colv Y v.val, colv_lt Y v.val⟩, Fin.ext (hsurj v.val v.isLt)⟩
  have hinj := Finite.injective_iff_surjective.2 hf
  have h0 : colv X 0 = 0 := Nat.eq_of_testBit_eq fun k => by
    rw [testBit_colv, Nat.zero_testBit, dot]
    rw [xs_congr 24 fun j _ => by rw [Nat.zero_testBit, Bool.and_false], xs_false]
    simp
  intro u hu hzero
  have := @hinj ⟨u, hu⟩ ⟨0, Nat.two_pow_pos 24⟩ (Fin.ext (by simp [f, hzero, h0]))
  exact congrArg Fin.val this

theorem inv_rows {X Y : Array Nat} (hX : ∀ k, rw' X k < 2 ^ 24) (hYs : Y.size = 24)
    (hXY : mulRows 24 X Y = idRows 24) : CFSG.Sporadic.Co1Schreier.Native.inv X = Y := by
  rw [inv_eq_model]
  obtain ⟨⟨hs, hrow, _⟩, hC⟩ := fold_spec hX (colv_inj hXY) 24 le_rfl
  generalize (List.range' 0 24).foldl stepCol (startOf X) = M at hs hrow hC
  apply Array.ext
  · rw [Array.size_map, hs, hYs]
  · intro r h1 h2
    have hr : r < 24 := by rw [hYs] at h2; exact h2
    rw [Array.getElem_map]
    have hM : M[r] = M[r]! := (getElem!_pos M r (by omega)).symm
    have hYr : Y[r] = rw' Y r := by simp [rw', h2]
    rw [hM, hYr]
    obtain ⟨hb, hl⟩ := hrow r hr
    have hlo : M[r]! % 2 ^ 24 = 1 <<< r := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_mod_two_pow, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hj : j < 24
      · rw [hC j hj r hr]
        simp [hj]
      · simp [hj]
        omega
    have ha : M[r]! >>> 24 < 2 ^ 24 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hb)
    rw [hlo] at hl
    rw [← vm_id ha, ← hXY, ← vm_assoc, ← hl, vm_one hr]

theorem unpackR_idF : unpackR 24 (idF 24) = idRows 24 := by
  have hI : idF 24 = orN 24 fun i => pw2 i <<< (24 * i) := rfl
  rw [idRows, unpackR]
  congr 1
  funext i
  have hlt : ∀ i < 24, pw2 i < 2 ^ 24 := fun i hi => by
    change 1 <<< i < 2 ^ 24
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by omega) hi
  rw [← rowF_eq, hI, rowF_orN 24 hlt i.isLt]
  rfl

theorem rw'_unpackR_lt (A k : Nat) : rw' (unpackR 24 A) k < 2 ^ 24 := by
  by_cases hk : k < 24
  · simp only [rw', unpackR, Array.getElem?_ofFn, hk, ↓reduceDIte, Option.getD_some]
    exact Nat.mod_lt _ (Nat.two_pow_pos 24)
  · simp [rw', unpackR, hk]

theorem inv_unpackR {A AI : Nat} (h : mulF 24 A AI = idF 24) :
    CFSG.Sporadic.Co1Schreier.Native.inv (unpackR 24 A) = unpackR 24 AI :=
  inv_rows (rw'_unpackR_lt A) (by simp [unpackR]) (by rw [mulRows_unpackR, h, unpackR_idF])

end CFSG.KC.F2W

end
