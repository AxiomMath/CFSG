module

public import Certificates.Data.Kernel.M24L2.Bfs
public import CFSG.Certificates.Kernel.M24L2.CodeSound

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native

variable {α : Type}

@[expose] def innerS (key : Table → Nat) (lt : α → Table) (X : Table) (w : List α)
    (st : Array (Option (List α)) × Array (Table × List α)) (l : α) :
    Array (Option (List α)) × Array (Table × List α) :=
  if (st.1[key (compT 16 X (lt l))]!).isNone = true then
    (st.1.set! (key (compT 16 X (lt l))) (some (w ++ [l])), st.2.push (compT 16 X (lt l), w ++ [l]))
  else st

@[expose] def outerS (key : Table → Nat) (lets : List α) (lt : α → Table)
    (s : Array (Option (List α)) × Array (Table × List α) × Nat) :
    Array (Option (List α)) × Array (Table × List α) × Nat :=
  if s.2.2 < s.2.1.size then
    let st := lets.foldl (innerS key lt s.2.1[s.2.2]!.1 s.2.1[s.2.2]!.2) (s.1, s.2.1)
    (st.1, st.2, s.2.2 + 1)
  else s

theorem forIn_id_eq_foldl {β γ : Type} (l : List γ) (init : β) (f : γ → β → Id (ForInStep β))
    (g : β → γ → β) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    (forIn l init f : Id β) = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, h, List.foldl_cons, ← ih]
    rfl

theorem bfsG_eq (N F : Nat) (key : Table → Nat) (lets : List α) (lt : α → Table) (X0 : Table) :
    bfsG N F key lets lt X0 =
      (let s := (List.range' 0 F).foldl (fun s _ => outerS key lets lt s)
          ((Array.replicate N none).set! (key X0) (some []), #[(X0, [])], 0)
       (s.1, s.2.1)) := by
  unfold bfsG
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [forIn_id_eq_foldl _ _ _ (fun s _ => outerS key lets lt s)]
  · simp [Std.Legacy.Range.size]
    rfl
  · intro a b
    unfold outerS
    split
    · rw [forIn_id_eq_foldl _ _ _ (innerS key lt _ _)]
      · rfl
      · intro l st
        unfold innerS
        split <;> rfl
    · rfl

theorem letN_eq {β : Sort _} (y : Nat) (k : Nat → β) : letN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def entT (e : Nat × List α) : Table × List α := (tabC e.1, e.2)

@[expose] def look (keyN : Nat → Nat) (k : Nat) (L : List (Nat × List α)) : Option (List α) :=
  (L.find? fun e => keyN e.1 == k).map Prod.snd

@[expose] def Good (lc : α → Nat) (lets : List α) (c0 : Nat) (e : Nat × List α) : Prop :=
  e.1 < 2 ^ 20 ∧ e.1 = e.2.foldl (fun c l => mulC c (lc l)) c0 ∧ ∀ l ∈ e.2, l ∈ lets

structure Rel (N : Nat) (keyN : Nat → Nat) (lc : α → Nat) (lets : List α) (c0 : Nat)
    (s : Array (Option (List α)) × Array (Table × List α) × Nat) (t : BS α) : Prop where
  q : s.2.1.toList = t.all.reverse.map entT
  d : s.2.1.toList.drop s.2.2 = (t.front ++ t.back.reverse).map entT
  le : s.2.2 ≤ s.2.1.size
  sz : s.1.size = N
  lk : ∀ k < N, s.1[k]! = look keyN k t.all.reverse
  mb : ∀ k, t.mask.testBit (k + 64) = t.all.any fun e => keyN e.1 == k
  gd : ∀ e ∈ t.all, Good lc lets c0 e
  fr : ∀ e ∈ t.front, e ∈ t.all
  bk : ∀ e ∈ t.back, e ∈ t.all

theorem land_pow_beq (x j : Nat) :
    Nat.beq (Nat.land x (Nat.shiftLeft 1 j)) 0 = !x.testBit j := by
  change (x &&& 1 <<< j == 0) = _
  rw [Nat.one_shiftLeft]
  rcases hb : x.testBit j with _ | _
  · simp only [Bool.not_false, beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases h : j = i
    · subst h
      simp [hb]
    · simp [h]
  · simp only [Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro h0
    have := congrArg (fun z => z.testBit j) h0
    simp [Nat.testBit_and, Nat.testBit_two_pow, hb] at this

theorem testBit_addKey (M m k : Nat) :
    (addKey M m).testBit (k + 64) = (M.testBit (k + 64) || k == m) := by
  unfold addKey
  have hs : ∀ s : Nat, s < 2 ^ 64 → s.testBit (k + 64) = false := fun s hs =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h1 : Nat.land M 18446744073709551615 < 2 ^ 64 := by
    change M &&& (2 ^ 64 - 1) < 2 ^ 64
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  have h2 : saltN (Nat.land M 18446744073709551615) < 2 ^ 64 := by
    unfold saltN
    change _ &&& (2 ^ 64 - 1) < 2 ^ 64
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  change ((M ||| 1 <<< (m + 64)) ^^^ (Nat.land M 18446744073709551615 ^^^
    saltN (Nat.land M 18446744073709551615))).testBit (k + 64) = _
  rw [Nat.testBit_xor, hs _ (Nat.xor_lt_two_pow h1 h2), Bool.xor_false, Nat.testBit_or,
    Nat.one_shiftLeft, Nat.testBit_two_pow]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Nat.add_right_cancel_iff, eq_comm]

theorem look_isNone (keyN : Nat → Nat) (k : Nat) (L : List (Nat × List α)) :
    (look keyN k L).isNone = !(L.any fun e => keyN e.1 == k) := by
  unfold look
  cases h : L.find? (fun e => keyN e.1 == k) with
  | none =>
    rw [List.find?_eq_none] at h
    simp only [Option.map_none, Option.isNone_none]
    symm
    rw [Bool.not_eq_true', List.any_eq_false]
    intro x hx
    simpa using h x hx
  | some e =>
    have := List.find?_some h
    have hm := List.mem_of_find?_eq_some h
    simp only [Option.map_some, Option.isNone_some]
    symm
    rw [Bool.not_eq_false', List.any_eq_true]
    exact ⟨e, hm, this⟩

theorem look_snoc_self (keyN : Nat → Nat) (L : List (Nat × List α)) (e : Nat × List α)
    (h : (L.any fun x => keyN x.1 == keyN e.1) = false) :
    look keyN (keyN e.1) (L ++ [e]) = some e.2 := by
  unfold look
  have h1 : L.find? (fun x => keyN x.1 == keyN e.1) = none := by
    rw [List.find?_eq_none]
    intro x hx
    rw [List.any_eq_false] at h
    simpa using h x hx
  rw [List.find?_append, h1]
  simp

theorem look_snoc_ne (keyN : Nat → Nat) {k : Nat} (L : List (Nat × List α)) (e : Nat × List α)
    (h : keyN e.1 ≠ k) : look keyN k (L ++ [e]) = look keyN k L := by
  unfold look
  rw [List.find?_append]
  have h1 : [e].find? (fun x => keyN x.1 == k) = none := by simp [h]
  rw [h1, Option.or_none]

section Sim

variable {N : Nat} {key : Table → Nat} {keyN : Nat → Nat} {lets : List α} {lt : α → Table}
  {lc : α → Nat} {c0 : Nat}

theorem rel_inner (hlt : ∀ l, lt l = tabC (lc l)) (hkey : ∀ c < 2 ^ 20, key (tabC c) = keyN c)
    (hN : ∀ c < 2 ^ 20, keyN c < N) {arr : Array (Option (List α))} {queue : Array (Table × List α)}
    {j : Nat} {t : BS α} {x : Nat} {w : List α} {l : α}
    (hr : Rel N keyN lc lets c0 (arr, queue, j) t) (hx : Good lc lets c0 (x, w)) (hl : l ∈ lets) :
    Rel N keyN lc lets c0 ((innerS key lt (tabC x) w (arr, queue) l).1,
      (innerS key lt (tabC x) w (arr, queue) l).2, j) (innerK keyN lc x w t l) := by
  have hy := mulC_lt x (lc l)
  have hm := hN _ hy
  unfold innerS innerK
  simp only [letN_eq, hlt l, compT_tabC, hkey _ hy, land_pow_beq]
  have hc : (arr[keyN (mulC x (lc l))]!).isNone =
      !t.mask.testBit (Nat.add (keyN (mulC x (lc l))) 64) := by
    rw [hr.lk _ hm, look_isNone]
    change _ = !t.mask.testBit (keyN (mulC x (lc l)) + 64)
    rw [hr.mb, List.any_reverse]
  rcases hb : t.mask.testBit (Nat.add (keyN (mulC x (lc l))) 64) with _ | _
  · rw [hb] at hc
    simp only [hc, hb, ↓reduceIte, Bool.not_false]
    change t.mask.testBit (keyN (mulC x (lc l)) + 64) = false at hb
    generalize hyv : mulC x (lc l) = y at hy hm hb
    have hany : (t.all.reverse.any fun e => keyN e.1 == keyN y) = false := by
      rw [List.any_reverse, ← hr.mb]
      exact hb
    change Rel N keyN lc lets c0 (arr.set! (keyN y) (some (w ++ [l])),
      queue.push (tabC y, w ++ [l]), j)
      (BS.mk t.front ((y, w ++ [l]) :: t.back) ((y, w ++ [l]) :: t.all) (addKey t.mask (keyN y)))
    have hq : queue.toList = t.all.reverse.map entT := hr.q
    have hd : queue.toList.drop j = (t.front ++ t.back.reverse).map entT := hr.d
    have hle : j ≤ queue.size := hr.le
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Array.toList_push, hq, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil]
      rfl
    · simp only [Array.toList_push]
      rw [List.drop_append_of_le_length (by simpa using hle), hd]
      simp only [List.reverse_cons, List.map_append, List.append_assoc, List.map_cons,
        List.map_nil]
      rfl
    · simp only [Array.size_push]
      have := hr.le
      simp only at this
      omega
    · simp only [Array.size_set!]
      exact hr.sz
    · intro k hk
      by_cases hkm : k = keyN y
      · subst hkm
        rw [Array.getElem!_set!_self _ _ _ (by rw [hr.sz]; exact hm), List.reverse_cons]
        exact (look_snoc_self keyN t.all.reverse (y, w ++ [l]) hany).symm
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkm), hr.lk k hk, List.reverse_cons,
          look_snoc_ne keyN _ (y, w ++ [l]) (Ne.symm hkm)]
    · intro k
      change (addKey t.mask (keyN y)).testBit (k + 64) = _
      rw [testBit_addKey, hr.mb k, List.any_cons, Bool.or_comm]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, eq_comm]
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · refine ⟨hy, ?_, ?_⟩
        · rw [List.foldl_append, ← hx.2.1, ← hyv]
          rfl
        · intro l' hl'
          rcases List.mem_append.1 hl' with h | h
          · exact hx.2.2 _ h
          · rw [List.mem_singleton] at h
            rw [h]
            exact hl
      · exact hr.gd e he
    · intro e he
      exact List.mem_cons_of_mem _ (hr.fr e he)
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hr.bk e he)
  · rw [hb] at hc
    simp only [hc, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact hr

theorem rel_fold (hlt : ∀ l, lt l = tabC (lc l)) (hkey : ∀ c < 2 ^ 20, key (tabC c) = keyN c)
    (hN : ∀ c < 2 ^ 20, keyN c < N) {x : Nat} {w : List α} (hx : Good lc lets c0 (x, w))
    {j : Nat} : ∀ (L : List α), (∀ l ∈ L, l ∈ lets) →
      ∀ (st : Array (Option (List α)) × Array (Table × List α)) (t : BS α),
      Rel N keyN lc lets c0 (st.1, st.2, j) t →
      Rel N keyN lc lets c0 ((L.foldl (innerS key lt (tabC x) w) st).1,
        (L.foldl (innerS key lt (tabC x) w) st).2, j) (L.foldl (innerK keyN lc x w) t)
  | [], _, _, _, hr => hr
  | l :: L, hL, st, t, hr => by
    rw [List.foldl_cons, List.foldl_cons]
    exact rel_fold hlt hkey hN hx L (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')) _ _
      (rel_inner hlt hkey hN hr hx (hL l List.mem_cons_self))

theorem rel_outer (hlt : ∀ l, lt l = tabC (lc l)) (hkey : ∀ c < 2 ^ 20, key (tabC c) = keyN c)
    (hN : ∀ c < 2 ^ 20, keyN c < N) {s : Array (Option (List α)) × Array (Table × List α) × Nat}
    {t : BS α} (hr : Rel N keyN lc lets c0 s t) :
    Rel N keyN lc lets c0 (outerS key lets lt s) (outerK keyN lc lets t) := by
  obtain ⟨arr, queue, i⟩ := s
  obtain ⟨front, back, all, mask⟩ := t
  have hd := hr.d
  simp only at hd
  unfold outerS outerK
  simp only
  by_cases hi : i < queue.size
  · rw [if_pos hi]
    have hlen : i < queue.toList.length := by simpa using hi
    rw [List.drop_eq_getElem_cons hlen] at hd
    have hqi : queue[i]! = queue.toList[i] := by
      rw [getElem!_pos queue i hi]
      rfl
    rcases front with _ | ⟨e, f⟩
    · rcases hbr : back.reverse with _ | ⟨e, f⟩
      · rw [hbr] at hd
        simp at hd
      · rw [hbr] at hd
        simp only [List.nil_append, List.map_cons, List.cons.injEq] at hd
        simp only
        rw [hqi, hd.1]
        have he : e ∈ all := hr.bk e (by rw [← List.mem_reverse, hbr]; exact List.mem_cons_self)
        refine rel_fold hlt hkey hN (hr.gd e he) lets (fun l hl => hl) (arr, queue) _ ?_
        refine ⟨hr.q, ?_, ?_, hr.sz, hr.lk, hr.mb, hr.gd, ?_, ?_⟩
        · simpa using hd.2
        · simpa using hi
        · intro e' he'
          exact hr.bk e' (by rw [← List.mem_reverse, hbr]; exact List.mem_cons_of_mem _ he')
        · intro e' he'
          simp at he'
    · simp only [List.cons_append, List.map_cons, List.cons.injEq] at hd
      simp only
      rw [hqi, hd.1]
      have he : e ∈ all := hr.fr e List.mem_cons_self
      refine rel_fold hlt hkey hN (hr.gd e he) lets (fun l hl => hl) (arr, queue) _ ?_
      refine ⟨hr.q, ?_, ?_, hr.sz, hr.lk, hr.mb, hr.gd, ?_, hr.bk⟩
      · simpa using hd.2
      · simpa using hi
      · intro e' he'
        exact hr.fr e' (List.mem_cons_of_mem _ he')
  · rw [if_neg hi]
    have hnil : queue.toList.drop i = [] :=
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hi)
    rw [hnil] at hd
    have h1 : front = [] := by
      rcases front with _ | ⟨e, f⟩
      · rfl
      · simp at hd
    have h2 : back = [] := by
      subst h1
      rcases back with _ | ⟨e, f⟩
      · rfl
      · simp at hd
    subst h1 h2
    exact hr

theorem rel_loop (hlt : ∀ l, lt l = tabC (lc l)) (hkey : ∀ c < 2 ^ 20, key (tabC c) = keyN c)
    (hN : ∀ c < 2 ^ 20, keyN c < N) : ∀ (n a : Nat)
    (s : Array (Option (List α)) × Array (Table × List α) × Nat) (t : BS α),
    Rel N keyN lc lets c0 s t →
      Rel N keyN lc lets c0 ((List.range' a n).foldl (fun s _ => outerS key lets lt s) s)
        (loopK keyN lc lets n t)
  | 0, _, _, _, hr => hr
  | n + 1, a, s, t, hr => by
    rw [List.range'_succ, List.foldl_cons]
    have e : loopK keyN lc lets (n + 1) t = loopK keyN lc lets n (outerK keyN lc lets t) := by
      change letN (Nat.land (outerK keyN lc lets t).mask 1)
        (fun _ => loopK keyN lc lets n (outerK keyN lc lets t)) = _
      rw [letN_eq]
    rw [e]
    exact rel_loop hlt hkey hN n (a + 1) _ _ (rel_outer hlt hkey hN hr)

theorem bfsG_twin (F : Nat) (hlt : ∀ l, lt l = tabC (lc l))
    (hkey : ∀ c < 2 ^ 20, key (tabC c) = keyN c) (hN : ∀ c < 2 ^ 20, keyN c < N)
    (h0 : c0 < 2 ^ 20) :
    (bfsG N F key lets lt (tabC c0)).2.toList = (bfsT F keyN lc lets c0).all.reverse.map entT ∧
    (bfsG N F key lets lt (tabC c0)).1.size = N ∧
    (∀ k < N, (bfsG N F key lets lt (tabC c0)).1[k]! =
      look keyN k (bfsT F keyN lc lets c0).all.reverse) ∧
    (∀ k, (bfsT F keyN lc lets c0).mask.testBit (k + 64) =
      (bfsT F keyN lc lets c0).all.any fun e => keyN e.1 == k) ∧
    ∀ e ∈ (bfsT F keyN lc lets c0).all, Good lc lets c0 e := by
  have hm0 := hN c0 h0
  have h00 : Rel N keyN lc lets c0
      ((Array.replicate N none).set! (key (tabC c0)) (some []), #[(tabC c0, [])], 0)
      (BS.mk [(c0, [])] [] [(c0, [])] (Nat.shiftLeft 1 (Nat.add (keyN c0) 64))) := by
    rw [hkey c0 h0]
    refine ⟨rfl, rfl, by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      by_cases hkm : k = keyN c0
      · subst hkm
        rw [Array.getElem!_set!_self _ _ _ (by simpa using hm0)]
        simp [look]
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hkm)]
        have : (Array.replicate N (none : Option (List α)))[k]! = none := by
          rw [getElem!_pos _ k (by simpa using hk), Array.getElem_replicate]
        rw [this]
        simp [look, Ne.symm hkm]
    · intro k
      change (1 <<< (keyN c0 + 64)).testBit (k + 64) = _
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Nat.add_right_cancel_iff, eq_comm]
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨h0, rfl, fun l hl => by simp at hl⟩
    · intro e he
      exact he
    · intro e he
      simp at he
  have hr := rel_loop hlt hkey hN F 0 _ _ h00
  rw [bfsG_eq]
  exact ⟨hr.q, hr.sz, hr.lk, hr.mb, hr.gd⟩

end Sim

end CFSG.KC.M24L2
