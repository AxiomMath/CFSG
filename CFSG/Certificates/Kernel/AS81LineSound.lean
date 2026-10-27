module

public import CFSG.Certificates.Kernel.MergeGSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3LineTests
public import Certificates.Data.Kernel.AS81Line

public section

namespace CFSG.KC.AS81

open CFSG.ComponentClassification.AS81.MinusLines CFSG.Sporadic.Co1Block.Native
open CFSG.KC.MergeR CFSG.KC.MergeG

theorem forIn_root (par : Array Nat) :
    ∀ (l : List Nat) (r : Nat),
      (forIn (m := Id) l r fun _ r => if (par[r]! == r) = true then pure (ForInStep.done r)
        else pure (ForInStep.yield par[r]!)).run = ufFind par l.length r
  | [], r => rfl
  | a :: l, r => by
    rw [List.forIn_cons, List.length_cons, ufFind]
    by_cases h : (par[r]! == r) = true
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      exact forIn_root par l _

theorem lineRoot_eq (par : Array Nat) (x : Nat) : lineRoot par x = ufFind par par.size x := by
  unfold lineRoot
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, bind_pure]
  have h := forIn_root par (List.range' 0 par.size) x
  rw [List.length_range'] at h
  exact h

theorem ufFind_id {n b : Nat} (hb : b < n) :
    ufFind (Array.ofFn (n := n) fun i => i.val) n b = b := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [ufFind, getElem!_pos _ b (by simpa using hb), Array.getElem_ofFn]
  simp

@[expose] def innerL (G : Array (Array Nat)) (u v : Nat) (s : St) (i : Nat) : St :=
  if (lineRoot s.1 (G[i]!)[u]! != lineRoot s.1 (G[i]!)[v]!) = true then
    if s.2.1[lineRoot s.1 (G[i]!)[u]!]! < s.2.1[lineRoot s.1 (G[i]!)[v]!]! then
      (s.1.set! (lineRoot s.1 (G[i]!)[u]!) (lineRoot s.1 (G[i]!)[v]!),
        s.2.1.set! (lineRoot s.1 (G[i]!)[v]!)
          (s.2.1[lineRoot s.1 (G[i]!)[v]!]! + s.2.1[lineRoot s.1 (G[i]!)[u]!]!),
        s.2.2.1.push ((G[i]!)[u]!, (G[i]!)[v]!), s.2.2.2.push (i, u, v))
    else
      (s.1.set! (lineRoot s.1 (G[i]!)[v]!) (lineRoot s.1 (G[i]!)[u]!),
        s.2.1.set! (lineRoot s.1 (G[i]!)[u]!)
          (s.2.1[lineRoot s.1 (G[i]!)[u]!]! + s.2.1[lineRoot s.1 (G[i]!)[v]!]!),
        s.2.2.1.push ((G[i]!)[u]!, (G[i]!)[v]!), s.2.2.2.push (i, u, v))
  else s

theorem innerL_eq {n : Nat} {G : Array (Array Nat)} {u v : Nat} {s : St} (hs : s.1.size = n)
    (i : Nat) : innerL G u v s i = innerA n G u v s i := by
  unfold innerL innerA
  rw [lineRoot_eq, lineRoot_eq, hs, Nat.add_comm (s.2.1[ufFind s.1 n (G[i]!)[v]!]!)]

theorem innerA_size {n : Nat} {G : Array (Array Nat)} {u v : Nat} (s : St) (i : Nat) :
    (innerA n G u v s i).1.size = s.1.size := by
  unfold innerA
  split_ifs <;> simp

theorem foldl_innerL {n : Nat} {G : Array (Array Nat)} {u v : Nat} :
    ∀ (l : List Nat) (s : St), s.1.size = n →
      l.foldl (innerL G u v) s = l.foldl (innerA n G u v) s ∧
        (l.foldl (innerA n G u v) s).1.size = n
  | [], s, hs => ⟨rfl, hs⟩
  | i :: l, s, hs => by
    rw [List.foldl_cons, List.foldl_cons, innerL_eq hs]
    exact foldl_innerL l _ (by rw [innerA_size, hs])

@[expose] def outerL (G : Array (Array Nat))
    (T : Array Nat × Array Nat × Array (Nat × Nat) × Array (Nat × Nat × Nat) × Nat) (_ : Nat) :
    Array Nat × Array Nat × Array (Nat × Nat) × Array (Nat × Nat × Nat) × Nat :=
  if T.2.2.2.2 < T.2.2.1.size then
    let r := (List.range G.size).foldl (innerL G (T.2.2.1[T.2.2.2.2]!).1 (T.2.2.1[T.2.2.2.2]!).2)
      (T.1, T.2.1, T.2.2.1, T.2.2.2.1)
    (r.1, r.2.1, r.2.2.1, r.2.2.2, T.2.2.2.2 + 1)
  else T

@[expose] def proj (T : Array Nat × Array Nat × Array (Nat × Nat) × Array (Nat × Nat × Nat) × Nat) :
    St := (T.1, T.2.1, T.2.2.1, T.2.2.2.1)

theorem step_size {n : Nat} {G : Array (Array Nat)} {st : St} (hs : st.1.size = n) (h : Nat) :
    (mergeSearchStep n G st h).1.size = n := by
  rw [step_eq]
  split_ifs
  · exact (foldl_innerL (G := G) _ st hs).2
  · exact hs

theorem innerA_qsize {n : Nat} {G : Array (Array Nat)} {u v : Nat} (s : St) (i : Nat) :
    s.2.2.1.size ≤ (innerA n G u v s i).2.2.1.size := by
  unfold innerA
  split_ifs <;> simp

theorem foldl_qsize {n : Nat} {G : Array (Array Nat)} {u v : Nat} :
    ∀ (l : List Nat) (s : St), s.2.2.1.size ≤ (l.foldl (innerA n G u v) s).2.2.1.size
  | [], _ => le_rfl
  | i :: l, s => le_trans (innerA_qsize s i) (foldl_qsize l _)

theorem outer_inv {n : Nat} {G : Array (Array Nat)} {S0 : St} (h0 : S0.1.size = n)
    (hq0 : 0 < S0.2.2.1.size) :
    ∀ j : Nat, ∀ T, (proj T = S0 ∧ T.2.2.2.2 = 0) →
      proj ((List.range j).foldl (outerL G) T) =
          (List.range j).foldl (mergeSearchStep n G) S0 ∧
        ((List.range j).foldl (mergeSearchStep n G) S0).1.size = n ∧
        ((List.range j).foldl (outerL G) T).2.2.2.2 ≤
          ((List.range j).foldl (mergeSearchStep n G) S0).2.2.1.size ∧
        ((List.range j).foldl (outerL G) T).2.2.2.2 ≤ j ∧
        (((List.range j).foldl (outerL G) T).2.2.2.2 = j ∨
          ((List.range j).foldl (outerL G) T).2.2.2.2 =
            ((List.range j).foldl (mergeSearchStep n G) S0).2.2.1.size)
  | 0, T, ⟨hp, hh⟩ => by
    simp only [List.range_zero, List.foldl_nil]
    exact ⟨hp, h0, by rw [hh]; exact Nat.zero_le _, by rw [hh], Or.inl hh⟩
  | j + 1, T, hT => by
    obtain ⟨hp, hsz, hle, hlj, hh⟩ := outer_inv h0 hq0 j T hT
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize (List.range j).foldl (outerL G) T = U at hp hle hlj hh
    generalize (List.range j).foldl (mergeSearchStep n G) S0 = s at hp hsz hle hh
    subst hp
    obtain ⟨p, z, q, o, hd⟩ := U
    change p.size = n at hsz
    change hd ≤ q.size at hle
    change hd ≤ j at hlj
    change hd = j ∨ hd = q.size at hh
    have hpj : proj (p, z, q, o, hd) = (p, z, q, o) := rfl
    rw [hpj]
    have hstep : mergeSearchStep n G (p, z, q, o) j =
        if j < q.size then
          (List.range G.size).foldl (innerA n G (q[j]!).1 (q[j]!).2) (p, z, q, o)
        else (p, z, q, o) := step_eq n G (p, z, q, o) j
    by_cases hq : hd < q.size
    · have hj : hd = j := by omega
      subst hj
      have e := foldl_innerL (n := n) (G := G) (u := (q[hd]!).1) (v := (q[hd]!).2)
        (List.range G.size) (p, z, q, o) hsz
      have hq' := foldl_qsize (n := n) (G := G) (u := (q[hd]!).1) (v := (q[hd]!).2)
        (List.range G.size) (p, z, q, o)
      have hout : outerL G (p, z, q, o, hd) hd =
          (((List.range G.size).foldl (innerL G (q[hd]!).1 (q[hd]!).2) (p, z, q, o)).1,
            ((List.range G.size).foldl (innerL G (q[hd]!).1 (q[hd]!).2) (p, z, q, o)).2.1,
            ((List.range G.size).foldl (innerL G (q[hd]!).1 (q[hd]!).2) (p, z, q, o)).2.2.1,
            ((List.range G.size).foldl (innerL G (q[hd]!).1 (q[hd]!).2) (p, z, q, o)).2.2.2,
            hd + 1) := by
        unfold outerL
        rw [if_pos hq]
      rw [hstep, if_pos hq, hout, e.1]
      change (_ = _) ∧ _ ∧ hd + 1 ≤ _ ∧ hd + 1 ≤ hd + 1 ∧ (hd + 1 = hd + 1 ∨ _)
      refine ⟨rfl, e.2, ?_, le_rfl, Or.inl rfl⟩
      change q.size ≤ _ at hq'
      omega
    · have hout : outerL G (p, z, q, o, hd) j = (p, z, q, o, hd) := by
        unfold outerL
        rw [if_neg hq]
      have hjq : ¬ j < q.size := by omega
      rw [hstep, if_neg hjq, hout]
      change (_ = _) ∧ p.size = n ∧ hd ≤ q.size ∧ hd ≤ j + 1 ∧ (hd = j + 1 ∨ hd = q.size)
      exact ⟨rfl, hsz, hle, by omega, Or.inr (by omega)⟩

theorem proj_init {n b x : Nat} (hb : b < n) (hx : x < n) :
    proj ((Array.ofFn (n := n) fun i => i.val).set! x b,
      (Array.replicate n 1).set! b ((Array.replicate n 1)[b]! + (Array.replicate n 1)[x]!),
      (#[] : Array (Nat × Nat)).push (b, x), (#[] : Array (Nat × Nat × Nat)), 0) = initSt n b x := by
  unfold proj initSt
  rw [getElem!_pos _ b (by simpa using hb), getElem!_pos _ x (by simpa using hx)]
  simp

theorem lineMergeSearch_eq {n : Nat} {G : Array (Array Nat)} {b x : Nat} (hb : b < n)
    (hx : x < n) (hbx : b ≠ x) :
    lineMergeSearch n G b x =
      ((List.range (2 * n)).foldl (mergeSearchStep n G) (initSt n b x)).2.2.2.toList := by
  unfold lineMergeSearch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [lineRoot_eq, lineRoot_eq, Array.size_ofFn, ufFind_id hb, ufFind_id hx]
  have hne : (b != x) = true := by simpa using hbx
  simp only [hne, if_true]
  rw [forIn_yield (List.range' 0 (2 * n) 1) _ _ (outerL G)]
  · have h0 := proj_init (n := n) hb hx
    have hs0 : (initSt n b x).1.size = n := by simp [initSt]
    have hq0 : 0 < (initSt n b x).2.2.1.size := by simp [initSt]
    obtain ⟨hp, -⟩ := outer_inv (G := G) hs0 hq0 (2 * n) _ ⟨h0, rfl⟩
    rw [← List.range_eq_range']
    simp only [Id.run, pure_bind]
    rw [← hp]
    rfl
  · intro a T
    obtain ⟨p, z, q, o, hd⟩ := T
    simp only [outerL]
    by_cases hq : hd < q.size
    · rw [if_pos hq, if_pos hq]
      rw [forIn_yield (List.range' 0 G.size 1) _ _ (innerL G (q[hd]!).1 (q[hd]!).2)]
      · rw [← List.range_eq_range']
        rfl
      · intro i s
        obtain ⟨p', z', q', o'⟩ := s
        simp only [innerL]
        split_ifs <;> rfl
    · rw [if_neg hq, if_neg hq]

@[expose] def keys (s : Nat × Nat × Nat) : List Nat :=
  [120 * s.1 + s.2.1, 120 * s.2.1 + s.1, 120 * s.1 + s.2.2, 120 * s.2.2 + s.1,
    120 * s.2.1 + s.2.2, 120 * s.2.2 + s.2.1]

theorem foldl_set_get (t : Nat) :
    ∀ (l : List Nat) (T : Array Nat), (∀ a ∈ l, a < T.size) →
      (l.foldl (fun T k => T.set! k t) T).size = T.size ∧
        ∀ k, (l.foldl (fun T k => T.set! k t) T)[k]! = if k ∈ l then t else T[k]!
  | [], T, _ => ⟨rfl, fun k => by simp⟩
  | a :: l, T, hl => by
    have ha := hl a List.mem_cons_self
    have hl' : ∀ a' ∈ l, a' < (T.set! a t).size := fun a' h => by
      simpa using hl a' (List.mem_cons_of_mem a h)
    obtain ⟨h1, h2⟩ := foldl_set_get t l (T.set! a t) hl'
    rw [List.foldl_cons]
    refine ⟨by rw [h1]; simp, fun k => ?_⟩
    rw [h2, set_get ha]
    by_cases hk : k ∈ l
    · simp [hk]
    · by_cases hka : k = a
      · simp [hka]
      · simp [hk, hka]

theorem fold_table_get {N M : Nat} {L : Nat → List Nat} {P : Nat → Nat}
    (hA : ∀ t < M, ∀ k ∈ L t, k < N ∧ P k = t)
    (hB : ∀ k < N, P k = 0 ∨ (P k < M ∧ k ∈ L (P k))) :
    ∀ k < N, ((List.range M).foldl (fun T t => (L t).foldl (fun T k => T.set! k t) T)
      (Array.replicate N 0))[k]! = P k := by
  have inv : ∀ j ≤ M,
      ((List.range j).foldl (fun T t => (L t).foldl (fun T k => T.set! k t) T)
        (Array.replicate N 0)).size = N ∧
      (∀ k < N, (∀ t < j, k ∉ L t) →
        ((List.range j).foldl (fun T t => (L t).foldl (fun T k => T.set! k t) T)
          (Array.replicate N 0))[k]! = 0) ∧
      (∀ k < N, ∀ t < j, k ∈ L t →
        ((List.range j).foldl (fun T t => (L t).foldl (fun T k => T.set! k t) T)
          (Array.replicate N 0))[k]! = P k) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨by simp, fun k hk _ => ?_, fun k _ t ht => absurd ht (Nat.not_lt_zero t)⟩
      simp only [List.range_zero, List.foldl_nil]
      rw [getElem!_pos _ k (by simpa using hk)]
      simp
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      generalize (List.range j).foldl (fun T t => (L t).foldl (fun T k => T.set! k t) T)
        (Array.replicate N 0) = T at h1 h2 h3
      have hl : ∀ a ∈ L j, a < T.size := fun a ha => by
        rw [h1]
        exact (hA j (by omega) a ha).1
      obtain ⟨e1, e2⟩ := foldl_set_get j (L j) T hl
      refine ⟨by rw [e1, h1], fun k hk hn => ?_, fun k hk t ht hkt => ?_⟩
      · rw [e2, if_neg (hn j (by omega))]
        exact h2 k hk fun t ht => hn t (by omega)
      · rw [e2]
        by_cases hkj : k ∈ L j
        · rw [if_pos hkj, (hA j (by omega) k hkj).2]
        · rw [if_neg hkj]
          have htj : t < j := by
            rcases Nat.lt_or_ge t j with h | h
            · exact h
            · have : t = j := by omega
              subst this
              exact absurd hkt hkj
          exact h3 k hk t htj hkt
  intro k hk
  obtain ⟨-, h2, h3⟩ := inv M le_rfl
  by_cases hex : ∃ t < M, k ∈ L t
  · obtain ⟨t, ht, hkt⟩ := hex
    exact h3 k hk t ht hkt
  · have hn : ∀ t < M, k ∉ L t := fun t ht hkt => hex ⟨t, ht, hkt⟩
    rw [h2 k hk hn]
    rcases hB k hk with e | ⟨e1, e2⟩
    · exact e.symm
    · exact absurd e2 (hn _ e1)

@[expose] def pairOf (L : Array (ℕ × ℕ × ℕ)) : Array ℕ := Id.run do
  let mut T : Array ℕ := Array.replicate 14400 0
  for t in [0:L.size] do
    let s := L[t]!
    T := T.set! (120 * s.1 + s.2.1) t
    T := T.set! (120 * s.2.1 + s.1) t
    T := T.set! (120 * s.1 + s.2.2) t
    T := T.set! (120 * s.2.2 + s.1) t
    T := T.set! (120 * s.2.1 + s.2.2) t
    T := T.set! (120 * s.2.2 + s.2.1) t
  return T

set_option maxHeartbeats 50000 in
theorem pairOf_eq (L : Array (ℕ × ℕ × ℕ)) : pairOf L = (List.range L.size).foldl
    (fun T t => (keys L[t]!).foldl (fun T k => T.set! k t) T) (Array.replicate 14400 0) := by
  unfold pairOf
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield _ _ _ (fun T t => (keys L[t]!).foldl (fun T k => T.set! k t) T),
    List.range_eq_range']
  · simp only [Id.run, pure_bind]
    rfl
  · intro t T
    simp only [keys, List.foldl_cons, List.foldl_nil]

set_option maxHeartbeats 50000 in
theorem pairLine_eq : pairLine = pairOf lineArr := rfl

theorem pairLine_get {P : Nat → Nat}
    (hA : ∀ t < lineArr.size, ∀ k ∈ keys lineArr[t]!, k < 14400 ∧ P k = t)
    (hB : ∀ k < 14400, P k = 0 ∨ (P k < lineArr.size ∧ k ∈ keys lineArr[P k]!)) :
    ∀ k < 14400, pairLine[k]! = P k := by
  rw [pairLine_eq]
  generalize lineArr = L at hA hB
  rw [pairOf_eq]
  exact fold_table_get hA hB

theorem filtStep_odd {p : Nat → Bool} {R : Nat → Nat} {i s : Nat} (hs : s % 2 = 1) :
    filtStep p R i s = s := by
  unfold filtStep
  rw [land_one, hs]
  rfl

theorem filt_inv {p : Nat → Bool} {R : Nat → Nat} : ∀ j : Nat,
    (List.range j).foldl (fun s i => filtStep p R i s) 0 % 2 = 1 ∨
      ∃ c, (List.range j).foldl (fun s i => filtStep p R i s) 0 = 2 * c ∧
        (List.range j).filter p = (List.range c).map R
  | 0 => Or.inr ⟨0, rfl, rfl⟩
  | j + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.filter_append]
    rcases filt_inv (p := p) (R := R) j with h | ⟨c, hc, hf⟩
    · exact Or.inl (by rw [filtStep_odd h]; exact h)
    · rw [hc, hf]
      have hev : Nat.beq (Nat.land (2 * c) (nat_lit 1)) (nat_lit 1) = false := by
        rw [land_one]
        cases e : Nat.beq (2 * c % 2) 1
        · rfl
        · have := Nat.eq_of_beq_eq_true e
          omega
      have hsh : Nat.shiftRight (2 * c) (nat_lit 1) = c := by
        change (2 * c) >>> 1 = c
        rw [Nat.shiftRight_eq_div_pow]
        omega
      unfold filtStep
      rw [hev]
      dsimp only
      cases hp : p j
      · refine Or.inr ⟨c, rfl, ?_⟩
        simp [hp]
      · rw [hsh]
        dsimp only
        by_cases hR : R c = j
        · rw [hR, Nat.beq_refl]
          refine Or.inr ⟨c + 1, by change 2 * c + 2 = 2 * (c + 1); ring, ?_⟩
          rw [List.range_succ, List.map_append]
          simp [hp, hR]
        · have hb : Nat.beq (R c) j = false := by
            cases e : Nat.beq (R c) j
            · rfl
            · exact absurd (Nat.eq_of_beq_eq_true e) hR
          rw [hb]
          exact Or.inl rfl

theorem filtK_sound {p : Nat → Bool} {R : Nat → Nat} {N cnt : Nat} (h : filtK p R N cnt = true) :
    (List.range N).filter p = (List.range cnt).map R := by
  unfold filtK at h
  rw [CFSG.KC.Pack.foldUp_eq] at h
  have h2 := Nat.eq_of_beq_eq_true h
  change (List.range N).foldl (fun s i => filtStep p R i s) 0 = 2 * cnt at h2
  rcases filt_inv (p := p) (R := R) N with h1 | ⟨c, hc, hf⟩
  · rw [h2] at h1
    omega
  · rw [hf]
    congr 1
    rw [h2] at hc
    have : cnt = c := by omega
    rw [this]

theorem flatMap_filter_range {α : Type} (A B : Nat) (q : Nat → Nat → Bool) (f : Nat → Nat → α) :
    (List.range A).flatMap (fun a => ((List.range B).filter (q a)).map (f a)) =
      ((List.range (A * B)).filter (fun i => q (i / B) (i % B))).map
        (fun i => f (i / B) (i % B)) := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.filter_append,
      List.map_append]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [List.filter_map, List.map_map]
    have hd : ∀ i ∈ List.range B, (A * B + i) / B = A ∧ (A * B + i) % B = i := by
      intro i hi
      have hi' := List.mem_range.1 hi
      have hB : 0 < B := by omega
      refine ⟨?_, ?_⟩
      · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hi', Nat.zero_add]
      · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi']
    have e1 : (List.range B).filter ((fun i => q (i / B) (i % B)) ∘ (A * B + ·)) =
        (List.range B).filter (q A) :=
      List.filter_congr fun i hi => by simp only [Function.comp_apply, (hd i hi).1, (hd i hi).2]
    rw [e1]
    refine List.map_congr_left fun i hi => ?_
    have hi' := (List.mem_filter.1 hi).1
    simp only [Function.comp_apply, (hd i hi').1, (hd i hi').2]

theorem bitN_toNat (x i : ℕ) : CFSG.KC.O8.bitN x i = (x.testBit i).toNat := by
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]

theorem bb_toNat (x y i j : ℕ) : CFSG.KC.O8.bb x y i j = (x.testBit i && y.testBit j).toNat := by
  rw [CFSG.KC.O8.bb, bitN_toNat, bitN_toNat]
  cases x.testBit i <;> cases y.testBit j <;> rfl

theorem xor_toNat (a b : Bool) : Nat.xor a.toNat b.toNat = (a ^^ b).toNat := by
  cases a <;> cases b <;> rfl

theorem b8K_eq (v w : ℕ) :
    CFSG.KC.O8.b8K false v w = (CFSG.EvenSmallLie.OmegaEight.bNat v w).toNat := by
  simp only [CFSG.KC.O8.b8K, CFSG.EvenSmallLie.OmegaEight.bNat, bb_toNat, xor_toNat,
    Bool.xor_assoc]

theorem q8K_eq (v : ℕ) : CFSG.KC.O8.q8K false v = (CFSG.EvenSmallLie.OmegaEight.qNat v).toNat := by
  simp only [CFSG.KC.O8.q8K, CFSG.EvenSmallLie.OmegaEight.qNat, bb_toNat, xor_toNat,
    Bool.xor_assoc]

theorem bNat_eq (v w : ℕ) :
    CFSG.EvenSmallLie.OmegaEight.bNat v w = Nat.beq (CFSG.KC.O8.b8K false v w) 1 := by
  rw [b8K_eq]
  cases CFSG.EvenSmallLie.OmegaEight.bNat v w <;> rfl

theorem eichNat_eq (u w x : ℕ) :
    CFSG.EvenSmallLie.OmegaEight.eichNat u w x = CFSG.KC.O8.eichK false u w x := by
  unfold CFSG.EvenSmallLie.OmegaEight.eichNat CFSG.KC.O8.eichK
  rw [b8K_eq, b8K_eq, q8K_eq]
  cases CFSG.EvenSmallLie.OmegaEight.bNat x u <;> cases CFSG.EvenSmallLie.OmegaEight.bNat x w <;>
    cases CFSG.EvenSmallLie.OmegaEight.qNat w <;> simp

end CFSG.KC.AS81

end
