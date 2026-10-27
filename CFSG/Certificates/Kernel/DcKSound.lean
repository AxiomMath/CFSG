module

public import Certificates.Data.Kernel.DcKN
public import CFSG.Certificates.Kernel.E64FSound
public import CFSG.Certificates.Kernel.Spor.KeyBfsGen

public section

namespace CFSG.KC.DcK

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.KC.E64F

theorem evalW_eq {n : Nat} {T : Array (Array Nat)} {L : Nat → Nat → Nat} :
    ∀ w : List Nat, (∀ l ∈ w, Good n (T.getD l #[]) (L l)) → ∀ p < n,
      evalW T w p = wordF L w p ∧ wordF L w p < n
  | [], _, p, hp => ⟨rfl, hp⟩
  | l :: w, hw, p, hp => by
    obtain ⟨e, hlt⟩ := evalW_eq w (fun l' h => hw l' (List.mem_cons_of_mem _ h)) p hp
    have hl := hw l List.mem_cons_self
    have e' : evalW T (l :: w) p = img (T.getD l #[]) (evalW T w p) := rfl
    have f' : wordF L (l :: w) p = L l (wordF L w p) := rfl
    rw [e', f', e]
    exact hl.2 _ hlt

theorem good_tabW {n : Nat} {T : Array (Array Nat)} {L : Nat → Nat → Nat} {w : List Nat}
    (hw : ∀ l ∈ w, Good n (T.getD l #[]) (L l)) : Good n (tabW n T w) (wordF L w) := by
  refine ⟨by simp [tabW], fun p hp => ?_⟩
  obtain ⟨e, hlt⟩ := evalW_eq w hw p hp
  refine ⟨?_, hlt⟩
  rw [← e]
  simp [tabW, Array.getD_eq_getD_getElem?, hp]

section BfsEnum
open CFSG.KS.KeyBfsG

private theorem bfsEnumL_forIn_rel {β γ : Type} (Rl : Nat → β → γ → Prop)
    (f : Nat → β → Id (ForInStep β)) (g : Nat → γ → Id (ForInStep γ))
    (h : ∀ x b c, Rl x b c → ∃ b' c', f x b = pure (ForInStep.yield b') ∧
      g x c = pure (ForInStep.yield c') ∧ Rl (x + 1) b' c') :
    ∀ (n s : Nat) (b : β) (c : γ), Rl s b c →
      Rl (s + n) (Id.run (forIn (List.range' s n) b f)) (Id.run (forIn (List.range' s n) c g)) := by
  intro n
  induction n with
  | zero => intro s b c h0; exact h0
  | succ n ih =>
    intro s b c h0
    obtain ⟨b', c', hf, hg, h1⟩ := h s b c h0
    rw [List.range'_succ, List.forIn_cons, List.forIn_cons, hf, hg]
    have := ih (s + 1) b' c' h1
    rw [show s + (n + 1) = s + 1 + n by omega]
    exact this

private abbrev BfsLSt := Array (List Nat) × Array Nat × Array Nat × Std.HashSet Nat × Nat

private def bfsEnumL_inner (n : Nat) (B : List Nat) (G : Array (Array Nat)) (r : List Nat) (h t : Nat)
    (s : GSt (List Nat)) : Id (ForInStep (GSt (List Nat))) :=
  if (!s.2.2.2.contains (keyNat n B.length (List.map (img (G.getD t #[])) r))) = true then
    pure (ForInStep.yield (s.1.push (List.map (img (G.getD t #[])) r), s.2.1.push h,
      s.2.2.1.push t, s.2.2.2.insert (keyNat n B.length (List.map (img (G.getD t #[])) r))))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

private def bfsEnumL_outer (n : Nat) (B : List Nat) (G : Array (Array Nat)) (_x : Nat) (s : BfsLSt) :
    Id (ForInStep BfsLSt) :=
  if s.2.2.2.2 < s.1.size then
    pure (ForInStep.yield (let s1 := Id.run (forIn (List.range' 0 G.size)
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1) (bfsEnumL_inner n B G s.1[s.2.2.2.2]! s.2.2.2.2));
      (s1.1, s1.2.1, s1.2.2.1, s1.2.2.2, s.2.2.2.2 + 1)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

private theorem bfsEnumL_eq_loop (n : Nat) (B : List Nat) (G : Array (Array Nat)) (cap : Nat) :
    bfsEnumL n B G cap =
      ((Id.run (forIn (List.range' 0 cap) ((#[B], #[0], #[0],
        (∅ : Std.HashSet Nat).insert (keyNat n B.length B), 0) : BfsLSt)
        (bfsEnumL_outer n B G))).2.1,
      (Id.run (forIn (List.range' 0 cap) ((#[B], #[0], #[0],
        (∅ : Std.HashSet Nat).insert (keyNat n B.length B), 0) : BfsLSt)
        (bfsEnumL_outer n B G))).2.2.1) := by
  unfold bfsEnumL
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def bfsEnumL_rel (h : Nat) (s : BfsLSt) (g : GSt (List Nat)) : Prop :=
  g = (s.1, s.2.1, s.2.2.1, s.2.2.2.1) ∧
    ((s.2.2.2.2 = h ∧ h ≤ s.1.size) ∨ (s.2.2.2.2 = s.1.size ∧ s.1.size ≤ h))

private theorem bfsEnumL_rel_step (n : Nat) (B : List Nat) (G : Array (Array Nat)) :
    ∀ x b c, bfsEnumL_rel x b c → ∃ b' c', bfsEnumL_outer n B G x b = pure (ForInStep.yield b') ∧
      outerG (keyNat n B.length) (fun t r => r.map (img (G.getD t #[]))) G.size x c =
        pure (ForInStep.yield c') ∧ bfsEnumL_rel (x + 1) b' c' := by
  rintro x ⟨rows, par, lab, seen, i⟩ g ⟨rfl, hi⟩
  dsimp only at hi
  by_cases hlt : i < rows.size
  · have hx : i = x := by omega
    subst hx
    have hstep : ∀ (t : Nat) (b c : GSt (List Nat)),
        (fun _ (b c : GSt (List Nat)) => c = b ∧ i < b.1.size ∧ b.1[i]! = rows[i]!) t b c →
        ∃ b' c', bfsEnumL_inner n B G rows[i]! i t b = pure (ForInStep.yield b') ∧
          innerG (keyNat n B.length) (fun t r => r.map (img (G.getD t #[]))) i t c =
            pure (ForInStep.yield c') ∧
          (fun _ (b c : GSt (List Nat)) => c = b ∧ i < b.1.size ∧ b.1[i]! = rows[i]!) (t + 1) b' c' := by
      rintro t b0 b ⟨rfl, hb, hr⟩
      by_cases hc : b.2.2.2.contains
          (keyNat n B.length (List.map (img (G.getD t #[])) rows[i]!)) = true
      · refine ⟨(b.1, b.2.1, b.2.2.1, b.2.2.2), (b.1, b.2.1, b.2.2.1, b.2.2.2), ?_, ?_,
          rfl, hb, hr⟩
        · simp only [bfsEnumL_inner, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        · simp only [innerG, hr, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · have hnc := Bool.eq_false_iff.2 hc
        refine ⟨(b.1.push (List.map (img (G.getD t #[])) rows[i]!), b.2.1.push i,
          b.2.2.1.push t, b.2.2.2.insert (keyNat n B.length (List.map (img (G.getD t #[])) rows[i]!))),
          (b.1.push (List.map (img (G.getD t #[])) rows[i]!), b.2.1.push i,
          b.2.2.1.push t, b.2.2.2.insert (keyNat n B.length (List.map (img (G.getD t #[])) rows[i]!))),
          ?_, ?_, rfl, ?_, ?_⟩
        · simp only [bfsEnumL_inner, hnc, Bool.not_false, ↓reduceIte]
        · simp only [innerG, hr, hnc, Bool.not_false, ↓reduceIte]
        · simp only [Array.size_push]
          omega
        · simp only
          rw [CFSG.KS.KeyBfs.push_lt hb]
          exact hr
    obtain ⟨e, hsz, -⟩ := bfsEnumL_forIn_rel
      (fun _ (b c : GSt (List Nat)) => c = b ∧ i < b.1.size ∧ b.1[i]! = rows[i]!)
      (bfsEnumL_inner n B G rows[i]! i)
      (innerG (keyNat n B.length) (fun t r => r.map (img (G.getD t #[]))) i) hstep G.size 0
      (rows, par, lab, seen) (rows, par, lab, seen) ⟨rfl, hlt, rfl⟩
    refine ⟨_, _, by simp only [bfsEnumL_outer, hlt, ↓reduceIte]; rfl,
      by simp only [outerG, hlt, ↓reduceIte]; rfl, ?_⟩
    refine ⟨?_, Or.inl ⟨rfl, ?_⟩⟩
    · exact e
    · exact hsz
  · have hx : ¬ x < rows.size := by omega
    refine ⟨(rows, par, lab, seen, i), (rows, par, lab, seen),
      by simp only [bfsEnumL_outer, hlt, ↓reduceIte],
      by simp only [outerG, hx, ↓reduceIte], rfl, Or.inr ⟨by dsimp only; omega,
        by dsimp only; omega⟩⟩

private theorem bfsEnumL_eq_keyBfsG (n : Nat) (B : List Nat) (G : Array (Array Nat)) (cap : Nat) :
    bfsEnumL n B G cap =
      ((keyBfsG (keyNat n B.length) (fun t r => r.map (img (G.getD t #[]))) G.size B
          (keyNat n B.length B) cap).2.1,
        (keyBfsG (keyNat n B.length) (fun t r => r.map (img (G.getD t #[]))) G.size B
          (keyNat n B.length B) cap).2.2) := by
  rw [bfsEnumL_eq_loop, keyBfsG_eq]
  obtain ⟨e, -⟩ := bfsEnumL_forIn_rel bfsEnumL_rel (bfsEnumL_outer n B G)
    (outerG (keyNat n B.length) (fun t r => r.map (img (G.getD t #[]))) G.size)
    (bfsEnumL_rel_step n B G) cap 0
    ((#[B], #[0], #[0], (∅ : Std.HashSet Nat).insert (keyNat n B.length B), 0) : BfsLSt)
    (initG B (keyNat n B.length B)) ⟨rfl, Or.inl ⟨rfl, by simp⟩⟩
  rw [e]

private theorem bfsEnumL_elemK_spec {n : Nat} {B : List Nat} {G : Nat → Nat → Nat} {m : Nat} {E : EnumK}
    {k : Nat} (h : elemK n B G m E k = true) :
    (k = 0 → E.row 0 = B ∧ E.par 0 = 0 ∧ E.lab 0 = 0 ∧ E.cnt 0 = 1) ∧
    (k ≠ 0 → E.par k < k ∧ E.lab k < m ∧ E.row k = (E.row (E.par k)).map (G (E.lab k))) ∧
    (∀ t < m, E.tgt k t < E.N ∧ (E.row k).map (G t) = E.row (E.tgt k t)) ∧
    E.sig k < E.N ∧ E.sinv (E.sig k) = k ∧ E.sinv k < E.N ∧ E.sig (E.sinv k) = k ∧
    (k + 1 < E.N → E.skey n B.length k < E.skey n B.length (k + 1)) ∧
    k < E.cnt k ∧
    replayRow E k (List.range m) (E.cnt k) = some (if k + 1 < E.N then E.cnt (k + 1) else E.N) := by
  unfold elemK at h
  by_cases hk : k = 0
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.or_eq_true, List.all_eq_true, List.mem_range] at h
    simp only [and_assoc] at h
    obtain ⟨a1, a2, a3, a4, h2, h3, h4, h5, h6, h8, h9, h10⟩ := h
    refine ⟨fun _ => ⟨a1, a2, a3, a4⟩, fun hk => absurd rfl hk, h2, h3, h4, h5,
      h6, fun hk => ?_, h9, h10⟩
    rcases h8 with a | a
    · omega
    · exact a
  · have hk' : (k == 0) = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, Bool.or_eq_true, List.all_eq_true, List.mem_range] at h
    simp only [and_assoc] at h
    obtain ⟨a1, a2, a3, h2, h3, h4, h5, h6, h8, h9, h10⟩ := h
    refine ⟨fun h0 => absurd h0 hk, fun _ => ⟨a1, a2, a3⟩, h2, h3, h4, h5,
      h6, fun hk => ?_, h9, h10⟩
    rcases h8 with a | a
    · omega
    · exact a

private theorem bfsEnumL_replayStep_spec {E : EnumK} {i t c c' : Nat} (h : replayStep E i t c = some c') :
    (E.tgt i t = c ∧ c < E.N ∧ E.par c = i ∧ E.lab c = t ∧ c' = c + 1) ∨
      (E.tgt i t < c ∧ c' = c) := by
  unfold replayStep at h
  by_cases h1 : E.tgt i t = c
  · by_cases h2 : c < E.N ∧ E.par c = i ∧ E.lab c = t
    · simp [h1, h2] at h
      exact Or.inl ⟨h1, h2.1, h2.2.1, h2.2.2, h.symm⟩
    · exfalso
      simp only [h1, beq_self_eq_true, ↓reduceIte] at h
      split at h
      · rename_i h3
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h3
        exact h2 ⟨h3.1.1, h3.1.2, h3.2⟩
      · exact absurd h (by simp)
  · have h1' : (E.tgt i t == c) = false := by simpa using h1
    simp only [h1', Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · rename_i h3
      exact Or.inr ⟨by simpa using h3, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

private theorem bfsEnumL_replayRow_spec (E : EnumK) (i : Nat) : ∀ (ts : List Nat) (c c' : Nat),
    ts.Pairwise (· < ·) → replayRow E i ts c = some c' →
    c ≤ c' ∧
    (∀ x, c ≤ x → x < c' → x < E.N ∧ E.par x = i ∧ E.lab x ∈ ts ∧
      (x + 1 < c' → E.lab x < E.lab (x + 1))) ∧
    (∀ t ∈ ts, E.tgt i t < c ∨ (c ≤ E.tgt i t ∧ E.tgt i t < c' ∧ E.lab (E.tgt i t) ≤ t))
  | [], c, c', _, h => by
    simp only [replayRow, Option.some.injEq] at h
    subst h
    exact ⟨Nat.le_refl _, fun x h1 h2 => by omega, by simp⟩
  | t :: ts, c, c', hp, h => by
    rw [List.pairwise_cons] at hp
    rw [replayRow] at h
    cases hs : replayStep E i t c with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some c1 =>
      rw [hs] at h
      dsimp only at h
      obtain ⟨A, Bb, C⟩ := bfsEnumL_replayRow_spec E i ts c1 c' hp.2 h
      rcases bfsEnumL_replayStep_spec hs with ⟨e1, e2, e3, e4, e5⟩ | ⟨e1, e5⟩
      · subst e5
        refine ⟨by omega, fun x hx1 hx2 => ?_, fun t' ht' => ?_⟩
        · rcases Nat.lt_or_ge x (c + 1) with a | a
          · have hxc : x = c := by omega
            subst hxc
            refine ⟨e2, e3, by rw [e4]; exact List.mem_cons_self, fun hx => ?_⟩
            obtain ⟨-, -, hm, -⟩ := Bb (x + 1) (Nat.le_refl _) hx
            rw [e4]
            exact hp.1 _ hm
          · obtain ⟨b1, b2, b3, b4⟩ := Bb x a hx2
            exact ⟨b1, b2, List.mem_cons_of_mem _ b3, b4⟩
        · rcases List.mem_cons.1 ht' with rfl | ht'
          · exact Or.inr ⟨by omega, by omega, by rw [e1, e4] <;> exact Nat.le_refl _⟩
          · rcases C t' ht' with a | a
            · rcases Nat.lt_or_ge (E.tgt i t') c with b | b
              · exact Or.inl b
              · have hb : E.tgt i t' = c := by omega
                have := hp.1 t' ht'
                exact Or.inr ⟨b, by omega, by rw [hb, e4]; exact Nat.le_of_lt this⟩
            · exact Or.inr ⟨by omega, a.2.1, a.2.2⟩
      · subst e5
        refine ⟨A, fun x hx1 hx2 => ?_, fun t' ht' => ?_⟩
        · obtain ⟨b1, b2, b3, b4⟩ := Bb x hx1 hx2
          exact ⟨b1, b2, List.mem_cons_of_mem _ b3, b4⟩
        · rcases List.mem_cons.1 ht' with rfl | ht'
          · exact Or.inl e1
          · exact C t' ht'

private def bfsEnumL_nxt (E : EnumK) (i : Nat) : Nat := if i + 1 < E.N then E.cnt (i + 1) else E.N

section

variable {n : Nat} {B : List Nat} {L : Nat → Nat → Nat} {m : Nat} {E : EnumK}

private theorem bfsEnumL_head (he : ∀ k < E.N, elemK n B L m E k = true) {i : Nat} (hi : i < E.N) :
    E.cnt i ≤ bfsEnumL_nxt E i ∧
    (∀ x, E.cnt i ≤ x → x < bfsEnumL_nxt E i → x < E.N ∧ E.par x = i ∧ E.lab x < m ∧
      (x + 1 < bfsEnumL_nxt E i → E.lab x < E.lab (x + 1))) ∧
    (∀ t < m, E.tgt i t < E.cnt i ∨
      (E.cnt i ≤ E.tgt i t ∧ E.tgt i t < bfsEnumL_nxt E i ∧ E.lab (E.tgt i t) ≤ t)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hr⟩ := bfsEnumL_elemK_spec (he i hi)
  obtain ⟨A, Bb, C⟩ := bfsEnumL_replayRow_spec E i (List.range m) _ _ List.pairwise_lt_range hr
  refine ⟨A, fun x h1 h2 => ?_, fun t ht => C t (List.mem_range.2 ht)⟩
  obtain ⟨b1, b2, b3, b4⟩ := Bb x h1 h2
  exact ⟨b1, b2, List.mem_range.1 b3, b4⟩

private theorem bfsEnumL_cnt_mono (he : ∀ k < E.N, elemK n B L m E k = true) :
    ∀ d i, i + d < E.N → E.cnt i ≤ E.cnt (i + d) := by
  intro d
  induction d with
  | zero => intro i _; exact Nat.le_refl _
  | succ d ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := (bfsEnumL_head he (i := i + d) (by omega)).1
    have e : bfsEnumL_nxt E (i + d) = E.cnt (i + (d + 1)) := by
      unfold bfsEnumL_nxt
      rw [if_pos (by omega)]
      rfl
    omega

private theorem bfsEnumL_cnt_le (he : ∀ k < E.N, elemK n B L m E k = true) {i j : Nat} (hij : i ≤ j)
    (hj : j < E.N) : E.cnt i ≤ E.cnt j := by
  have := bfsEnumL_cnt_mono he (j - i) i (by omega)
  rwa [Nat.add_sub_cancel' hij] at this

private theorem bfsEnumL_nxt_le (he : ∀ k < E.N, elemK n B L m E k = true) {i j : Nat} (hij : i < j)
    (hj : j < E.N) : bfsEnumL_nxt E i ≤ E.cnt j := by
  unfold bfsEnumL_nxt
  rw [if_pos (by omega)]
  exact bfsEnumL_cnt_le he hij hj

private theorem bfsEnumL_cover (he : ∀ k < E.N, elemK n B L m E k = true) {x : Nat} (hx0 : 0 < x)
    (hx : x < E.N) :
    E.cnt (E.par x) ≤ x ∧ x < bfsEnumL_nxt E (E.par x) ∧ E.par x < E.N ∧ E.lab x < m := by
  have aux : ∀ d j, j + d + 1 = E.N → E.cnt j ≤ x →
      ∃ i < E.N, E.cnt i ≤ x ∧ x < bfsEnumL_nxt E i := by
    intro d
    induction d with
    | zero =>
      intro j hj hc
      refine ⟨j, by omega, hc, ?_⟩
      unfold bfsEnumL_nxt
      rw [if_neg (by omega)]
      exact hx
    | succ d ih =>
      intro j hj hc
      by_cases h : x < E.cnt (j + 1)
      · refine ⟨j, by omega, hc, ?_⟩
        unfold bfsEnumL_nxt
        rw [if_pos (by omega)]
        exact h
      · exact ih (j + 1) (by omega) (by omega)
  have hc0 : E.cnt 0 = 1 := ((bfsEnumL_elemK_spec (he 0 (by omega))).1 rfl).2.2.2
  obtain ⟨i, hi, h1, h2⟩ := aux (E.N - 1) 0 (by omega) (by omega)
  obtain ⟨-, b2, b3, -⟩ := (bfsEnumL_head he hi).2.1 x h1 h2
  rw [b2]
  exact ⟨h1, h2, hi, b3⟩

private theorem bfsEnumL_mul_lt {k a b c d : Nat} (hb : b < k) (hac : a < c) : k * a + b < k * c + d := by
  have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hac)
  rw [Nat.mul_succ] at this
  omega

private theorem bfsEnumL_order (he : ∀ k < E.N, elemK n B L m E k = true) {x : Nat} (hx0 : 0 < x)
    (hx : x + 1 < E.N) : m * E.par x + E.lab x < m * E.par (x + 1) + E.lab (x + 1) := by
  obtain ⟨a1, a2, a3, a4⟩ := bfsEnumL_cover he hx0 (by omega)
  obtain ⟨b1, b2, b3, b4⟩ := bfsEnumL_cover he (x := x + 1) (by omega) hx
  rcases Nat.lt_trichotomy (E.par x) (E.par (x + 1)) with h | h | h
  · exact bfsEnumL_mul_lt a4 h
  · rw [← h] at b2
    have := ((bfsEnumL_head he a3).2.1 x a1 a2).2.2.2 b2
    rw [h]
    omega
  · have := bfsEnumL_nxt_le he h a3
    omega

private theorem bfsEnumL_close (he : ∀ k < E.N, elemK n B L m E k = true) {i t : Nat} (hi : i < E.N)
    (ht : t < m) :
    E.tgt i t = 0 ∨ m * E.par (E.tgt i t) + E.lab (E.tgt i t) ≤ m * i + t := by
  rcases (bfsEnumL_head he hi).2.2 t ht with h | ⟨h1, h2, h3⟩
  · rcases Nat.eq_zero_or_pos (E.tgt i t) with h0 | h0
    · exact Or.inl h0
    · right
      have hN := ((bfsEnumL_elemK_spec (he i hi)).2.2.1 t ht).1
      obtain ⟨a1, -, a3, a4⟩ := bfsEnumL_cover he h0 hN
      have hlt : E.par (E.tgt i t) < i := by
        refine Nat.lt_of_not_le fun hle => ?_
        have := bfsEnumL_cnt_le he hle a3
        omega
      exact Nat.le_of_lt (bfsEnumL_mul_lt a4 hlt)
  · right
    rw [((bfsEnumL_head he hi).2.1 _ h1 h2).2.1]
    omega

end

private theorem bfsEnumL_rows_lt {n : Nat} {B : List Nat} {G : Array (Array Nat)} {L : Nat → Nat → Nat}
    {E : EnumK} (hG : ∀ t < G.size, Good n (G.getD t #[]) (L t)) (hB : ∀ b ∈ B, b < n)
    (he : ∀ k < E.N, elemK n B L G.size E k = true) :
    ∀ b k, k < b → k < E.N → ∀ x ∈ E.row k, x < n := by
  intro b
  induction b with
  | zero => intro k hk; omega
  | succ b ih =>
    intro k hk hkN x hx
    obtain ⟨h0, h1, -⟩ := bfsEnumL_elemK_spec (he k hkN)
    by_cases hk0 : k = 0
    · subst hk0
      rw [(h0 rfl).1] at hx
      exact hB x hx
    · obtain ⟨hp, hl, hr⟩ := h1 hk0
      rw [hr, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ((hG _ hl).2 y (ih (E.par k) (by omega) (by omega) y hy)).2

private theorem bfsEnumL_st_eq {n : Nat} {G : Array (Array Nat)} {L : Nat → Nat → Nat}
    (hG : ∀ t < G.size, Good n (G.getD t #[]) (L t)) {r : List Nat} (hr : ∀ x ∈ r, x < n)
    {t : Nat} (ht : t < G.size) : r.map (img (G.getD t #[])) = r.map (L t) :=
  List.map_congr_left fun x hx => ((hG t ht).2 x (hr x hx)).1

private theorem bfsEnumL_inj {n : Nat} {B : List Nat} {L : Nat → Nat → Nat} {m : Nat} {E : EnumK}
    (he : ∀ k < E.N, elemK n B L m E k = true) :
    ∀ a < E.N, ∀ b < E.N, keyNat n B.length (E.row a) = keyNat n B.length (E.row b) → a = b := by
  have hS := fun p hp => bfsEnumL_elemK_spec (n := n) (B := B) (G := L) (m := m) (he p hp)
  have mono : ∀ p1 p2, p1 < p2 → p2 < E.N → E.skey n B.length p1 < E.skey n B.length p2 := by
    intro p1 p2 h12 h2c
    induction p2 with
    | zero => omega
    | succ p ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 h12 with h | h
      · exact Nat.lt_trans (ih h (by omega)) ((hS p (by omega)).2.2.2.2.2.2.2.1 h2c)
      · subst h
        exact (hS p1 (by omega)).2.2.2.2.2.2.2.1 h2c
  intro a ha b hb e
  obtain ⟨-, -, -, -, -, ha1, ha2, -⟩ := hS a ha
  obtain ⟨-, -, -, -, -, hb1, hb2, -⟩ := hS b hb
  have ek : ∀ p, E.skey n B.length p = keyNat n B.length (E.row (E.sig p)) := fun _ => rfl
  rcases Nat.lt_trichotomy (E.sinv a) (E.sinv b) with hlt | heq | hgt
  · have := mono _ _ hlt hb1
    rw [ek, ek, ha2, hb2] at this
    omega
  · rw [← ha2, ← hb2, heq]
  · have := mono _ _ hgt ha1
    rw [ek, ek, ha2, hb2] at this
    omega

theorem bfsEnumL_of_elemK {n cap : Nat} {B : List Nat} {G : Array (Array Nat)}
    {L : Nat → Nat → Nat} {E : EnumK} (hG : ∀ t < G.size, Good n (G.getD t #[]) (L t))
    (hm : 0 < G.size) (hd : enumHd n B cap E = true)
    (he : ∀ k < E.N, elemK n B L G.size E k = true) :
    bfsEnumL n B G cap =
      (((List.range E.N).map E.par).toArray, ((List.range E.N).map E.lab).toArray) := by
  have hd' : 0 < E.N ∧ E.N ≤ cap ∧ ∀ b ∈ B, b < n := by
    simpa [enumHd, and_assoc] using hd
  obtain ⟨hN0, hNcap, hB⟩ := hd'
  have hS := fun k hk => bfsEnumL_elemK_spec (n := n) (B := B) (G := L) (m := G.size) (he k hk)
  obtain ⟨hr0, hp0, hl0, -⟩ := (hS 0 hN0).1 rfl
  have hrow := fun k hk => bfsEnumL_rows_lt hG hB he (k + 1) k (Nat.lt_succ_self k) hk
  have R : GRec (keyNat n B.length) (fun t r => r.map (img (G.getD t #[]))) G.size B
      (keyNat n B.length B) E.N (G.size * E.N) E.row E.par E.lab
      (fun e => E.tgt (e / G.size) (e % G.size)) := by
    refine ⟨hm, hN0, hr0, rfl, hp0, hl0, bfsEnumL_inj he, fun i hi0 hi => ?_,
      fun i hi0 hi => bfsEnumL_order he hi0 hi, ?_, fun e he' => ?_⟩
    · obtain ⟨hp, hl, hr⟩ := (hS i hi).2.1 (by omega)
      refine ⟨hp, hl, ?_⟩
      rw [bfsEnumL_st_eq hG (hrow _ (by omega)) hl]
      exact hr
    · rcases Nat.eq_zero_or_pos (E.N - 1) with h | h
      · rw [h, hp0, hl0]
        exact Nat.mul_pos hm hN0
      · obtain ⟨hp, hl, -⟩ := (hS (E.N - 1) (by omega)).2.1 (by omega)
        have := bfsEnumL_mul_lt (d := 0) hl (by omega : E.par (E.N - 1) < E.N)
        omega
    · have hi : e / G.size < E.N := (Nat.div_lt_iff_lt_mul hm).2 (by rwa [Nat.mul_comm] at he')
      have ht : e % G.size < G.size := Nat.mod_lt _ hm
      obtain ⟨htN, hrt⟩ := (hS _ hi).2.2.1 _ ht
      refine ⟨htN, ?_, ?_⟩
      · rw [bfsEnumL_st_eq hG (hrow _ hi) ht, hrt]
      · have := bfsEnumL_close he hi ht
        rw [Nat.div_add_mod] at this
        exact this
  have hcap : E.par (E.N - 1) < cap := by
    rcases Nat.eq_zero_or_pos (E.N - 1) with h | h
    · rw [h, hp0]
      omega
    · have := ((hS (E.N - 1) (by omega)).2.1 (by omega)).1
      omega
  obtain ⟨-, hget, hsz, hps, hls⟩ := keyBfsG_rec R hcap
  have hsz' := hsz (Nat.le_refl _)
  rw [bfsEnumL_eq_keyBfsG]
  congr 1
  · apply Array.ext
    · rw [hps, hsz', List.size_toArray, List.length_map, List.length_range]
    · intro j h1 h2
      rw [← getElem!_pos _ j h1]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      exact (hget j (by rw [hps, hsz'] at h1; exact h1)).2.1
  · apply Array.ext
    · rw [hls, hsz', List.size_toArray, List.length_map, List.length_range]
    · intro j h1 h2
      rw [← getElem!_pos _ j h1]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      exact (hget j (by rw [hls, hsz'] at h1; exact h1)).2.2

end BfsEnum

section OrbitLabels

private def orbitLabels_of_orbCK_gensB (n : Nat) (G : Array (Array Nat)) (c x : Nat) (t : Nat)
    (st : (Array Nat × Array Nat)) : Id (ForInStep ((Array Nat × Array Nat))) :=
  if (st.1.getD (img (G.getD t #[]) x) 0 == n) = true then
    pure (ForInStep.yield (st.1.set! (img (G.getD t #[]) x) c, st.2.push (img (G.getD t #[]) x)))
  else pure (ForInStep.yield (st.1, st.2))

private def orbitLabels_of_orbCK_queueB (n : Nat) (G : Array (Array Nat)) (c : Nat) (_ : Nat)
    (st : (Array Nat × Array Nat × Nat)) :
    Id (ForInStep ((Array Nat × Array Nat × Nat))) :=
  if st.2.2 < st.2.1.size then do
    let r ← forIn (List.range' 0 G.size) ((st.1, st.2.1) : (Array Nat × Array Nat))
      (orbitLabels_of_orbCK_gensB n G c (st.2.1.getD st.2.2 0))
    pure (ForInStep.yield (r.1, r.2, st.2.2 + 1))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2))

private def orbitLabels_of_orbCK_scanB (n : Nat) (G : Array (Array Nat)) (s : Nat)
    (st : (Array Nat × Nat)) : Id (ForInStep ((Array Nat × Nat))) :=
  if (st.1.getD s 0 == n) = true then do
    let r ← forIn (List.range' 0 n)
      ((st.1.set! s st.2, #[s], 0) : (Array Nat × Array Nat × Nat))
      (orbitLabels_of_orbCK_queueB n G st.2)
    pure (ForInStep.yield (r.1, st.2 + 1))
  else pure (ForInStep.yield (st.1, st.2))

private theorem orbitLabels_of_orbCK_eq (n : Nat) (G : Array (Array Nat)) :
    orbitLabels n G = (Id.run (forIn (List.range' 0 n)
      ((Array.replicate n n, 0) : (Array Nat × Nat)) (orbitLabels_of_orbCK_scanB n G))).1 := by
  unfold orbitLabels
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def orbitLabels_of_orbCK_LInv (n : Nat) (vt lb : Nat → Nat) (cnt : Nat) (A : Array Nat) : Prop :=
  A.size = n ∧ ∀ y < n, A.getD y 0 = if vt y < cnt then lb y else n

private def orbitLabels_of_orbCK_QInv (Q : Nat → Nat) (cnt0 cnt : Nat) (q : Array Nat) : Prop :=
  cnt0 + q.size = cnt ∧ ∀ j < q.size, q.getD j 0 = Q (cnt0 + j)

private def orbitLabels_of_orbCK_HB (n : Nat) (Q vt lb : Nat → Nat) : Prop :=
  ∀ y < n, vt y < n ∧ Q (vt y) = y ∧ Q y < n ∧ vt (Q y) = y ∧ lb y < n

private theorem orbitLabels_of_orbCK_hb {n : Nat} {L : Nat → Nat → Nat} {m : Nat} {Q vt lb : Nat → Nat}
    (h : orbCK n L m Q vt lb = true) :
    orbitLabels_of_orbCK_HB n Q vt lb ∧ orbScan n L m Q vt lb (List.range n) 0 0 = some n := by
  unfold orbCK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq]
    at h
  exact ⟨fun y hy => by
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h.1 y hy
    exact ⟨a, b, c, d, e⟩, h.2⟩

private theorem orbitLabels_of_orbCK_test {n : Nat} {Q vt lb : Nat → Nat} {cnt : Nat} {A : Array Nat}
    (hA : orbitLabels_of_orbCK_LInv n vt lb cnt A) (hB : orbitLabels_of_orbCK_HB n Q vt lb)
    {y : Nat} (hy : y < n) : (A.getD y 0 == n) = !decide (vt y < cnt) := by
  rw [hA.2 y hy]
  have := (hB y hy).2.2.2.2
  by_cases h : vt y < cnt <;> simp [h]
  omega

private theorem orbitLabels_of_orbCK_set {n : Nat} {Q vt lb : Nat → Nat} {cnt : Nat} {A : Array Nat}
    (hA : orbitLabels_of_orbCK_LInv n vt lb cnt A) (hB : orbitLabels_of_orbCK_HB n Q vt lb)
    {y : Nat} (hy : y < n) (hv : vt y = cnt) :
    orbitLabels_of_orbCK_LInv n vt lb (cnt + 1) (A.set! y (lb y)) := by
  refine ⟨by simp [hA.1], fun z hz => ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
  by_cases hzy : y = z
  · subst hzy
    simp [hA.1, hy, hv]
  · simp only [hzy, ↓reduceIte]
    rw [← Array.getD_eq_getD_getElem?, hA.2 z hz]
    have hne : vt z ≠ cnt := fun e => hzy (by
      have h1 := (hB z hz).2.1
      have h2 := (hB y hy).2.1
      rw [e, ← hv] at h1
      rw [← h1, h2])
    by_cases h1 : vt z < cnt
    · simp [h1, show vt z < cnt + 1 by omega]
    · simp [h1, show ¬ vt z < cnt + 1 by omega]

private theorem orbitLabels_of_orbCK_push {n : Nat} {Q vt lb : Nat → Nat} {cnt0 cnt : Nat} {q : Array Nat}
    (hq : orbitLabels_of_orbCK_QInv Q cnt0 cnt q) (hB : orbitLabels_of_orbCK_HB n Q vt lb)
    {y : Nat} (hy : y < n) (hv : vt y = cnt) :
    orbitLabels_of_orbCK_QInv Q cnt0 (cnt + 1) (q.push y) := by
  refine ⟨by simp [← hq.1]; omega, fun j hj => ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases hjs : j = q.size
  · subst hjs
    simp only [↓reduceIte, Option.getD_some]
    rw [hq.1, ← hv, (hB y hy).2.1]
  · simp only [hjs, ↓reduceIte]
    rw [← Array.getD_eq_getD_getElem?]
    exact hq.2 j (by simp at hj; omega)

private theorem orbitLabels_of_orbCK_gens {n : Nat} {G : Array (Array Nat)} {L : Nat → Nat → Nat}
    {Q vt lb : Nat → Nat} (hG : ∀ t < G.size, Good n (G.getD t #[]) (L t))
    (hB : orbitLabels_of_orbCK_HB n Q vt lb) {c x cnt0 : Nat} (hx : x < n) :
    ∀ (ts : List Nat), (∀ t ∈ ts, t < G.size) → ∀ (cnt cnt' : Nat) (A q : Array Nat),
      orbitLabels_of_orbCK_LInv n vt lb cnt A → orbitLabels_of_orbCK_QInv Q cnt0 cnt q →
      cnt ≤ n → orbGens L vt lb c x ts cnt = some cnt' →
      orbitLabels_of_orbCK_LInv n vt lb cnt'
          (Id.run (forIn ts (A, q) (orbitLabels_of_orbCK_gensB n G c x))).1 ∧
        orbitLabels_of_orbCK_QInv Q cnt0 cnt'
          (Id.run (forIn ts (A, q) (orbitLabels_of_orbCK_gensB n G c x))).2 ∧
        cnt ≤ cnt' ∧ cnt' ≤ n
  | [], _, cnt, cnt', A, q, hA, hq, hn, h => by
    simp only [orbGens, Option.some.injEq] at h
    subst h
    exact ⟨hA, hq, Nat.le_refl _, hn⟩
  | t :: ts, hts, cnt, cnt', A, q, hA, hq, hn, h => by
    have ht := hG t (hts t List.mem_cons_self)
    have himg : img (G.getD t #[]) x = L t x := (ht.2 x hx).1
    have hy : L t x < n := (ht.2 x hx).2
    have hts' : ∀ t ∈ ts, t < G.size := fun t' h' => hts t' (List.mem_cons_of_mem _ h')
    rw [List.forIn_cons]
    unfold orbGens at h
    by_cases hl : vt (L t x) < cnt
    · simp only [hl, decide_true, ↓reduceIte] at h
      simp only [orbitLabels_of_orbCK_gensB, himg, orbitLabels_of_orbCK_test hA hB hy, hl,
        decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind, Id.run]
      exact orbitLabels_of_orbCK_gens hG hB hx ts hts' cnt cnt' A q hA hq hn h
    · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq]
        at h
      split at h
      · rename_i hc
        obtain ⟨hv, hc⟩ := hc
        subst hc
        have hn' : cnt + 1 ≤ n := by have := (hB _ hy).1; omega
        simp only [orbitLabels_of_orbCK_gensB, himg, orbitLabels_of_orbCK_test hA hB hy, hl,
          decide_false, Bool.not_false, ↓reduceIte, pure_bind, Id.run]
        obtain ⟨h1, h2, h3, h4⟩ := orbitLabels_of_orbCK_gens hG hB hx ts hts' (cnt + 1) cnt' _ _
          (orbitLabels_of_orbCK_set hA hB hy hv) (orbitLabels_of_orbCK_push hq hB hy hv) hn' h
        exact ⟨h1, h2, by omega, h4⟩
      · exact absurd h (by simp)

private theorem orbitLabels_of_orbCK_idle {n : Nat} {G : Array (Array Nat)} {c : Nat} {A q : Array Nat}
    {h : Nat} (hh : ¬ h < q.size) :
    ∀ l : List Nat, Id.run (forIn l (A, q, h) (orbitLabels_of_orbCK_queueB n G c)) = (A, q, h)
  | [] => rfl
  | a :: l => by
    rw [List.forIn_cons]
    simp only [orbitLabels_of_orbCK_queueB, hh, ↓reduceIte, pure_bind]
    exact orbitLabels_of_orbCK_idle hh l

private theorem orbitLabels_of_orbCK_queue {n : Nat} {G : Array (Array Nat)} {L : Nat → Nat → Nat}
    {Q vt lb : Nat → Nat} (hG : ∀ t < G.size, Good n (G.getD t #[]) (L t))
    (hB : orbitLabels_of_orbCK_HB n Q vt lb) {c cnt0 : Nat} :
    ∀ (l : List Nat) (A q : Array Nat) (h cnt cnt' : Nat),
      orbitLabels_of_orbCK_LInv n vt lb cnt A → orbitLabels_of_orbCK_QInv Q cnt0 cnt q →
      h ≤ q.size → cnt ≤ n → orbQueue L G.size Q vt lb c l.length (cnt0 + h) cnt = some cnt' →
      orbitLabels_of_orbCK_LInv n vt lb cnt'
          (Id.run (forIn l (A, q, h) (orbitLabels_of_orbCK_queueB n G c))).1 ∧
        orbitLabels_of_orbCK_QInv Q cnt0 cnt'
          (Id.run (forIn l (A, q, h) (orbitLabels_of_orbCK_queueB n G c))).2.1 ∧ cnt' ≤ n := by
  intro l A q h cnt cnt' hA hq hh hn ho
  by_cases hlt : h < q.size
  · match l with
    | [] =>
      simp only [List.length_nil, orbQueue, Option.some.injEq] at ho
      subst ho
      exact ⟨hA, hq, hn⟩
    | a :: l =>
      have hac : cnt0 + h < cnt := by have := hq.1; omega
      have hx : q.getD h 0 = Q (cnt0 + h) := hq.2 h hlt
      have hxn : Q (cnt0 + h) < n := (hB _ (by omega)).2.2.1
      simp only [List.length_cons, orbQueue, hac, decide_true, ↓reduceIte] at ho
      split at ho
      · rename_i cnt'' hg
        rw [List.range_eq_range'] at hg
        obtain ⟨h1, h2, h3, h4⟩ := orbitLabels_of_orbCK_gens hG hB hxn (List.range' 0 G.size)
          (fun t ht => by simp [List.mem_range'] at ht; omega) cnt cnt'' A q hA hq hn hg
        rw [List.forIn_cons]
        simp only [orbitLabels_of_orbCK_queueB, hlt, ↓reduceIte, hx, pure_bind, Id.run] at h1 h2 ⊢
        exact orbitLabels_of_orbCK_queue hG hB l _ _ (h + 1) cnt'' cnt' h1 h2
          (by have := h2.1; have := hq.1; omega) h4 ho
      · exact absurd ho (by simp)
  · rw [orbitLabels_of_orbCK_idle hlt]
    have : cnt' = cnt := by
      cases l with
      | nil => simpa [orbQueue] using ho.symm
      | cons a l =>
        have hac : ¬ cnt0 + h < cnt := by have := hq.1; omega
        simpa [orbQueue, hac] using ho.symm
    subst this
    exact ⟨hA, hq, hn⟩

private theorem orbitLabels_of_orbCK_scan {n : Nat} {G : Array (Array Nat)} {L : Nat → Nat → Nat}
    {Q vt lb : Nat → Nat} (hG : ∀ t < G.size, Good n (G.getD t #[]) (L t))
    (hB : orbitLabels_of_orbCK_HB n Q vt lb) :
    ∀ (ss : List Nat), (∀ s ∈ ss, s < n) → ∀ (A : Array Nat) (c cnt cnt' : Nat),
      orbitLabels_of_orbCK_LInv n vt lb cnt A → cnt ≤ n →
      orbScan n L G.size Q vt lb ss c cnt = some cnt' →
      orbitLabels_of_orbCK_LInv n vt lb cnt'
        (Id.run (forIn ss (A, c) (orbitLabels_of_orbCK_scanB n G))).1
  | [], _, A, c, cnt, cnt', hA, _, h => by
    simp only [orbScan, Option.some.injEq] at h
    subst h
    exact hA
  | s :: ss, hss, A, c, cnt, cnt', hA, hn, h => by
    have hs : s < n := hss s List.mem_cons_self
    have hss' : ∀ s ∈ ss, s < n := fun s' h' => hss s' (List.mem_cons_of_mem _ h')
    rw [List.forIn_cons]
    unfold orbScan at h
    by_cases hl : vt s < cnt
    · simp only [hl, decide_true, ↓reduceIte] at h
      simp only [orbitLabels_of_orbCK_scanB, orbitLabels_of_orbCK_test hA hB hs, hl,
        decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind, Id.run]
      exact orbitLabels_of_orbCK_scan hG hB ss hss' A c cnt cnt' hA hn h
    · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq]
        at h
      split at h
      · rename_i hc
        obtain ⟨hv, hc⟩ := hc
        subst hc
        have hn' : cnt + 1 ≤ n := by have := (hB _ hs).1; omega
        split at h
        · rename_i cnt'' hq
          have hq0 : orbitLabels_of_orbCK_QInv Q cnt (cnt + 1) #[s] :=
            ⟨by simp, fun j hj => by
              simp at hj
              subst hj
              simp [← hv, (hB s hs).2.1]⟩
          obtain ⟨h1, -, h3⟩ := orbitLabels_of_orbCK_queue hG hB (List.range' 0 n) _ _ 0
            (cnt + 1) cnt'' (orbitLabels_of_orbCK_set hA hB hs hv) hq0 (by simp) hn'
            (by simpa using hq)
          simp only [orbitLabels_of_orbCK_scanB, orbitLabels_of_orbCK_test hA hB hs, hl,
            decide_false, Bool.not_false, ↓reduceIte, pure_bind, Id.run] at h1 ⊢
          exact orbitLabels_of_orbCK_scan hG hB ss hss' _ _ cnt'' cnt' h1 h3 h
        · exact absurd h (by simp)
      · exact absurd h (by simp)

theorem orbitLabels_of_orbCK {n : Nat} {G : Array (Array Nat)} {L : Nat → Nat → Nat}
    {Q vt lb : Nat → Nat} (hG : ∀ t < G.size, Good n (G.getD t #[]) (L t))
    (h : orbCK n L G.size Q vt lb = true) : ∀ q < n, (orbitLabels n G).getD q 0 = lb q := by
  intro q hq
  obtain ⟨hB, hs⟩ := orbitLabels_of_orbCK_hb h
  rw [List.range_eq_range'] at hs
  have h0 : orbitLabels_of_orbCK_LInv n vt lb 0 (Array.replicate n n) :=
    ⟨by simp, fun y hy => by simp [Array.getD_eq_getD_getElem?, hy]⟩
  have := orbitLabels_of_orbCK_scan hG hB (List.range' 0 n)
    (fun s hs' => by simp [List.mem_range'] at hs'; omega) _ 0 0 n h0 (Nat.zero_le _) hs
  rw [orbitLabels_of_orbCK_eq, this.2 q hq]
  simp [(hB q hq).1]

end OrbitLabels

structure Rel (D : DcData) (K : DcK) : Prop where
  n_eq : D.n = K.n
  B_eq : D.B = K.B
  ab_size : D.AB.size = 4
  ab : ∀ l < 4, Good K.n (D.AB.getD l #[]) (K.ab l)
  rt_size : D.RT.size = K.nr
  rti_size : D.RTi.size = K.nr
  rt : ∀ t < K.nr, Good K.n (D.RT.getD t #[]) (K.rt t)
  rti : ∀ t < K.nr, Good K.n (D.RTi.getD t #[]) (K.rti t)
  NR_eq : D.NR = K.R.N
  rpar : ∀ k < K.R.N, D.rpar.getD k 0 = K.R.par k
  rlab : ∀ k < K.R.N, D.rlab.getD k 0 = K.R.lab k
  lb : ∀ q < K.n, D.lb.getD q 0 = K.lb q
  reps_eq : D.reps = K.reps
  edges_eq : D.edges = K.edges
  c0_eq : D.c0 = K.c0
  inEdge_eq : D.inEdge = K.inEdge
  dIn_eq : D.dIn = K.dIn
  reach_eq : D.reach = K.reach
  outEdge_eq : D.outEdge = K.outEdge
  dOut_eq : D.dOut = K.dOut
  order_eq : D.order = K.order
  Vs : List.Forall₂ (fun V W => V.1 = W.1 ∧ V.2.2.2 = W.2.2.N ∧
    (∀ i < V.1.length, ∀ p < K.n, wordF K.ab (V.1.getD i []) p = W.2.1 i p) ∧
    ∀ k < W.2.2.N, V.2.1.getD k 0 = W.2.2.par k ∧ V.2.2.1.getD k 0 = W.2.2.lab k) D.Vs K.Vs

section ChkAll

private theorem chkAll_of_chkAllK_good_congr {n : Nat} {s : Array Nat} {f g : Nat → Nat}
    (h : Good n s f) (hfg : ∀ p < n, f p = g p) : Good n s g :=
  ⟨h.1, fun p hp => by rw [← hfg p hp]; exact h.2 p hp⟩

private theorem chkAll_of_chkAllK_img {n : Nat} {s : Array Nat} {f : Nat → Nat} (h : Good n s f)
    {p : Nat} (hp : p < n) : img s p = f p ∧ f p < n := h.2 p hp

private theorem chkAll_of_chkAllK_strictInc : ∀ l : List Nat, l.Pairwise (· < ·) → strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have h1 : a < b := List.rel_of_pairwise_cons h List.mem_cons_self
    have h2 := chkAll_of_chkAllK_strictInc (b :: l) h.of_cons
    simp [strictInc, h1, h2]

private theorem chkAll_of_chkAllK_distinctNat {l : List Nat} (h : l.Nodup) : distinctNat l = true := by
  unfold distinctNat
  apply chkAll_of_chkAllK_strictInc
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) l
  have hn : (l.mergeSort fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm l _).nodup_iff.mpr h
  exact (hs.and hn).imp fun ⟨h1, h2⟩ => by simp at h1; omega

private theorem chkAll_of_chkAllK_allNe : ∀ {l : List Nat}, allNe l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [allNe, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    exact List.nodup_cons.mpr ⟨fun hx => h.1 x hx rfl, chkAll_of_chkAllK_allNe h.2⟩

private theorem chkAll_of_chkAllK_sumK (f : Nat → Nat) :
    ∀ (l : List Nat) (a : Nat), sumK f l a = a + (l.map f).sum
  | [], a => by simp [sumK]
  | k :: ks, a => by
    rw [sumK, chkAll_of_chkAllK_sumK f ks]; simp; omega

private theorem chkAll_of_chkAllK_cntB (f : Nat → Bool) :
    ∀ (l : List Nat) (a : Nat), cntB f l a = a + (l.filter f).length
  | [], a => by simp [cntB]
  | k :: ks, a => by
    rw [cntB]
    split <;> rename_i hk <;> rw [chkAll_of_chkAllK_cntB f ks] <;> simp [List.filter_cons, hk] <;>
      omega

private theorem chkAll_of_chkAllK_cntK (f : Nat → Option Bool) (g : Nat → Bool) :
    ∀ (l : List Nat) (a c : Nat), (∀ k ∈ l, (f k = some true → g k = true) ∧
      (f k = some false → g k = false)) → cntK f l a = some c → c = a + (l.filter g).length
  | [], a, c, _, h => by simp [cntK] at h; simp [h]
  | k :: ks, a, c, hg, h => by
    have hks : ∀ k ∈ ks, (f k = some true → g k = true) ∧ (f k = some false → g k = false) :=
      fun k' hk' => hg k' (List.mem_cons_of_mem _ hk')
    have hk := hg k List.mem_cons_self
    rw [cntK] at h
    split at h
    · rename_i hf
      rw [chkAll_of_chkAllK_cntK f g ks (a + 1) c hks h]
      simp [List.filter_cons, hk.1 hf]; omega
    · rename_i hf
      rw [chkAll_of_chkAllK_cntK f g ks a c hks h]
      simp [List.filter_cons, hk.2 hf]
    · simp at h

private theorem chkAll_of_chkAllK_forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | _, _, .nil, a, ha => by simp at ha
  | _, _, .cons (a := a') (b := b') r h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b', List.mem_cons_self, r⟩
    · obtain ⟨b, hb, hr⟩ := chkAll_of_chkAllK_forall₂_mem h a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

private theorem chkAll_of_chkAllK_ptsArr_succ (G : Array (Array Nat)) (par lab : Array Nat) (M q : Nat) :
    ptsArr G par lab (M + 1) q = ptsStep G par lab q (ptsArr G par lab M q) M := by
  simp [ptsArr, List.range_succ, List.foldl_append]

private theorem chkAll_of_chkAllK_ptsArr_size (G : Array (Array Nat)) (par lab : Array Nat) (q : Nat) :
    ∀ M, (ptsArr G par lab M q).size = M
  | 0 => rfl
  | M + 1 => by
    rw [chkAll_of_chkAllK_ptsArr_succ]
    simp [ptsStep, chkAll_of_chkAllK_ptsArr_size G par lab q M]

private theorem chkAll_of_chkAllK_ptsArr_getD_le (G : Array (Array Nat)) (par lab : Array Nat) (q : Nat)
    {k M : Nat} (hk : k < M) : ∀ N, M ≤ N →
      (ptsArr G par lab N q).getD k 0 = (ptsArr G par lab M q).getD k 0 := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hMN ih =>
    rw [chkAll_of_chkAllK_ptsArr_succ, ← ih]
    have hs := chkAll_of_chkAllK_ptsArr_size G par lab q N
    simp only [ptsStep, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]
    rw [if_neg (by omega)]

private theorem chkAll_of_chkAllK_ptsArr_getD (G : Array (Array Nat)) (par lab : Array Nat) (q : Nat)
    {k N : Nat} (hk : k < N) : (ptsArr G par lab N q).getD k 0 =
      if k = 0 then q else img (G.getD (lab.getD k 0) #[]) ((ptsArr G par lab k q).getD (par.getD k 0) 0) := by
  rw [chkAll_of_chkAllK_ptsArr_getD_le G par lab q (Nat.lt_succ_self k) N hk,
    chkAll_of_chkAllK_ptsArr_succ]
  have hs := chkAll_of_chkAllK_ptsArr_size G par lab q k
  simp only [ptsStep, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]
  simp

private theorem chkAll_of_chkAllK_elemK {n : Nat} {B : List Nat} {G : Nat → Nat → Nat} {m : Nat}
    {E : EnumK} {k : Nat} (h : elemK n B G m E k = true) :
    (k = 0 → E.row 0 = B) ∧
    (k ≠ 0 → E.par k < k ∧ E.lab k < m ∧ E.row k = (E.row (E.par k)).map (G (E.lab k))) ∧
    (∀ t < m, E.tgt k t < E.N ∧ (E.row k).map (G t) = E.row (E.tgt k t)) ∧
    E.sig k < E.N ∧ E.sinv (E.sig k) = k ∧ E.sinv k < E.N ∧ E.sig (E.sinv k) = k ∧
    (E.N ≤ k + 1 ∨ E.skey n B.length k < E.skey n B.length (k + 1)) := by
  unfold elemK at h
  by_cases hk : k = 0
  · subst hk
    simp only [beq_self_eq_true, if_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      List.mem_range, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, -⟩ := h
    exact ⟨fun _ => h1, fun h0 => absurd rfl h0, h2, h3, h4, h5, h6, h7⟩
  · have hk' : (k == 0) = false := by simp [hk]
    simp only [hk', Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      List.mem_range, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hl⟩, hr⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, -⟩ := h
    exact ⟨fun h0 => absurd h0 hk, fun _ => ⟨hp, hl, hr⟩, h2, h3, h4, h5, h6, h7⟩

section Pts

variable {n : Nat} {G : Array (Array Nat)} {Lm : Nat → Nat → Nat} {m : Nat} {E : EnumK}
  {par lab : Array Nat}

private theorem chkAll_of_chkAllK_pts (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hpl : ∀ k < E.N, k ≠ 0 → E.par k < k ∧ E.lab k < m)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k)
    {q : Nat} (hq : q < n) : ∀ k < E.N, (ptsArr G par lab E.N q).getD k 0 < n ∧
      (ptsArr G par lab E.N q).getD k 0 =
        if k = 0 then q else Lm (E.lab k) ((ptsArr G par lab E.N q).getD (E.par k) 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [chkAll_of_chkAllK_ptsArr_getD G par lab q hk]
    by_cases h0 : k = 0
    · simp [h0, hq]
    · obtain ⟨hp, hl⟩ := hpl k hk h0
      rw [hpar k hk, hlab k hk, ← chkAll_of_chkAllK_ptsArr_getD_le G par lab q hp E.N hk.le]
      have ih' := (ih (E.par k) hp (by omega)).1
      have := chkAll_of_chkAllK_img (hG _ hl) ih'
      simp only [h0, if_false]
      exact ⟨by rw [this.1]; exact this.2, this.1⟩

private theorem chkAll_of_chkAllK_ePts (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hpl : ∀ k < E.N, k ≠ 0 → E.par k < k ∧ E.lab k < m)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k)
    {qs : List Nat} (hqs : ∀ q ∈ qs, q < n) :
    ∀ k < E.N, ∀ f, k < f → DcK.ePts E Lm f k qs = qs.map (fun q => (ptsArr G par lab E.N q).getD k 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    by_cases h0 : k = 0
    · subst h0
      simp only [DcK.ePts, beq_self_eq_true, if_true]
      symm
      refine (List.map_congr_left fun q hq => ?_).trans (List.map_id' qs)
      rw [(chkAll_of_chkAllK_pts hG hpl hpar hlab (hqs q hq) 0 hk).2]
      simp
    · have hk' : (k == 0) = false := by simp [h0]
      obtain ⟨hp, _⟩ := hpl k hk h0
      simp only [DcK.ePts, hk', Bool.false_eq_true, if_false]
      rw [ih (E.par k) hp (by omega) f (by omega), List.map_map]
      refine List.map_congr_left fun q hq => ?_
      rw [(chkAll_of_chkAllK_pts hG hpl hpar hlab (hqs q hq) k hk).2]
      simp [h0]

end Pts

section Keys

variable {n : Nat} {B : List Nat} {Lm : Nat → Nat → Nat} {m : Nat} {E : EnumK}

private theorem chkAll_of_chkAllK_skey_lt (he : ∀ k < E.N, elemK n B Lm m E k = true) {a : Nat} :
    ∀ b, a < b → b < E.N → E.skey n B.length a < E.skey n B.length b := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base =>
    intro hb
    rcases (chkAll_of_chkAllK_elemK (he a (by omega))).2.2.2.2.2.2.2 with h | h
    · omega
    · exact h
  | succ b hab ih =>
    intro hb
    refine Nat.lt_trans (ih (by omega)) ?_
    rcases (chkAll_of_chkAllK_elemK (he b (by omega))).2.2.2.2.2.2.2 with h | h
    · omega
    · exact h

private theorem chkAll_of_chkAllK_skey_le (he : ∀ k < E.N, elemK n B Lm m E k = true) {a b : Nat}
    (hab : a ≤ b) (hb : b < E.N) : E.skey n B.length a ≤ E.skey n B.length b := by
  rcases Nat.eq_or_lt_of_le hab with rfl | h
  · exact Nat.le_refl _
  · exact (chkAll_of_chkAllK_skey_lt he b h hb).le

private theorem chkAll_of_chkAllK_key_skey (he : ∀ k < E.N, elemK n B Lm m E k = true) {k : Nat}
    (hk : k < E.N) : E.key n B.length k = E.skey n B.length (E.sinv k) ∧ E.sinv k < E.N := by
  have h := chkAll_of_chkAllK_elemK (he k hk)
  refine ⟨?_, h.2.2.2.2.2.1⟩
  unfold EnumK.skey
  rw [h.2.2.2.2.2.2.1]

private theorem chkAll_of_chkAllK_key_inj (he : ∀ k < E.N, elemK n B Lm m E k = true) {k k' : Nat}
    (hk : k < E.N) (hk' : k' < E.N) (h : E.key n B.length k = E.key n B.length k') : k = k' := by
  obtain ⟨e1, l1⟩ := chkAll_of_chkAllK_key_skey he hk
  obtain ⟨e2, l2⟩ := chkAll_of_chkAllK_key_skey he hk'
  rw [e1, e2] at h
  rcases Nat.lt_trichotomy (E.sinv k) (E.sinv k') with c | c | c
  · exact absurd h (Nat.ne_of_lt (chkAll_of_chkAllK_skey_lt he _ c l2))
  · have := (chkAll_of_chkAllK_elemK (he k hk)).2.2.2.2.2.2.1
    have := (chkAll_of_chkAllK_elemK (he k' hk')).2.2.2.2.2.2.1
    rw [← (chkAll_of_chkAllK_elemK (he k hk)).2.2.2.2.2.2.1,
      ← (chkAll_of_chkAllK_elemK (he k' hk')).2.2.2.2.2.2.1, c]
  · exact absurd h.symm (Nat.ne_of_lt (chkAll_of_chkAllK_skey_lt he _ c l1))

private theorem chkAll_of_chkAllK_keys_nodup (he : ∀ k < E.N, elemK n B Lm m E k = true) :
    ((List.range E.N).map (E.key n B.length)).Nodup := by
  refine List.nodup_range.map_on fun x hx y hy h => ?_
  exact chkAll_of_chkAllK_key_inj he (List.mem_range.mp hx) (List.mem_range.mp hy) h

private theorem chkAll_of_chkAllK_memK_true (he : ∀ k < E.N, elemK n B Lm m E k = true) {x p : Nat}
    (h : memK n B.length E x p = some true) : ∃ k < E.N, E.key n B.length k = x := by
  unfold memK at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact ⟨E.sig p, (chkAll_of_chkAllK_elemK (he p hc.1)).2.2.2.1, hc.2⟩
  · split at h <;> simp at h

private theorem chkAll_of_chkAllK_memK_false (he : ∀ k < E.N, elemK n B Lm m E k = true) {x p : Nat}
    (h : memK n B.length E x p = some false) : ∀ k < E.N, E.key n B.length k ≠ x := by
  unfold memK at h
  split at h
  · simp at h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      intro k hk hx
      obtain ⟨e, l⟩ := chkAll_of_chkAllK_key_skey he hk
      rw [e] at hx
      by_cases hq : E.sinv k < p
      · rcases h1 with h1 | h1
        · omega
        · have := chkAll_of_chkAllK_skey_le he (a := E.sinv k) (b := p - 1) (by omega) (by omega)
          omega
      · rcases h2 with h2 | h2
        · omega
        · have := chkAll_of_chkAllK_skey_le he (a := p) (b := E.sinv k) (by omega) l
          omega
    · simp at h

end Keys

section Rec

variable {n : Nat} {B : List Nat} {G : Array (Array Nat)} {Lm : Nat → Nat → Nat} {m : Nat}
  {E : EnumK} {par lab : Array Nat}

private theorem chkAll_of_chkAllK_hpl (he : ∀ k < E.N, elemK n B Lm m E k = true) :
    ∀ k < E.N, k ≠ 0 → E.par k < k ∧ E.lab k < m := fun k hk h0 =>
  let h := (chkAll_of_chkAllK_elemK (he k hk)).2.1 h0
  ⟨h.1, h.2.1⟩

private theorem chkAll_of_chkAllK_rowOf (P : Nat → Array Nat) (k : Nat) :
    rowOf (B.map P) k = B.map fun b => (P b).getD k 0 := by
  simp [rowOf, List.map_map, Function.comp_def]

private theorem chkAll_of_chkAllK_rec_row (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    ∀ k < E.N, rowOf (B.map (ptsArr G par lab E.N)) k = E.row k := by
  have hpl := chkAll_of_chkAllK_hpl he
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [chkAll_of_chkAllK_rowOf]
    by_cases h0 : k = 0
    · subst h0
      rw [(chkAll_of_chkAllK_elemK (he 0 hk)).1 rfl]
      refine (List.map_congr_left fun q hq => ?_).trans (List.map_id' B)
      rw [(chkAll_of_chkAllK_pts hG hpl hpar hlab (hB q hq) 0 hk).2]
      simp
    · obtain ⟨hp, -, hr⟩ := (chkAll_of_chkAllK_elemK (he k hk)).2.1 h0
      rw [hr, ← ih (E.par k) hp (by omega), chkAll_of_chkAllK_rowOf, List.map_map]
      refine List.map_congr_left fun q hq => ?_
      rw [(chkAll_of_chkAllK_pts hG hpl hpar hlab (hB q hq) k hk).2]
      simp [h0]

private theorem chkAll_of_chkAllK_rec_lt (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    ∀ k < E.N, ∀ x ∈ E.row k, x < n := by
  intro k hk x hx
  rw [← chkAll_of_chkAllK_rec_row hG hB he hpar hlab k hk, chkAll_of_chkAllK_rowOf] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact (chkAll_of_chkAllK_pts hG (chkAll_of_chkAllK_hpl he) hpar hlab (hB b hb) k hk).1

private theorem chkAll_of_chkAllK_rec_keys (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    rowKeys n B G par lab E.N = (List.range E.N).map (E.key n B.length) := by
  unfold rowKeys
  refine List.map_congr_left fun k hk => ?_
  have := chkAll_of_chkAllK_rec_row hG hB he hpar hlab k (List.mem_range.mp hk)
  unfold rowOf at this
  simp only [EnumK.key, this]

private theorem chkAll_of_chkAllK_rec_enumOK (hGs : G.size = m)
    (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    enumOK E.N G par lab = true := by
  unfold enumOK
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq]
  intro k hk
  by_cases h0 : k = 0
  · exact Or.inl h0
  · have := chkAll_of_chkAllK_hpl he k hk h0
    rw [hpar k hk, hlab k hk, hGs]
    exact Or.inr this

private theorem chkAll_of_chkAllK_rec_distinct (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    distinctNat (rowKeys n B G par lab E.N) = true := by
  rw [chkAll_of_chkAllK_rec_keys hG hB he hpar hlab]
  exact chkAll_of_chkAllK_distinctNat (chkAll_of_chkAllK_keys_nodup he)

private theorem chkAll_of_chkAllK_rec_closed (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hGs : G.size = m) (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    closedOK n B G par lab E.N = true := by
  have hrow := chkAll_of_chkAllK_rec_row hG hB he hpar hlab
  have hlt := chkAll_of_chkAllK_rec_lt hG hB he hpar hlab
  unfold closedOK
  have hM : ((List.range E.N).map fun k =>
      (keyNat n B.length (rowOf (B.map (ptsArr G par lab E.N)) k), k)) =
      (List.range E.N).map fun k => (E.key n B.length k, k) := by
    refine List.map_congr_left fun k hk => ?_
    rw [hrow k (List.mem_range.mp hk)]; rfl
  simp only []
  rw [hM]
  have hdist : ((List.range E.N).map fun k => (E.key n B.length k, k)).Pairwise
      (fun a b => (a.1 == b.1) = false) := by
    rw [List.pairwise_map]
    refine List.nodup_range.imp_of_mem fun {a b} ha hb hab => ?_
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    exact hab (chkAll_of_chkAllK_key_inj he (List.mem_range.mp ha) (List.mem_range.mp hb) h)
  simp only [List.all_eq_true, List.mem_range]
  intro k hk t ht
  rw [hGs] at ht
  obtain ⟨htg, hrt⟩ := (chkAll_of_chkAllK_elemK (he k hk)).2.2.1 t ht
  have hmap : (rowOf (B.map (ptsArr G par lab E.N)) k).map (img (G.getD t #[])) =
      E.row (E.tgt k t) := by
    rw [hrow k hk, ← hrt]
    exact List.map_congr_left fun x hx => (chkAll_of_chkAllK_img (hG t ht) (hlt k hk x hx)).1
  have hget : (Std.HashMap.ofList ((List.range E.N).map fun k => (E.key n B.length k, k))).get?
      (keyNat n B.length (E.row (E.tgt k t))) = some (E.tgt k t) := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_ofList_of_mem (k := E.key n B.length (E.tgt k t)) (by simp [EnumK.key])
      hdist (List.mem_map.mpr ⟨E.tgt k t, List.mem_range.mpr htg, rfl⟩)
  unfold closedStep
  rw [hmap, hget]
  simp [htg, hrow _ htg]

end Rec

section Checks

variable {D : DcData} {K : DcK}

private theorem chkAll_of_chkAllK_parts {I H : List Nat} (h : chkAllK K I H = true) :
    K.invOK = true ∧ K.basicOK = true ∧ K.labOK = true ∧ K.distOK I = true ∧
      K.edgesOK = true ∧ K.vsOK = true ∧ K.hitOK H = true ∧ K.massOK H = true := by
  simp only [chkAllK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

private theorem chkAll_of_chkAllK_basic_parts (h : K.basicOK = true) :
    (∀ b ∈ K.B, b < K.n) ∧ 0 < K.R.N ∧ (∀ w ∈ K.reps.toList, ∀ l ∈ w, l < 4) ∧
      K.c0 < K.reps.size ∧ (∀ j ∈ K.reach, j < K.reps.size) ∧ K.Vs.length ≤ 3 ∧
      (∀ V ∈ K.Vs, ∀ w ∈ V.1, ∀ l ∈ w, l < 4) := by
  simp only [DcK.basicOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

private theorem chkAll_of_chkAllK_reps_lt (hb : K.basicOK = true) (j : Nat) :
    ∀ l ∈ K.reps.getD j [], l < 4 := by
  intro l hl
  by_cases hj : j < K.reps.size
  · have hm : K.reps.getD j [] ∈ K.reps.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hj)
    exact (chkAll_of_chkAllK_basic_parts hb).2.2.1 _ hm l hl
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hl
    simp at hl

private theorem chkAll_of_chkAllK_invW_lt {w : List Nat} (hw : ∀ l ∈ w, l < 4) :
    ∀ l ∈ invW w, l < 4 := by
  intro l hl
  simp only [invW, List.mem_reverse, List.mem_map] at hl
  obtain ⟨a, ha, rfl⟩ := hl
  have := hw a ha
  unfold invL; split <;> omega

private theorem chkAll_of_chkAllK_word (hr : Rel D K) {w : List Nat} (hw : ∀ l ∈ w, l < 4) :
    ∀ p < K.n, evalW D.AB w p = wordF K.ab w p ∧ wordF K.ab w p < K.n :=
  evalW_eq w fun l hl => hr.ab l (hw l hl)

private theorem chkAll_of_chkAllK_tab (hr : Rel D K) {w : List Nat} (hw : ∀ l ∈ w, l < 4) :
    Good K.n (tabW D.n D.AB w) (wordF K.ab w) := by
  rw [hr.n_eq]; exact good_tabW fun l hl => hr.ab l (hw l hl)

private theorem chkAll_of_chkAllK_chkInv (hr : Rel D K) (h : K.invOK = true) : D.chkInv = true := by
  unfold DcData.chkInv
  unfold DcK.invOK at h
  rw [hr.ab_size, hr.rti_size, hr.rt_size, hr.n_eq]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h ⊢
  refine ⟨⟨⟨trivial, trivial⟩, fun q hq => ⟨?_, ?_⟩⟩, fun t ht q hq => ?_⟩
  · have e0 := chkAll_of_chkAllK_img (hr.ab 0 (by omega)) hq
    rw [e0.1, (chkAll_of_chkAllK_img (hr.ab 2 (by omega)) e0.2).1]
    exact (h q hq).1.1
  · have e0 := chkAll_of_chkAllK_img (hr.ab 1 (by omega)) hq
    rw [e0.1, (chkAll_of_chkAllK_img (hr.ab 3 (by omega)) e0.2).1]
    exact (h q hq).1.2
  · have e0 := chkAll_of_chkAllK_img (hr.rt t ht) hq
    rw [e0.1, (chkAll_of_chkAllK_img (hr.rti t ht) e0.2).1]
    exact (h q hq).2 t ht

private theorem chkAll_of_chkAllK_chkBasic (hr : Rel D K) (h : K.basicOK = true) : D.chkBasic = true := by
  obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := chkAll_of_chkAllK_basic_parts h
  unfold DcData.chkBasic
  rw [hr.B_eq, hr.n_eq, hr.ab_size, hr.rt_size, hr.rti_size, hr.reps_eq, hr.c0_eq, hr.reach_eq,
    hr.Vs.length_eq, fa_all (Q := fun V => V.1.all fun w => w.all fun l => decide (l < 4))
      (fun a b r => by rw [r.1]) hr.Vs, ← Array.all_toList]
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_self_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h1, trivial⟩, trivial⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

private theorem chkAll_of_chkAllK_chkR (hr : Rel D K) (hb : K.basicOK = true)
    (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true) : D.chkR = true := by
  have hB := (chkAll_of_chkAllK_basic_parts hb).1
  unfold DcData.chkR DcData.rKeys
  rw [hr.NR_eq, hr.n_eq, hr.B_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, (chkAll_of_chkAllK_basic_parts hb).2.1⟩
  · exact chkAll_of_chkAllK_rec_enumOK hr.rt_size hR hr.rpar hr.rlab
  · exact chkAll_of_chkAllK_rec_distinct hr.rt hB hR hr.rpar hr.rlab
  · exact chkAll_of_chkAllK_rec_closed hr.rt hr.rt_size hB hR hr.rpar hr.rlab

private theorem chkAll_of_chkAllK_chkLab (hr : Rel D K) (h : K.labOK = true) : D.chkLab = true := by
  unfold DcData.chkLab labOK
  unfold DcK.labOK at h
  simp only [Array.all_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h ⊢
  intro t ht q hq
  rw [hr.rt_size] at ht
  rw [hr.n_eq] at hq
  have e : D.RT[t] = D.RT.getD t #[] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (hr.rt_size ▸ ht)]
  rw [e]
  have e0 := chkAll_of_chkAllK_img (hr.rt t ht) hq
  rw [e0.1, hr.lb _ e0.2, hr.lb q hq]
  exact h t ht q hq

private theorem chkAll_of_chkAllK_dcInv (hr : Rel D K) {w : List Nat} (hw : ∀ l ∈ w, l < 4) :
    dcInv D.n D.lb (tabW D.n D.AB w) =
      sumK (fun q => wt (K.lb q) (K.lb (wordF K.ab w q))) (List.range K.n) 0 := by
  rw [chkAll_of_chkAllK_sumK, Nat.zero_add]
  unfold dcInv
  rw [hr.n_eq]
  refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
  have hq := List.mem_range.mp hq
  have e := chkAll_of_chkAllK_img (good_tabW (n := K.n) fun l hl => hr.ab l (hw l hl)) hq
  rw [e.1, hr.lb q hq, hr.lb _ e.2]

private theorem chkAll_of_chkAllK_list_getD {l : List Nat} {i : Nat} (h : i < l.length) :
    l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem chkAll_of_chkAllK_chkDist (hr : Rel D K) (hb : K.basicOK = true) {I : List Nat}
    (hd : K.distOK I = true) : D.chkDist = true := by
  simp only [DcK.distOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hd
  obtain ⟨⟨hlen, hinv⟩, hne⟩ := hd
  have hnd := chkAll_of_chkAllK_allNe hne
  have hI : ∀ i < K.reps.size,
      (((List.range K.reps.size).map fun j => dcInv D.n D.lb (D.X j)).toArray).getD i 0 =
        I.getD i 0 := by
    intro i hi
    rw [← hinv i hi]
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    unfold DcData.X
    rw [hr.reps_eq, chkAll_of_chkAllK_dcInv hr (chkAll_of_chkAllK_reps_lt hb i)]
    rfl
  unfold DcData.chkDist DcData.chkDistWith
  simp only []
  rw [hr.reps_eq]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
  intro i hi j hj
  by_cases hji : j ≤ i
  · exact Or.inl (Or.inl hji)
  · refine Or.inl (Or.inr ?_)
    rw [hI i hi, hI j hj, bne_iff_ne, ne_eq,
      chkAll_of_chkAllK_list_getD (by omega), chkAll_of_chkAllK_list_getD (by omega),
      hnd.getElem_inj_iff]
    omega

private theorem chkAll_of_chkAllK_edgeL (hr : Rel D K) {w : List Nat} (hw : ∀ l ∈ w, l < 4) {l p : Nat}
    (hl : l < K.nr + K.nr + 2) (hp : p < K.n) :
    edgeLetter D.RT D.RTi D.AB w l p = K.edgeL w l p ∧ K.edgeL w l p < K.n := by
  unfold edgeLetter DcK.edgeL
  rw [hr.rt_size, hr.rti_size]
  by_cases h1 : l < K.nr
  · simp only [h1, if_true]
    exact chkAll_of_chkAllK_img (hr.rt l h1) hp
  · by_cases h2 : l < K.nr + K.nr
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
      exact chkAll_of_chkAllK_img (hr.rti (l - K.nr) (by omega)) hp
    · by_cases h3 : l = K.nr + K.nr
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, if_pos h3, if_pos h3]
        exact chkAll_of_chkAllK_word hr hw p hp
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, if_neg h3, if_neg h3]
        exact chkAll_of_chkAllK_word hr (chkAll_of_chkAllK_invW_lt hw) p hp

private theorem chkAll_of_chkAllK_evalE (hr : Rel D K) {w : List Nat} (hw : ∀ l ∈ w, l < 4) :
    ∀ e : List Nat, (∀ l ∈ e, l < K.nr + K.nr + 2) → ∀ p < K.n,
      evalE D.RT D.RTi D.AB w e p = K.evalE w e p ∧ K.evalE w e p < K.n
  | [], _, p, hp => ⟨rfl, hp⟩
  | l :: e, he, p, hp => by
    obtain ⟨e1, h1⟩ := chkAll_of_chkAllK_evalE hr hw e
      (fun l' h => he l' (List.mem_cons_of_mem _ h)) p hp
    have a1 : evalE D.RT D.RTi D.AB w (l :: e) p =
      edgeLetter D.RT D.RTi D.AB w l (evalE D.RT D.RTi D.AB w e p) := rfl
    have a2 : K.evalE w (l :: e) p = K.edgeL w l (K.evalE w e p) := rfl
    rw [a1, a2, e1]
    exact chkAll_of_chkAllK_edgeL hr hw (he l List.mem_cons_self) h1

private theorem chkAll_of_chkAllK_chkEdges (hr : Rel D K) (hb : K.basicOK = true)
    (h : K.edgesOK = true) : D.chkEdges = true := by
  have hB := (chkAll_of_chkAllK_basic_parts hb).1
  unfold DcK.edgesOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hed, hin⟩, hout⟩, hne⟩ := h
  unfold DcData.chkEdges
  rw [hr.edges_eq, hr.reps_eq, hr.c0_eq, hr.inEdge_eq, hr.dIn_eq, hr.reach_eq, hr.outEdge_eq,
    hr.dOut_eq, hin, hout, chkAll_of_chkAllK_distinctNat (chkAll_of_chkAllK_allNe hne),
    ← Array.all_toList]
  simp only [Bool.and_true]
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hed ⊢
  intro ed hm
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hed ed hm
  unfold edgeOK
  rw [hr.rt_size, hr.rti_size, hr.B_eq]
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, fun b hbm => ?_⟩
  rw [(chkAll_of_chkAllK_word hr (chkAll_of_chkAllK_reps_lt hb _) b (hB b hbm)).1,
    (chkAll_of_chkAllK_evalE hr (chkAll_of_chkAllK_reps_lt hb _) _ h3 b (hB b hbm)).1]
  exact h4 b hbm

private abbrev chkAll_of_chkAllK_VRel (K : DcK) (V : List (List Nat) × Array Nat × Array Nat × Nat)
    (W : List (List Nat) × (Nat → Nat → Nat) × EnumK) : Prop :=
  V.1 = W.1 ∧ V.2.2.2 = W.2.2.N ∧
    (∀ i < V.1.length, ∀ p < K.n, wordF K.ab (V.1.getD i []) p = W.2.1 i p) ∧
    ∀ k < W.2.2.N, V.2.1.getD k 0 = W.2.2.par k ∧ V.2.2.1.getD k 0 = W.2.2.lab k

private theorem chkAll_of_chkAllK_VG_size (hr : Rel D K) (ws : List (List Nat)) :
    (D.VG ws).size = K.nr + ws.length := by
  simp [DcData.VG, hr.rt_size]

private theorem chkAll_of_chkAllK_VG_good (hr : Rel D K) {V : List (List Nat) × Array Nat × Array Nat × Nat}
    {W : List (List Nat) × (Nat → Nat → Nat) × EnumK} (hVW : chkAll_of_chkAllK_VRel K V W)
    (hl : ∀ w ∈ V.1, ∀ l ∈ w, l < 4) :
    ∀ t < K.nr + V.1.length, Good K.n ((D.VG V.1).getD t #[]) (K.vg W.2.1 t) := by
  intro t ht
  unfold DcData.VG DcK.vg
  by_cases h1 : t < K.nr
  · rw [if_pos h1]
    have e : (D.RT ++ (V.1.map (tabW D.n D.AB)).toArray).getD t #[] = D.RT.getD t #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by rw [hr.rt_size]; exact h1),
        ← Array.getD_eq_getD_getElem?]
    rw [e]
    exact hr.rt t h1
  · rw [if_neg h1]
    have hi : t - K.nr < V.1.length := by omega
    have e : (D.RT ++ (V.1.map (tabW D.n D.AB)).toArray).getD t #[] =
        tabW D.n D.AB (V.1.getD (t - K.nr) []) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by rw [hr.rt_size]; omega),
        hr.rt_size]
      simp [List.getD_eq_getElem?_getD, hi]
    rw [e]
    have hw : ∀ l ∈ V.1.getD (t - K.nr) [], l < 4 := by
      intro l hlm
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hlm
      exact hl _ (List.getElem_mem hi) l hlm
    exact chkAll_of_chkAllK_good_congr (chkAll_of_chkAllK_tab hr hw) (hVW.2.2.1 _ hi)

private theorem chkAll_of_chkAllK_V_keys (hr : Rel D K) (hb : K.basicOK = true)
    {V : List (List Nat) × Array Nat × Array Nat × Nat}
    {W : List (List Nat) × (Nat → Nat → Nat) × EnumK} (hVW : chkAll_of_chkAllK_VRel K V W)
    (hl : ∀ w ∈ V.1, ∀ l ∈ w, l < 4)
    (he : ∀ k < W.2.2.N, elemK K.n K.B (K.vg W.2.1) (K.nr + V.1.length) W.2.2 k = true) :
    D.vKeys V = (List.range W.2.2.N).map (W.2.2.key K.n K.B.length) := by
  unfold DcData.vKeys
  rw [hVW.2.1, hr.n_eq, hr.B_eq]
  exact chkAll_of_chkAllK_rec_keys (chkAll_of_chkAllK_VG_good hr hVW hl)
    (chkAll_of_chkAllK_basic_parts hb).1 he (fun k hk => (hVW.2.2.2 k hk).1)
    (fun k hk => (hVW.2.2.2 k hk).2)

private theorem chkAll_of_chkAllK_V_rel (hr : Rel D K) (hb : K.basicOK = true) :
    ∀ V ∈ D.Vs, ∃ W ∈ K.Vs, chkAll_of_chkAllK_VRel K V W ∧ ∀ w ∈ V.1, ∀ l ∈ w, l < 4 := by
  intro V hV
  obtain ⟨W, hW, hVW⟩ := chkAll_of_chkAllK_forall₂_mem hr.Vs V hV
  refine ⟨W, hW, hVW, ?_⟩
  rw [hVW.1]
  exact (chkAll_of_chkAllK_basic_parts hb).2.2.2.2.2.2 W hW

private theorem chkAll_of_chkAllK_chkVs (hr : Rel D K) (hb : K.basicOK = true) (hvs : K.vsOK = true)
    (hV : ∀ V ∈ K.Vs, ∀ k < V.2.2.N,
      elemK K.n K.B (K.vg V.2.1) (K.nr + V.1.length) V.2.2 k = true) : D.chkVs = true := by
  unfold DcData.chkVs
  rw [List.all_eq_true]
  intro V hVm
  obtain ⟨W, hW, hVW, hl⟩ := chkAll_of_chkAllK_V_rel hr hb V hVm
  have he : ∀ k < W.2.2.N, elemK K.n K.B (K.vg W.2.1) (K.nr + V.1.length) W.2.2 k = true := by
    rw [hVW.1]; exact hV W hW
  have hB := (chkAll_of_chkAllK_basic_parts hb).1
  have hG := chkAll_of_chkAllK_VG_good hr hVW hl
  have hGs := chkAll_of_chkAllK_VG_size hr V.1
  have hpar : ∀ k < W.2.2.N, V.2.1.getD k 0 = W.2.2.par k := fun k hk => (hVW.2.2.2 k hk).1
  have hlab : ∀ k < W.2.2.N, V.2.2.1.getD k 0 = W.2.2.lab k := fun k hk => (hVW.2.2.2 k hk).2
  simp only [DcK.vsOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hvs
  rw [chkAll_of_chkAllK_V_keys hr hb hVW hl he, hVW.2.1, hr.n_eq, hr.B_eq, hr.order_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, (hvs W hW).1⟩, (hvs W hW).2⟩
  · exact chkAll_of_chkAllK_rec_enumOK hGs he hpar hlab
  · exact chkAll_of_chkAllK_distinctNat (chkAll_of_chkAllK_keys_nodup he)
  · exact chkAll_of_chkAllK_rec_closed hG hGs hB he hpar hlab

private theorem chkAll_of_chkAllK_rKeys (hr : Rel D K) (hb : K.basicOK = true)
    (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true) :
    D.rKeys = (List.range K.R.N).map (K.R.key K.n K.B.length) := by
  unfold DcData.rKeys
  rw [hr.NR_eq, hr.n_eq, hr.B_eq]
  exact chkAll_of_chkAllK_rec_keys hr.rt (chkAll_of_chkAllK_basic_parts hb).1 hR hr.rpar hr.rlab

private theorem chkAll_of_chkAllK_conjKeys (hr : Rel D K) (hb : K.basicOK = true)
    (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true) (j : Nat) :
    conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi j) (D.X j) =
      (List.range K.R.N).map (K.conjKey j) := by
  have hB := (chkAll_of_chkAllK_basic_parts hb).1
  have hw := chkAll_of_chkAllK_reps_lt hb j
  have hX := chkAll_of_chkAllK_tab hr hw
  have hXi := chkAll_of_chkAllK_tab hr (chkAll_of_chkAllK_invW_lt hw)
  have hpl := chkAll_of_chkAllK_hpl hR
  rw [hr.n_eq] at hX hXi
  unfold conjKeys DcData.X DcData.Xi
  rw [hr.reps_eq, hr.NR_eq, hr.B_eq]
  refine List.map_congr_left fun k hk => ?_
  have hk := List.mem_range.mp hk
  unfold DcK.conjKey
  have hqs : ∀ q ∈ K.B.map (wordF K.ab (K.reps.getD j [])), q < K.n := by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
    exact (chkAll_of_chkAllK_img hX (hB b hb)).2
  rw [chkAll_of_chkAllK_ePts hr.rt hpl hr.rpar hr.rlab hqs k hk (k + 1) (Nat.lt_succ_self k),
    hr.n_eq, List.map_map, List.map_map, List.map_map]
  refine congrArg (keyNat K.n K.B.length) (List.map_congr_left fun b hbm => ?_)
  have e1 := chkAll_of_chkAllK_img hX (hB b hbm)
  have e2 := (chkAll_of_chkAllK_pts hr.rt hpl hr.rpar hr.rlab e1.2 k hk).1
  simp only [Function.comp_apply]
  rw [e1.1, (chkAll_of_chkAllK_img hXi e2).1]

private theorem chkAll_of_chkAllK_hitCount (hr : Rel D K) (hb : K.basicOK = true)
    (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true) {H : List Nat}
    (hh : K.hitOK H = true) {j : Nat} (hj : j < K.reps.size) :
    hitCount D.rSet (conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi j) (D.X j)) = H.getD j 0 := by
  simp only [DcK.hitOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hh
  have hc := hh.2 j hj
  unfold DcK.hit at hc
  rw [chkAll_of_chkAllK_cntK _ (fun k => D.rSet.contains (K.conjKey j k)) _ 0 _ ?_ hc,
    Nat.zero_add]
  · unfold hitCount
    rw [chkAll_of_chkAllK_conjKeys hr hb hR, List.filter_map, List.length_map]
    rfl
  · intro k _
    unfold DcData.rSet
    rw [Std.HashSet.contains_ofList, chkAll_of_chkAllK_rKeys hr hb hR]
    constructor
    · intro hm
      obtain ⟨k', hk', e⟩ := chkAll_of_chkAllK_memK_true hR hm
      exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨k', List.mem_range.mpr hk', e⟩)
    · intro hm
      have hf := chkAll_of_chkAllK_memK_false hR hm
      cases hc : ((List.range K.R.N).map (K.R.key K.n K.B.length)).contains (K.conjKey j k)
      · rfl
      · obtain ⟨k', hk', e⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
        exact absurd e (hf k' (List.mem_range.mp hk'))

private theorem chkAll_of_chkAllK_map_range (f : Nat → Nat) (l : List Nat) :
    (List.range l.length).map (fun j => f (l.getD j 0)) = l.map f := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [chkAll_of_chkAllK_list_getD (by simpa using h1)]

private theorem chkAll_of_chkAllK_filter_le {p q : Nat → Bool} :
    ∀ l : List Nat, (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | x :: l, h => by
    have ih := chkAll_of_chkAllK_filter_le l fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx := h x List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

private theorem chkAll_of_chkAllK_unionLB_mono : ∀ (kss : List (List Nat)) (acc : Nat × Std.HashSet Nat),
    acc.1 ≤ (kss.foldl (fun (acc : Nat × Std.HashSet Nat) ks =>
      (acc.1 + (ks.filter fun k => !acc.2.contains k).length, acc.2.insertMany ks)) acc).1
  | [], _ => Nat.le_refl _
  | ks :: kss, acc => by
    rw [List.foldl_cons]
    have := chkAll_of_chkAllK_unionLB_mono kss
      (acc.1 + (ks.filter fun k => !acc.2.contains k).length, acc.2.insertMany ks)
    exact Nat.le_trans (Nat.le_add_right _ _) this

private theorem chkAll_of_chkAllK_ulb (hr : Rel D K) (hb : K.basicOK = true)
    (hV : ∀ V ∈ K.Vs, ∀ k < V.2.2.N,
      elemK K.n K.B (K.vg V.2.1) (K.nr + V.1.length) V.2.2 k = true) :
    K.ulb ≤ unionLB (D.Vs.map D.vKeys) := by
  have hl := (chkAll_of_chkAllK_basic_parts hb).2.2.2.2.2.2
  have hF := hr.Vs
  unfold DcK.ulb
  generalize D.Vs = DV at hF ⊢
  generalize K.Vs = KV at hF hV hl ⊢
  have hkeys : ∀ {V W}, chkAll_of_chkAllK_VRel K V W → W ∈ KV →
      D.vKeys V = (List.range W.2.2.N).map (W.2.2.key K.n K.B.length) := by
    intro V W hVW hW
    refine chkAll_of_chkAllK_V_keys hr hb hVW (hVW.1 ▸ hl W hW) ?_
    rw [hVW.1]; exact hV W hW
  rcases hF with _ | @⟨V0, W0, DV', KV', r0, hF⟩
  · exact Nat.zero_le _
  · have hk0 := hkeys r0 List.mem_cons_self
    rcases hF with _ | @⟨V1, W1, DV'', KV'', r1, _⟩
    · simp only [unionLB, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, hk0,
        Std.HashSet.contains_empty, Bool.not_false, List.filter_true, List.length_map,
        List.length_range, Nat.zero_add]
      exact Nat.le_refl _
    · have hk1 := hkeys r1 (List.mem_cons_of_mem _ List.mem_cons_self)
      have he0 : ∀ k < W0.2.2.N,
          elemK K.n K.B (K.vg W0.2.1) (K.nr + W0.1.length) W0.2.2 k = true :=
        hV W0 List.mem_cons_self
      unfold unionLB
      simp only [List.map_cons, List.foldl_cons]
      refine Nat.le_trans ?_ (chkAll_of_chkAllK_unionLB_mono _ _)
      simp only [hk0, hk1, Std.HashSet.contains_empty, Bool.not_false, List.filter_true,
        List.length_map, List.length_range, Nat.zero_add, Std.HashSet.contains_insertMany_list,
        Bool.false_or, List.filter_map, chkAll_of_chkAllK_cntB, Function.comp_def]
      refine Nat.add_le_add_left (chkAll_of_chkAllK_filter_le _ fun k _ hk => ?_) _
      simp only [beq_iff_eq] at hk
      have hf := chkAll_of_chkAllK_memK_false he0 hk
      cases hc : ((List.range W0.2.2.N).map (W0.2.2.key K.n K.B.length)).contains
          (W1.2.2.key K.n K.B.length k)
      · rfl
      · obtain ⟨k', hk', e⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
        exact absurd e (hf k' (List.mem_range.mp hk'))

private theorem chkAll_of_chkAllK_chkMass (hr : Rel D K) (hb : K.basicOK = true)
    (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true)
    (hV : ∀ V ∈ K.Vs, ∀ k < V.2.2.N,
      elemK K.n K.B (K.vg V.2.1) (K.nr + V.1.length) V.2.2 k = true) {H : List Nat}
    (hh : K.hitOK H = true) (hm : K.massOK H = true) : D.chkMass = true := by
  have hlen : H.length = K.reps.size := by
    simp only [DcK.hitOK, Bool.and_eq_true, beq_iff_eq] at hh; exact hh.1
  have hms : ∀ j < K.reps.size, D.massWith D.rSet j = K.R.N * (K.R.N / H.getD j 0) := by
    intro j hj
    unfold DcData.massWith
    rw [chkAll_of_chkAllK_hitCount hr hb hR hh hj, hr.NR_eq]
  have hmsg : ∀ j < K.reps.size,
      (((List.range D.reps.size).map (D.massWith D.rSet)).toArray).getD j 0 =
        K.R.N * (K.R.N / H.getD j 0) := by
    intro j hj
    rw [← hms j hj, hr.reps_eq]
    simp [Array.getD_eq_getD_getElem?, hj]
  have hreach : (D.reach.map fun j =>
      (((List.range D.reps.size).map (D.massWith D.rSet)).toArray).getD j 0).sum =
      (K.reach.map fun j => K.R.N * (K.R.N / H.getD j 0)).sum := by
    rw [hr.reach_eq]
    exact congrArg List.sum (List.map_congr_left fun j hj =>
      hmsg j ((chkAll_of_chkAllK_basic_parts hb).2.2.2.2.1 j hj))
  have htot : (((List.range D.reps.size).map (D.massWith D.rSet)).toArray).toList.sum =
      (H.map fun h => K.R.N * (K.R.N / h)).sum := by
    rw [List.toList_toArray, hr.reps_eq, ← chkAll_of_chkAllK_map_range _ H, hlen]
    exact congrArg List.sum (List.map_congr_left fun j hj => hms j (List.mem_range.mp hj))
  simp only [DcK.massOK, Bool.and_eq_true, decide_eq_true_eq] at hm
  unfold DcData.chkMass DcData.chkMassWith
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hreach, htot, hr.order_eq]
  exact ⟨hm.1, Nat.le_trans hm.2 (Nat.add_le_add_left (chkAll_of_chkAllK_ulb hr hb hV) _)⟩

private theorem chkAll_of_chkAllK_conjKeys2 (hr : Rel D K) (hb : K.basicOK = true)
    (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true) (i j : Nat) :
    conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi i) (D.X j) =
      (List.range K.R.N).map (K.conjKey2 i j) := by
  have hB := (chkAll_of_chkAllK_basic_parts hb).1
  have hX := chkAll_of_chkAllK_tab hr (chkAll_of_chkAllK_reps_lt hb j)
  have hXi := chkAll_of_chkAllK_tab hr (chkAll_of_chkAllK_invW_lt (chkAll_of_chkAllK_reps_lt hb i))
  have hpl := chkAll_of_chkAllK_hpl hR
  rw [hr.n_eq] at hX hXi
  unfold conjKeys DcData.X DcData.Xi
  rw [hr.reps_eq, hr.NR_eq, hr.B_eq]
  refine List.map_congr_left fun k hk => ?_
  have hk := List.mem_range.mp hk
  unfold DcK.conjKey2
  have hqs : ∀ q ∈ K.B.map (wordF K.ab (K.reps.getD j [])), q < K.n := by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
    exact (chkAll_of_chkAllK_img hX (hB b hb)).2
  rw [chkAll_of_chkAllK_ePts hr.rt hpl hr.rpar hr.rlab hqs k hk (k + 1) (Nat.lt_succ_self k),
    hr.n_eq, List.map_map, List.map_map, List.map_map]
  refine congrArg (keyNat K.n K.B.length) (List.map_congr_left fun b hbm => ?_)
  have e1 := chkAll_of_chkAllK_img hX (hB b hbm)
  have e2 := (chkAll_of_chkAllK_pts hr.rt hpl hr.rpar hr.rlab e1.2 k hk).1
  simp only [Function.comp_apply]
  rw [e1.1, (chkAll_of_chkAllK_img hXi e2).1]

private theorem chkAll_of_chkAllK_noHit (hr : Rel D K) (hb : K.basicOK = true)
    (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true) {i j : Nat} {P : Nat → Nat}
    (h : K.noHitK i j P = true) :
    noHit D.rSet (conjKeys D.n D.B D.RT D.rpar D.rlab D.NR (D.Xi i) (D.X j)) = true := by
  simp only [DcK.noHitK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  unfold noHit
  rw [chkAll_of_chkAllK_conjKeys2 hr hb hR, List.all_map]
  refine List.all_eq_true.2 fun k hk => ?_
  have hk := List.mem_range.mp hk
  change (!D.rSet.contains (K.conjKey2 i j k)) = true
  cases hc : D.rSet.contains (K.conjKey2 i j k)
  · rfl
  · exfalso
    unfold DcData.rSet at hc
    rw [Std.HashSet.contains_ofList, chkAll_of_chkAllK_rKeys hr hb hR] at hc
    obtain ⟨k', hk', e⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
    exact chkAll_of_chkAllK_memK_false hR (h k hk) k' (List.mem_range.mp hk') e

private theorem chkAll_of_chkAllK_chkDistN (hr : Rel D K) (hb : K.basicOK = true)
    (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true) {I : List Nat}
    {P : Nat → Nat → Nat → Nat} (hd : K.distOKN I P = true) : D.chkDist = true := by
  simp only [DcK.distOKN, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hd
  obtain ⟨⟨-, hinv⟩, hne⟩ := hd
  have hI : ∀ i < K.reps.size,
      (((List.range K.reps.size).map fun j => dcInv D.n D.lb (D.X j)).toArray).getD i 0 =
        I.getD i 0 := by
    intro i hi
    rw [← hinv i hi]
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    unfold DcData.X
    rw [hr.reps_eq, chkAll_of_chkAllK_dcInv hr (chkAll_of_chkAllK_reps_lt hb i)]
    rfl
  unfold DcData.chkDist DcData.chkDistWith
  simp only []
  rw [hr.reps_eq]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
  intro i hi j hj
  rcases hne i hi j hj with (h1 | h1) | h1
  · exact Or.inl (Or.inl h1)
  · refine Or.inl (Or.inr ?_)
    rw [hI i hi, hI j hj, bne_iff_ne]
    exact h1
  · exact Or.inr (chkAll_of_chkAllK_noHit hr hb hR h1)

end Checks

theorem chkAll_of_chkAllK {D : DcData} {K : DcK} {I H : List Nat} (hr : Rel D K)
    (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true)
    (hV : ∀ V ∈ K.Vs, ∀ k < V.2.2.N, elemK K.n K.B (K.vg V.2.1) (K.nr + V.1.length) V.2.2 k = true)
    (h : chkAllK K I H = true) : D.chkAll = true := by
  obtain ⟨hi, hb, hl, hd, he, hvs, hh, hm⟩ := chkAll_of_chkAllK_parts h
  unfold DcData.chkAll
  rw [chkAll_of_chkAllK_chkInv hr hi, chkAll_of_chkAllK_chkBasic hr hb,
    chkAll_of_chkAllK_chkR hr hb hR, chkAll_of_chkAllK_chkLab hr hl,
    chkAll_of_chkAllK_chkDist hr hb hd, chkAll_of_chkAllK_chkEdges hr hb he,
    chkAll_of_chkAllK_chkVs hr hb hvs hV, chkAll_of_chkAllK_chkMass hr hb hR hV hh hm]
  rfl

theorem chkAll_of_chkAllKN {D : DcData} {K : DcK} {I H : List Nat} {P : Nat → Nat → Nat → Nat}
    (hr : Rel D K) (hR : ∀ k < K.R.N, elemK K.n K.B K.rt K.nr K.R k = true)
    (hV : ∀ V ∈ K.Vs, ∀ k < V.2.2.N, elemK K.n K.B (K.vg V.2.1) (K.nr + V.1.length) V.2.2 k = true)
    (h : chkAllKN K I H P = true) : D.chkAll = true := by
  simp only [chkAllKN, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hi, hb⟩, hl⟩, hd⟩, he⟩, hvs⟩, hh⟩, hm⟩ := h
  unfold DcData.chkAll
  rw [chkAll_of_chkAllK_chkInv hr hi, chkAll_of_chkAllK_chkBasic hr hb,
    chkAll_of_chkAllK_chkR hr hb hR, chkAll_of_chkAllK_chkLab hr hl,
    chkAll_of_chkAllK_chkDistN hr hb hR hd, chkAll_of_chkAllK_chkEdges hr hb he,
    chkAll_of_chkAllK_chkVs hr hb hvs hV, chkAll_of_chkAllK_chkMass hr hb hR hV hh hm]
  rfl

end ChkAll

end CFSG.KC.DcK

end
