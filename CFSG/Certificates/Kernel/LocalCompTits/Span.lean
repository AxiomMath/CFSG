module

public import Certificates.Data.Kernel.LocalComp.TitsChain
public import Certificates.Data.CFSGNative.SectionRank.TitsChain
import CFSG.Certificates.Kernel.Spor.TBfsSound
import CFSG.Certificates.Kernel.Common.Loop
import Init.Data.Range.Lemmas
import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.KC.LocalComp.TitsSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.TBfs CFSG.SectionRank.Native.Tits CFSG.Sporadic.Th.Native CFSG.KC.LocalComp.Tits

private theorem xor_swap4 (a b c d : Nat) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc b c d, Nat.xor_comm b c, Nat.xor_assoc c b d,
    ← Nat.xor_assoc]

private theorem xor_left_comm' (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

private theorem xor_dup (x y a : Nat) : (x ^^^ a) ^^^ (y ^^^ a) = x ^^^ y := by
  rw [xor_swap4, Nat.xor_self, Nat.xor_zero]

private theorem xor_dup' (x a : Nat) : a ^^^ (a ^^^ x) = x := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

private theorem xorSel_zero_mask (f : Nat → Nat) : ∀ k, xorSel f 0 k = 0
  | 0 => rfl
  | k + 1 => by simp [xorSel, xorSel_zero_mask f k]

private theorem xorSel_xor (f : Nat → Nat) (m m' : Nat) :
    ∀ k, xorSel f (m ^^^ m') k = xorSel f m k ^^^ xorSel f m' k
  | 0 => by simp [xorSel]
  | k + 1 => by
    simp only [xorSel, Nat.testBit_xor, xorSel_xor f m m' k]
    cases m.testBit k <;> cases m'.testBit k <;>
      simp [xor_dup, xor_dup', Nat.xor_assoc, Nat.xor_comm, xor_left_comm']

private theorem xorSel_two_pow (f : Nat → Nat) (t : Nat) :
    ∀ k, xorSel f (2 ^ t) k = if t < k then f t else 0
  | 0 => by simp [xorSel]
  | k + 1 => by
    simp only [xorSel, Nat.testBit_two_pow, xorSel_two_pow f t k]
    by_cases e : t = k
    · subst e; simp
    · have : ¬ t = k := e
      have h2 : (t < k + 1) = (t < k) := by simp; omega
      simp [this, h2]

private inductive Span (pv : Array Nat) : Nat → Prop
  | zero : Span pv 0
  | gen (b : Nat) : b < 52 → Span pv pv[b]!
  | add {x y : Nat} : Span pv x → Span pv y → Span pv (x ^^^ y)

private theorem Span.mono {pv pv' : Array Nat} (h : ∀ b < 52, pv[b]! = 0 ∨ pv'[b]! = pv[b]!)
    {x : Nat} (hx : Span pv x) : Span pv' x := by
  induction hx with
  | zero => exact .zero
  | gen b hb =>
    rcases h b hb with e | e
    · rw [e]; exact .zero
    · rw [← e]; exact .gen b hb
  | add _ _ ih1 ih2 => exact .add ih1 ih2

private theorem Span.of_sel {pv : Array Nat} (f : Nat → Nat) (m : Nat) :
    ∀ k, (∀ t < k, Span pv (f t)) → Span pv (xorSel f m k)
  | 0, _ => .zero
  | k + 1, h => by
    simp only [xorSel]
    have ih := Span.of_sel f m k fun t ht => h t (by omega)
    split
    · exact .add ih (h k (by omega))
    · exact ih

private theorem Span.to_mask {pv : Array Nat} {x : Nat} (hx : Span pv x) :
    ∃ m, xorSel (fun b => pv[b]!) m 52 = x := by
  induction hx with
  | zero => exact ⟨0, xorSel_zero_mask _ 52⟩
  | gen b hb => exact ⟨2 ^ b, by rw [xorSel_two_pow]; simp [hb]⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨m1, e1⟩ := ih1
    obtain ⟨m2, e2⟩ := ih2
    exact ⟨m1 ^^^ m2, by rw [xorSel_xor, e1, e2]⟩

private theorem testBit_top {p b : Nat} (h1 : 2 ^ b ≤ p) (h2 : p < 2 ^ (b + 1)) :
    p.testBit b = true := by
  have hp : p ≠ 0 := by have := Nat.two_pow_pos b; omega
  rw [← (Nat.log2_eq_iff hp).2 ⟨h1, h2⟩]
  exact Nat.testBit_log2 hp

private theorem testBit_above {p b c : Nat} (h2 : p < 2 ^ (b + 1)) (hb : b < c) :
    p.testBit c = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hb))

private def PForm (pv : Array Nat) : Prop :=
  ∀ b < 52, pv[b]! = 0 ∨ (2 ^ b ≤ pv[b]! ∧ pv[b]! < 2 ^ (b + 1))

private theorem xorSel_piv {pv : Array Nat} (hf : PForm pv) (m : Nat) :
    ∀ k ≤ 52, xorSel (fun b => pv[b]!) m k < 2 ^ k ∧
      (xorSel (fun b => pv[b]!) m k ≠ 0 → pv[(xorSel (fun b => pv[b]!) m k).log2]! ≠ 0)
  | 0, _ => by simp [xorSel]
  | k + 1, hk => by
    obtain ⟨ih1, ih2⟩ := xorSel_piv hf m k (by omega)
    have hpk : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    simp only [xorSel]
    by_cases hb : m.testBit k = true
    · rw [if_pos hb]
      rcases hf k (by omega) with e | ⟨e1, e2⟩
      · simp only [e, Nat.xor_zero]
        exact ⟨by omega, ih2⟩
      · have hy : xorSel (fun b => pv[b]!) m k ^^^ pv[k]! < 2 ^ (k + 1) :=
          Nat.xor_lt_two_pow (by omega) e2
        have hbit : (xorSel (fun b => pv[b]!) m k ^^^ pv[k]!).testBit k = true := by
          rw [Nat.testBit_xor, Nat.testBit_lt_two_pow ih1, testBit_top e1 e2]; rfl
        have hge := Nat.ge_two_pow_of_testBit hbit
        have hne : xorSel (fun b => pv[b]!) m k ^^^ pv[k]! ≠ 0 := by omega
        refine ⟨hy, fun _ => ?_⟩
        have : (xorSel (fun b => pv[b]!) m k ^^^ pv[k]!).log2 = k :=
          (Nat.log2_eq_iff hne).2 ⟨hge, hy⟩
        rw [this]
        intro h0
        rw [h0] at e1
        have := Nat.two_pow_pos k
        omega
    · rw [if_neg hb]
      exact ⟨by omega, ih2⟩

private theorem pv_ne_of_rep {pv : Array Nat} (hf : PForm pv) {c : Nat} (hc : c < 52)
    (h : ∃ m, xorSel (fun b => pv[b]!) m 52 = 2 ^ c) : pv[c]! ≠ 0 := by
  obtain ⟨m, e⟩ := h
  have := (xorSel_piv hf m 52 (Nat.le_refl 52)).2
  rw [e, Nat.log2_two_pow] at this
  exact this (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos c))

private abbrev X (vs : Array Nat) (m : Nat) : Nat := xorSel (fun t => vs[t]!) m vs.size

private theorem set_get (a : Array Nat) (i j v : Nat) (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by simp; omega), getElem!_pos a j hj]
  by_cases e : i = j
  · subst e; simp
  · rw [Array.getElem_setIfInBounds_ne hj e]
    simp [e]

private def body1in (pv pm : Array Nat) (k : Nat) (s : Nat × Nat) : Id (ForInStep (Nat × Nat)) :=
  if (s.fst.testBit (51 - k) && pv[51 - k]! != 0) = true then
    pure (ForInStep.yield (s.fst ^^^ pv[51 - k]!, s.snd ^^^ pm[51 - k]!))
  else pure (ForInStep.yield (s.fst, s.snd))

private def body1 (vs : Array Nat) (t : Nat) (s : Array Nat × Array Nat) :
    Id (ForInStep (Array Nat × Array Nat)) :=
  let r := Id.run (forIn (List.range' 0 52) (vs[t]!, 2 ^ t) (body1in s.fst s.snd))
  if (r.fst != 0) = true then
    pure (ForInStep.yield (s.fst.set! r.fst.log2 r.fst, s.snd.set! r.fst.log2 r.snd))
  else pure (ForInStep.yield (s.fst, s.snd))

private def body2in (pv pm : Array Nat) (b' : Nat) (s : Nat × Nat) : Id (ForInStep (Nat × Nat)) :=
  if s.fst.testBit b' = true then
    pure (ForInStep.yield (s.fst ^^^ pv[b']!, s.snd ^^^ pm[b']!))
  else pure (ForInStep.yield (s.fst, s.snd))

private def body2 (b : Nat) (s : Array Nat × Array Nat) : Id (ForInStep (Array Nat × Array Nat)) :=
  let r := Id.run (forIn (List.range' 0 b) (s.fst[b]!, s.snd[b]!) (body2in s.fst s.snd))
  pure (ForInStep.yield (s.fst.set! b r.fst, s.snd.set! b r.snd))

private def phase1 (vs : Array Nat) : Array Nat × Array Nat :=
  Id.run (forIn (List.range' 0 vs.size) (Array.replicate 52 0, Array.replicate 52 0) (body1 vs))

private theorem spanMasks_eq (vs : Array Nat) :
    spanMasks vs = (Id.run (forIn (List.range' 0 52) (phase1 vs) body2)).snd := by
  unfold spanMasks phase1
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private structure PInv (vs pv pm : Array Nat) : Prop where
  szv : pv.size = 52
  szm : pm.size = 52
  form : PForm pv
  lin : ∀ b < 52, X vs pm[b]! = pv[b]!

private theorem bit_cases {a b : Bool} : ¬ (a && b) = true → a = false ∨ b = false := by
  cases a <;> cases b <;> simp

private theorem inner1 {vs pv pm : Array Nat} (I : PInv vs pv pm) {t : Nat} (ht : t < vs.size)
    (hv : vs[t]! < 2 ^ 52) :
    let r := Id.run (forIn (List.range' 0 52) (vs[t]!, 2 ^ t) (body1in pv pm))
    r.fst < 2 ^ 52 ∧ X vs r.snd = r.fst ∧ Span pv (vs[t]! ^^^ r.fst) ∧
      ∀ b < 52, pv[b]! = 0 ∨ ¬ r.fst.testBit b = true := by
  intro r
  refine forIn_range'_done 52 0 (vs[t]!, 2 ^ t) (body1in pv pm)
    (fun j s => s.fst < 2 ^ 52 ∧ X vs s.snd = s.fst ∧ Span pv (vs[t]! ^^^ s.fst) ∧
      ∀ b, 52 - j ≤ b → b < 52 → pv[b]! = 0 ∨ ¬ s.fst.testBit b = true)
    (fun s => s.fst < 2 ^ 52 ∧ X vs s.snd = s.fst ∧ Span pv (vs[t]! ^^^ s.fst) ∧
      ∀ b < 52, pv[b]! = 0 ∨ ¬ s.fst.testBit b = true)
    (fun j hj s hP => Or.inl ?_) (fun s hP => ⟨hP.1, hP.2.1, hP.2.2.1, fun b hb => hP.2.2.2 b (by omega) hb⟩)
    ⟨hv, ?_, by simpa using Span.zero, fun b hb _ => by omega⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hP
    simp only [Nat.zero_add]
    by_cases hc : (s.fst.testBit (51 - j) && pv[51 - j]! != 0) = true
    · have hb : 51 - j < 52 := by omega
      have hne : pv[51 - j]! ≠ 0 := by simpa using (Bool.and_eq_true_iff.1 hc).2
      rcases I.form _ hb with e | ⟨e1, e2⟩
      · exact absurd e hne
      refine ⟨(s.fst ^^^ pv[51 - j]!, s.snd ^^^ pm[51 - j]!), by simp [body1in, hc], ?_, ?_, ?_, ?_⟩
      · exact Nat.xor_lt_two_pow h1 (Nat.lt_of_lt_of_le e2 (Nat.pow_le_pow_right (by decide) (by omega)))
      · show X vs (s.snd ^^^ pm[51 - j]!) = s.fst ^^^ pv[51 - j]!
        simp only [X] at h2 ⊢
        rw [xorSel_xor, h2]
        exact congrArg _ (I.lin _ hb)
      · rw [← Nat.xor_assoc]; exact .add h3 (.gen _ hb)
      · intro b hb1 hb2
        show pv[b]! = 0 ∨ ¬ (s.fst ^^^ pv[51 - j]!).testBit b = true
        by_cases hbe : b = 51 - j
        · subst hbe
          right
          rw [Nat.testBit_xor, testBit_top e1 e2]
          have := (Bool.and_eq_true_iff.1 hc).1
          rw [this]; simp
        · rcases h4 b (by omega) hb2 with e | e
          · exact Or.inl e
          · right
            rw [Nat.testBit_xor, testBit_above e2 (by omega)]
            simpa using e
    · refine ⟨(s.fst, s.snd), by simp [body1in, hc], h1, h2, h3, ?_⟩
      intro b hb1 hb2
      by_cases hbe : b = 51 - j
      · subst hbe
        rcases bit_cases hc with e | e
        · exact Or.inr (by simp [e])
        · exact Or.inl (by simpa using e)
      · exact h4 b (by omega) hb2
  · simp only [X]
    rw [xorSel_two_pow]; simp [ht]

private theorem rep_get {b : Nat} (hb : b < 52) : (Array.replicate 52 (0 : Nat))[b]! = 0 := by
  rw [getElem!_pos _ b (by simpa using hb)]; simp

private structure P1 (vs pv pm : Array Nat) (t : Nat) : Prop where
  inv : PInv vs pv pm
  span : ∀ t' < t, Span pv vs[t']!

private theorem phase1_spec (vs : Array Nat) (hv : ∀ t < vs.size, vs[t]! < 2 ^ 52) :
    P1 vs (phase1 vs).1 (phase1 vs).2 vs.size := by
  unfold phase1
  refine forIn_range'_done vs.size 0 (Array.replicate 52 0, Array.replicate 52 0) (body1 vs)
    (fun j s => P1 vs s.1 s.2 j) (fun s => P1 vs s.1 s.2 vs.size) (fun j hj s hP => Or.inl ?_)
    (fun s hP => hP) ⟨⟨by simp, by simp, fun b hb => Or.inl (rep_get hb), fun b hb => ?_⟩,
      fun t ht => by omega⟩
  rotate_left
  · show X vs (Array.replicate 52 (0 : Nat))[b]! = (Array.replicate 52 (0 : Nat))[b]!
    rw [rep_get hb]; exact xorSel_zero_mask _ _
  · obtain ⟨pv, pm⟩ := s
    obtain ⟨I, hS⟩ := hP
    have := I.szv
    have := I.szm
    simp only [Nat.zero_add] at *
    obtain ⟨hr1, hr2, hr3, hr4⟩ := inner1 I hj (hv j hj)
    generalize hr : Id.run (forIn (List.range' 0 52) (vs[j]!, 2 ^ j) (body1in pv pm)) = r
      at hr1 hr2 hr3 hr4
    by_cases hz : r.fst = 0
    · refine ⟨(pv, pm), by simp [body1, hr, hz], I, fun t' ht' => ?_⟩
      by_cases e : t' = j
      · subst e; simpa [hz] using hr3
      · exact hS t' (by omega)
    · have hj0 : r.fst.log2 < 52 := (Nat.log2_lt hz).2 hr1
      have hpv0 : pv[r.fst.log2]! = 0 := by
        rcases hr4 _ hj0 with e | e
        · exact e
        · exact absurd (Nat.testBit_log2 hz) e
      have hset : ∀ b < 52, pv[b]! = 0 ∨ (pv.set! r.fst.log2 r.fst)[b]! = pv[b]! := fun b hb => by
        rw [set_get _ _ _ _ (by omega)]
        by_cases e : r.fst.log2 = b
        · subst e; exact Or.inl hpv0
        · exact Or.inr (by simp [e])
      refine ⟨(pv.set! r.fst.log2 r.fst, pm.set! r.fst.log2 r.snd),
        by simp [body1, hr, hz], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [I.szv]
      · simp [I.szm]
      · intro b hb
        rw [set_get _ _ _ _ (by omega)]
        by_cases e : r.fst.log2 = b
        · subst e
          rw [if_pos rfl]
          exact Or.inr ((Nat.log2_eq_iff hz).1 rfl)
        · rw [if_neg e]; exact I.form b hb
      · intro b hb
        rw [set_get _ _ _ _ (by omega), set_get _ _ _ _ (by omega)]
        by_cases e : r.fst.log2 = b
        · subst e; rw [if_pos rfl, if_pos rfl]; exact hr2
        · rw [if_neg e, if_neg e]; exact I.lin b hb
      · intro t' ht'
        by_cases e : t' = j
        · subst e
          have hg := Span.gen (pv := pv.set! r.fst.log2 r.fst) r.fst.log2 hj0
          rw [set_get _ _ _ _ (by omega), if_pos rfl] at hg
          have e2 : vs[t']! = (vs[t']! ^^^ r.fst) ^^^ r.fst := by
            rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          rw [e2]
          exact .add (hr3.mono hset) hg
        · exact (hS t' (by omega)).mono hset

private theorem pv_ne_all {vs : Array Nat} {pv pm : Array Nat} (hP : P1 vs pv pm vs.size)
    (hM : ∀ c < 52, ∃ m, X vs m = 2 ^ c) : ∀ c < 52, pv[c]! ≠ 0 := fun c hc => by
  obtain ⟨m, hm⟩ := hM c hc
  have hs : Span pv (2 ^ c) := by
    rw [← hm]
    exact Span.of_sel _ m _ fun t ht => hP.span t ht
  exact pv_ne_of_rep hP.inv.form hc hs.to_mask

private structure P2 (vs pv pm : Array Nat) (b0 : Nat) : Prop where
  inv : PInv vs pv pm
  ne : ∀ b < 52, pv[b]! ≠ 0
  done : ∀ b < b0, pv[b]! = 2 ^ b

private theorem inner2 {vs pv pm : Array Nat} (I : PInv vs pv pm) {b : Nat} (hb : b < 52)
    (hd : ∀ b' < b, pv[b']! = 2 ^ b') (hne : pv[b]! ≠ 0) :
    let r := Id.run (forIn (List.range' 0 b) (pv[b]!, pm[b]!) (body2in pv pm))
    r.fst = 2 ^ b ∧ X vs r.snd = r.fst := by
  intro r
  obtain ⟨e1, e2⟩ : 2 ^ b ≤ pv[b]! ∧ pv[b]! < 2 ^ (b + 1) := by
    rcases I.form b hb with e | e
    · exact absurd e hne
    · exact e
  refine forIn_range'_done b 0 (pv[b]!, pm[b]!) (body2in pv pm)
    (fun j s => X vs s.snd = s.fst ∧
      ∀ i, s.fst.testBit i = if i < j then false else pv[b]!.testBit i)
    (fun s => s.fst = 2 ^ b ∧ X vs s.snd = s.fst)
    (fun j hj s hP => Or.inl ?_) (fun s hP => ⟨?_, hP.1⟩) ⟨I.lin b hb, fun i => by simp⟩
  · obtain ⟨h2, h4⟩ := hP
    simp only [Nat.zero_add]
    have hpj : pv[j]! = 2 ^ j := hd j hj
    by_cases hc : s.fst.testBit j = true
    · refine ⟨(s.fst ^^^ pv[j]!, s.snd ^^^ pm[j]!), by simp [body2in, hc], ?_, ?_⟩
      · show X vs (s.snd ^^^ pm[j]!) = s.fst ^^^ pv[j]!
        simp only [X] at h2 ⊢
        rw [xorSel_xor, h2]
        exact congrArg _ (I.lin _ (by omega))
      · intro i
        show (s.fst ^^^ pv[j]!).testBit i = _
        rw [Nat.testBit_xor, h4 i, hpj, Nat.testBit_two_pow]
        by_cases h1 : i < j
        · simp [h1, show ¬ j = i by omega, show i < j + 1 by omega]
        · by_cases h3 : i = j
          · subst h3
            have := h4 i
            rw [hc] at this
            simp [h1] at this
            simp [h1, this]
          · simp [h1, h3, show ¬ i < j + 1 by omega, show ¬ j = i by omega]
    · refine ⟨(s.fst, s.snd), by simp [body2in, hc], h2, fun i => ?_⟩
      rw [h4 i]
      by_cases h1 : i < j
      · simp [h1, show i < j + 1 by omega]
      · by_cases h3 : i = j
        · subst h3
          have := h4 i
          simp [h1] at this
          simp [h1, show i < i + 1 by omega]
          rw [← this]
          simpa using hc
        · simp [h1, show ¬ i < j + 1 by omega]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [hP.2 i, Nat.testBit_two_pow]
    by_cases h1 : i < b
    · simp [h1, show ¬ b = i by omega]
    · by_cases h3 : i = b
      · subst h3; simp [h1, testBit_top e1 e2]
      · simp [h1, show ¬ b = i by omega, testBit_above e2 (show b < i by omega)]

private theorem phase2_spec {vs pv pm : Array Nat} (hP : P2 vs pv pm 0) :
    P2 vs (Id.run (forIn (List.range' 0 52) (pv, pm) body2)).1
      (Id.run (forIn (List.range' 0 52) (pv, pm) body2)).2 52 := by
  refine forIn_range'_done 52 0 (pv, pm) body2 (fun j s => P2 vs s.1 s.2 j)
    (fun s => P2 vs s.1 s.2 52) (fun j hj s hP => Or.inl ?_) (fun s hP => hP) hP
  obtain ⟨pv, pm⟩ := s
  obtain ⟨I, hne, hd⟩ := hP
  have := I.szv
  have := I.szm
  simp only [Nat.zero_add] at *
  obtain ⟨hr1, hr2⟩ := inner2 I hj hd (hne j hj)
  generalize hr : Id.run (forIn (List.range' 0 j) (pv[j]!, pm[j]!) (body2in pv pm)) = r
    at hr1 hr2
  refine ⟨(pv.set! j r.fst, pm.set! j r.snd), by simp [body2, hr], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [I.szv]
  · simp [I.szm]
  · intro b hb
    rw [set_get _ _ _ _ (by omega)]
    by_cases e : j = b
    · subst e; rw [if_pos rfl, hr1]
      exact Or.inr ⟨Nat.le_refl _, Nat.pow_lt_pow_right (by decide) (by omega)⟩
    · rw [if_neg e]; exact I.form b hb
  · intro b hb
    rw [set_get _ _ _ _ (by omega), set_get _ _ _ _ (by omega)]
    by_cases e : j = b
    · subst e; rw [if_pos rfl, if_pos rfl]; exact hr2
    · rw [if_neg e, if_neg e]; exact I.lin b hb
  · intro b hb
    rw [set_get _ _ _ _ (by omega)]
    by_cases e : j = b
    · subst e; rw [if_pos rfl, hr1]; exact Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _)
    · rw [if_neg e]; exact hne b hb
  · intro b hb
    rw [set_get _ _ _ _ (by omega)]
    by_cases e : j = b
    · subst e; rw [if_pos rfl, hr1]
    · rw [if_neg e]; exact hd b (by omega)

theorem spanOK_of_reps (vs : Array Nat) (hv : ∀ t < vs.size, vs[t]! < 2 ^ 52)
    (hM : ∀ c < 52, ∃ m, xorSel (fun t => vs[t]!) m vs.size = 2 ^ c) :
    spanOK vs (spanMasks vs) = true := by
  have h1 := phase1_spec vs hv
  have hne := pv_ne_all h1 hM
  have h2 := phase2_spec (vs := vs) (pv := (phase1 vs).1) (pm := (phase1 vs).2)
    ⟨h1.inv, hne, fun b hb => by omega⟩
  rw [spanMasks_eq]
  unfold spanOK
  rw [allIn_iff]
  intro c hc
  have hc' : c < 52 := hc
  have e1 := h2.inv.lin c hc'
  have e2 := h2.done c hc'
  simp only [X] at e1
  rw [e1, e2]
  simp

private theorem xorSel_congr (f g : Nat → Nat) (m : Nat) :
    ∀ k, (∀ t < k, f t = g t) → xorSel f m k = xorSel g m k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [xorSel]
    rw [xorSel_congr f g m k (fun t ht => h t (by omega)), h k (by omega)]


private theorem bitnat (m t : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight m t) 1) 1 = m.testBit t := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  show Nat.beq ((m >>> t) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have : m / 2 ^ t % 2 = 0 ∨ m / 2 ^ t % 2 = 1 := by omega
  rcases this with h | h
  · simp [h]; rfl
  · simp [h]

private theorem xor_eq (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

private theorem foldr_xorSel (g : Nat → Nat) (m : Nat) :
    ∀ k a, (List.range k).foldr (fun t acc =>
      nIf(Nat.beq (Nat.land (Nat.shiftRight m t) 1) 1, Nat.xor acc (g t), acc)) a =
        a ^^^ xorSel g m k
  | 0, a => by simp [xorSel]
  | k + 1, a => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_xorSel g m k]
    simp only [xorSel, bitnat, xor_eq]
    cases m.testBit k
    · simp
    · simp [xor_eq, Nat.xor_assoc, Nat.xor_comm, xor_left_comm']

open CFSG.KC.LocalComp.TitsChain in
theorem span_sound {N : Nat} {TP M : Nat → Nat} {CP : List Nat}
    (hv : ∀ t < CP.length, CP.getD t 0 < N ∧ TP (CP.getD t 0) < 2 ^ 52)
    (h : spanK TP CP M = true) :
    spanOK (CP.toArray.map fun i => (Array.ofFn (n := N) fun j => TP j.val)[i]!)
      (spanMasks (CP.toArray.map fun i => (Array.ofFn (n := N) fun j => TP j.val)[i]!)) = true := by
  have hsz : (CP.toArray.map fun i => (Array.ofFn (n := N) fun j => TP j.val)[i]!).size
      = CP.length := by simp
  have hget : ∀ t < CP.length,
      (CP.toArray.map fun i => (Array.ofFn (n := N) fun j => TP j.val)[i]!)[t]! =
        TP (CP.getD t 0) := fun t ht => by
    rw [getElem!_pos _ t (by simpa using ht)]
    simp only [Array.getElem_map, List.getElem_toArray]
    have hlt := (hv t ht).1
    have hg : CP.getD t 0 = CP[t] := by simp [ht]
    rw [hg] at hlt ⊢
    exact ofFn_get (f := TP) hlt
  apply spanOK_of_reps
  · intro t ht
    rw [hsz] at ht
    rw [hget t ht]
    exact (hv t ht).2
  · intro c hc
    unfold spanK at h
    rw [List.all_eq_true] at h
    have h1 := Nat.eq_of_beq_eq_true (h c (List.mem_range.2 hc))
    rw [foldr_xorSel (fun t => TP (CP.getD t 0)) (M c) CP.length 0, Nat.zero_xor] at h1
    refine ⟨M c, ?_⟩
    rw [hsz]
    rw [xorSel_congr _ (fun t => TP (CP.getD t 0)) (M c) CP.length hget, h1]
    show 1 <<< c = 2 ^ c
    rw [Nat.shiftLeft_eq, Nat.one_mul]

end CFSG.KC.LocalComp.TitsSound

end
