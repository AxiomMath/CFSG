module

public import Certificates.Data.Kernel.Spor.BfsL
public import CFSG.Sporadic.HNOddCore.SCheckInputs
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.BfsL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

private def Lex (a b c d : Nat) : Prop := a < c ∨ (a = c ∧ b < d)

private theorem blt_dec' (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

private theorem beq_dec' (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

private theorem lexLtK_iff {a b c d : Nat} : lexLtK a b c d = true ↔ Lex a b c d := by
  unfold lexLtK Lex
  rw [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq, blt_dec', beq_dec', blt_dec']
  by_cases h : a < c <;> simp [h]

private theorem hd_spec {m root cnt : Nat} {PTS POS PAR LAB : Nat → Nat}
    (h : bfsLHdK m root cnt PTS POS PAR LAB = true) :
    0 < cnt ∧ cnt ≤ m ∧ m < noneK ∧ r32 PTS 0 = root ∧
      ∀ z < m, r32 POS z = noneK ∨ (r32 POS z < cnt ∧ r32 PTS (r32 POS z) = z) := by
  unfold bfsLHdK at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, -, h5, -, -, h8⟩ := h
  refine ⟨h1, h2, h3, h5, fun z hz => ?_⟩
  have hq := CFSG.KS.allN_spec h8 z hz
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq,
    Nat.beq_eq] at hq
  by_cases e : r32 POS z = noneK
  · exact Or.inl e
  · rw [if_neg e] at hq
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hq
    exact Or.inr hq

private theorem pt_spec {m cnt k : Nat} {L : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    {i : Nat} (h : bfsLPtK m cnt k L PTS POS PAR LAB i = true) :
    r32 PTS i < m ∧ r32 POS (r32 PTS i) = i ∧
    (i ≠ 0 → r32 PAR i < i ∧ r32 LAB i < k ∧ L (r32 LAB i) (r32 PTS (r32 PAR i)) = r32 PTS i ∧
      (i + 1 < cnt → Lex (r32 PAR i) (r32 LAB i) (r32 PAR (i + 1)) (r32 LAB (i + 1)))) ∧
    ∀ s < k, L s (r32 PTS i) < m → r32 POS (L s (r32 PTS i)) < cnt ∧
      (r32 POS (L s (r32 PTS i)) = 0 ∨
        ¬ Lex i s (r32 PAR (r32 POS (L s (r32 PTS i)))) (r32 LAB (r32 POS (L s (r32 PTS i))))) := by
  unfold bfsLPtK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, ht, hs⟩ := h
  refine ⟨h1, h2, fun hi => ?_, fun s hs' hlt => ?_⟩
  · have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [e] at ht
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq] at ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    refine ⟨h1, h2, h3, fun hc => ?_⟩
    have hc' : Nat.succ i < cnt := hc
    simp only [hc', ↓reduceIte] at h4
    exact lexLtK_iff.1 h4
  · have hq := CFSG.KS.allN_spec hs s hs'
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq,
      Nat.blt_eq, Nat.beq_eq] at hq
    rw [if_pos hlt] at hq
    simp only [Bool.and_eq_true, Nat.blt_eq] at hq
    obtain ⟨hq1, hq2⟩ := hq
    refine ⟨hq1, ?_⟩
    by_cases h0 : r32 POS (L s (r32 PTS i)) = 0
    · exact Or.inl h0
    · right
      intro hl
      rw [if_neg h0, if_pos (lexLtK_iff.2 hl)] at hq2
      exact absurd hq2 (by decide)

private structure Facts (m k cnt : Nat) (L : Nat → Nat → Nat) (T pos par lab : Nat → Nat) :
    Prop where
  pos_cnt : 0 < cnt
  cnt_le : cnt ≤ m
  lt_m : ∀ i < cnt, T i < m
  pos_T : ∀ i < cnt, pos (T i) = i
  tree : ∀ i, 0 < i → i < cnt → par i < i ∧ lab i < k ∧ L (lab i) (T (par i)) = T i
  order : ∀ i, 0 < i → i + 1 < cnt → Lex (par i) (lab i) (par (i + 1)) (lab (i + 1))
  close : ∀ h < cnt, ∀ j < k, L j (T h) < m → pos (L j (T h)) < cnt ∧
    T (pos (L j (T h))) = L j (T h) ∧
    (pos (L j (T h)) = 0 ∨ ¬ Lex h j (par (pos (L j (T h)))) (lab (pos (L j (T h)))))

private theorem facts_of {m root cnt k : Nat} {L : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    (hh : bfsLHdK m root cnt PTS POS PAR LAB = true)
    (hp : ∀ i < cnt, bfsLPtK m cnt k L PTS POS PAR LAB i = true) :
    Facts m k cnt L (r32 PTS) (r32 POS) (r32 PAR) (r32 LAB) := by
  obtain ⟨h1, h2, h3, -, h5⟩ := hd_spec hh
  refine ⟨h1, h2, fun i hi => (pt_spec (hp i hi)).1, fun i hi => (pt_spec (hp i hi)).2.1,
    fun i h0 hi => ?_, fun i h0 hi => ?_, fun a ha j hj hlt => ?_⟩
  · obtain ⟨t1, t2, t3, -⟩ := (pt_spec (hp i hi)).2.2.1 (by omega)
    exact ⟨t1, t2, t3⟩
  · exact ((pt_spec (hp i (by omega))).2.2.1 (by omega)).2.2.2 hi
  · obtain ⟨hq, hor⟩ := (pt_spec (hp a ha)).2.2.2 j hj hlt
    refine ⟨hq, ?_, hor⟩
    rcases h5 _ hlt with e | ⟨-, e⟩
    · omega
    · exact e

section Facts

variable {m k cnt : Nat} {L : Nat → Nat → Nat} {T pos par lab : Nat → Nat}

private theorem Facts.inj (F : Facts m k cnt L T pos par lab) {a b : Nat} (ha : a < cnt)
    (hb : b < cnt) (e : T a = T b) : a = b := by
  rw [← F.pos_T a ha, ← F.pos_T b hb, e]

private theorem lex_trans {a b c d e f : Nat} (h1 : Lex a b c d) (h2 : Lex c d e f) :
    Lex a b e f := by
  unfold Lex at *
  omega

private theorem lex_irrefl {a b : Nat} : ¬ Lex a b a b := by
  unfold Lex
  omega

private theorem Facts.order_lt (F : Facts m k cnt L T pos par lab) {i i' : Nat} (h0 : 0 < i)
    (hi : i < i') (hi' : i' < cnt) : Lex (par i) (lab i) (par i') (lab i') := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with a | a
    · exact lex_trans (ih a (by omega)) (F.order i' (by omega) hi')
    · have e : i = i' := by omega
      subst e
      exact F.order i h0 hi'

end Facts

private theorem forIn_range'_yield' {β : Type} (n s : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) (P : Nat → β → Prop)
    (h : ∀ j < n, ∀ b, P j b → ∃ b', f (s + j) b = pure (ForInStep.yield b') ∧ P (j + 1) b')
    (h0 : P 0 init) : P n (Id.run (forIn (List.range' s n) init f)) := by
  induction n generalizing s init P with
  | zero => simpa using h0
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨b', hb, hP⟩ := h 0 (by omega) init h0
    rw [Nat.add_zero] at hb
    rw [hb]
    have := ih (s + 1) b' (fun j b => P (j + 1) b) (fun j hj b hbj => by
      obtain ⟨b'', e, p⟩ := h (j + 1) (by omega) b hbj
      exact ⟨b'', by rw [show s + 1 + j = s + (j + 1) by omega]; exact e, p⟩) hP
    simpa using this

private theorem forIn_list_yield {α β : Type} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) (P : Nat → β → Prop)
    (h : ∀ j (hj : j < l.length), ∀ b, P j b →
      ∃ b', f l[j] b = pure (ForInStep.yield b') ∧ P (j + 1) b')
    (h0 : P 0 init) : P l.length (Id.run (forIn l init f)) := by
  induction l generalizing init P with
  | nil => simpa using h0
  | cons a l ih =>
    rw [List.forIn_cons]
    obtain ⟨b', hb, hP⟩ := h 0 (by simp) init h0
    rw [List.getElem_cons_zero] at hb
    rw [hb]
    have := ih b' (fun j b => P (j + 1) b) (fun j hj b hbj => by
      obtain ⟨b'', e, p⟩ := h (j + 1) (by simp only [List.length_cons]; omega) b hbj
      rw [List.getElem_cons_succ] at e
      exact ⟨b'', e, p⟩) hP
    simpa using this

private theorem forIn_array_yield {α β : Type} (A : Array α) (init : β)
    (f : α → β → Id (ForInStep β)) (P : Nat → β → Prop)
    (h : ∀ j (hj : j < A.size), ∀ b, P j b →
      ∃ b', f A[j] b = pure (ForInStep.yield b') ∧ P (j + 1) b')
    (h0 : P 0 init) : P A.size (Id.run (forIn A init f)) := by
  have := forIn_list_yield A.toList init f P (fun j hj b hb => by
    obtain ⟨b', e, p⟩ := h j (by simpa using hj) b hb
    exact ⟨b', by rw [Array.getElem_toList]; exact e, p⟩) h0
  rwa [Array.length_toList, Array.forIn_toList] at this

private theorem push_lt' {a : Array Nat} {x : Nat} {i : Nat} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), Array.getElem_push_lt h, getElem!_pos a i h]

private theorem push_eq' {a : Array Nat} {x : Nat} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

private theorem set_get' {α : Type} [Inhabited α] {a : Array α} {y z : Nat} {v : α}
    (hz : z < a.size) : (a.set! y v)[z]! = if y = z then v else a[z]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds y v) z (by simp; omega),
    Array.getElem_setIfInBounds hz, getElem!_pos a z hz]

private theorem ofFn_get {cnt : Nat} {f : Nat → Nat} {i : Nat} (hi : i < cnt) :
    (Array.ofFn (n := cnt) fun j => f j.val)[i]! = f i := by
  rw [getElem!_pos (Array.ofFn (n := cnt) fun j => f j.val) i (by simp; omega),
    Array.getElem_ofFn]

private abbrev BSt := Array Nat × Array Bool

private def innerB (m h : Nat) (g : Array Nat) (st : BSt) : Id (ForInStep BSt) :=
  if (decide (g[st.1[h]!]! < m) && !st.2[g[st.1[h]!]!]!) = true then
    pure (ForInStep.yield (st.1.push g[st.1[h]!]!, st.2.set! g[st.1[h]!]! true))
  else pure (ForInStep.yield (st.1, st.2))

private def outerB (m : Nat) (gens : Array (Array Nat)) (h : Nat) (st : BSt) :
    Id (ForInStep BSt) :=
  if h < st.1.size then pure (ForInStep.yield (Id.run (forIn gens (st.1, st.2) (innerB m h))))
  else pure (ForInStep.yield (st.1, st.2))

private theorem bfsList_eq (m : Nat) (gens : Array (Array Nat)) (root : Nat) :
    CFSG.Sporadic.HNOddCore.Native.bfsList m gens root =
      (Id.run (forIn (List.range' 0 m) (#[root], (Array.replicate m false).set! root true)
        (outerB m gens))).1 := by
  unfold CFSG.Sporadic.HNOddCore.Native.bfsList
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def BInv (m cnt : Nat) (T par lab : Nat → Nat) (h j : Nat) (st : BSt) : Prop :=
  st.1.size ≤ cnt ∧ (∀ i < st.1.size, st.1[i]! = T i) ∧ st.2.size = m ∧
    (∀ z < m, st.2[z]! = true ↔ ∃ i < st.1.size, T i = z) ∧
    (∀ i < cnt, i < st.1.size ↔ (i = 0 ∨ Lex (par i) (lab i) h j))

section Search

variable {m k cnt : Nat} {L : Nat → Nat → Nat} {T pos par lab : Nat → Nat}

private theorem inner_step (F : Facts m k cnt L T pos par lab) {h j : Nat} (hh : h < cnt)
    (hj : j < k) {g : Array Nat} (hg : ∀ x < m, g[x]! = L j x) {st : BSt}
    (hI : BInv m cnt T par lab h j st) :
    ∃ st', innerB m h g st = pure (ForInStep.yield st') ∧ BInv m cnt T par lab h (j + 1) st' := by
  obtain ⟨hle, hget, hsz, hseen, hch⟩ := hI
  have hhs : h < st.1.size := by
    rw [hch h hh]
    by_cases h0 : h = 0
    · exact Or.inl h0
    · exact Or.inr (Or.inl (F.tree h (by omega) hh).1)
  have hy : g[st.1[h]!]! = L j (T h) := by rw [hget h hhs]; exact hg _ (F.lt_m h hh)
  have hmove : ∀ i, (i = 0 ∨ Lex (par i) (lab i) h (j + 1)) ↔
      ((i = 0 ∨ Lex (par i) (lab i) h j) ∨ (0 < i ∧ par i = h ∧ lab i = j)) := by
    intro i
    unfold Lex
    omega
  have himg : ∀ i < cnt, 0 < i → par i = h → lab i = j → T i = L j (T h) := by
    intro i hi h0 hp hl
    rw [← (F.tree i h0 hi).2.2, hp, hl]
  unfold innerB
  rw [hy]
  by_cases hlt : L j (T h) < m
  · obtain ⟨hq, hx, hor⟩ := F.close h hh j hj hlt
    generalize pos (L j (T h)) = q at hq hx hor
    by_cases hnew : 0 < q ∧ par q = h ∧ lab q = j
    ·
      obtain ⟨hq0, hpq, hlq⟩ := hnew
      have hqs : ¬ q < st.1.size := by
        rw [hch q hq]
        rintro (e | e)
        · omega
        · rw [hpq, hlq] at e
          exact lex_irrefl e
      have hqm : q = st.1.size := by
        refine Nat.le_antisymm (Nat.le_of_not_lt fun hlt' => ?_) (by omega)
        have hm0 : 0 < st.1.size := by
          have := (hch 0 F.pos_cnt).2 (Or.inl rfl)
          omega
        have hns : ¬ (st.1.size = 0 ∨ Lex (par st.1.size) (lab st.1.size) h j) := by
          rw [← hch st.1.size (by omega)]
          exact Nat.lt_irrefl _
        have := F.order_lt hm0 hlt' hq
        rw [hpq, hlq] at this
        exact hns (Or.inr this)
      have hnc : st.2[L j (T h)]! = false := by
        rw [Bool.eq_false_iff]
        intro hc
        obtain ⟨i, hi, e⟩ := (hseen _ hlt).1 hc
        rw [← hx] at e
        have := F.inj (by omega) hq e
        omega
      refine ⟨(st.1.push (L j (T h)), st.2.set! (L j (T h)) true), by simp [hlt, hnc], ?_⟩
      unfold BInv
      dsimp only
      refine ⟨?_, fun i hi => ?_, ?_, fun z hz => ?_, fun i hi => ?_⟩
      · rw [Array.size_push]
        omega
      · rw [Array.size_push] at hi
        rcases Nat.lt_or_ge i st.1.size with a | a
        · rw [push_lt' a]
          exact hget i a
        · have e : i = st.1.size := by omega
          subst e
          rw [push_eq', ← hqm, hx]
      · simp [hsz]
      · rw [Array.size_push, set_get' (by omega)]
        by_cases e : L j (T h) = z
        · rw [if_pos e]
          exact iff_of_true rfl ⟨st.1.size, by omega, by rw [← hqm, hx, e]⟩
        · rw [if_neg e, hseen z hz]
          constructor
          · rintro ⟨i, hi, e'⟩
            exact ⟨i, by omega, e'⟩
          · rintro ⟨i, hi, e'⟩
            rcases Nat.lt_or_ge i st.1.size with a | a
            · exact ⟨i, a, e'⟩
            · have : i = st.1.size := by omega
              subst this
              rw [← hqm, hx] at e'
              exact absurd e' e
      · rw [Array.size_push, hmove i, ← hch i hi]
        constructor
        · intro hlt'
          rcases Nat.lt_or_ge i st.1.size with a | a
          · exact Or.inl a
          · have e : i = st.1.size := by omega
            subst e
            exact Or.inr ⟨by omega, by rw [← hqm]; exact hpq, by rw [← hqm]; exact hlq⟩
        · rintro (a | ⟨a0, a1, a2⟩)
          · omega
          · refine Classical.byContradiction fun hne => ?_
            have hgt : q < i := by omega
            have := F.order_lt hq0 hgt hi
            rw [hpq, hlq, a1, a2] at this
            exact lex_irrefl this
    ·
      have hqs : q < st.1.size := by
        rw [hch q hq]
        rcases hor with e | e
        · exact Or.inl e
        · by_cases h0 : q = 0
          · exact Or.inl h0
          · right
            unfold Lex at e ⊢
            have : ¬ (par q = h ∧ lab q = j) := fun e' => hnew ⟨by omega, e'.1, e'.2⟩
            omega
      have hc : st.2[L j (T h)]! = true := (hseen _ hlt).2 ⟨q, hqs, hx⟩
      refine ⟨st, by simp [hc], hle, hget, hsz, hseen, fun i hi => ?_⟩
      rw [hmove i, ← hch i hi]
      constructor
      · exact Or.inl
      · rintro (a | ⟨a0, a1, a2⟩)
        · exact a
        · exfalso
          have := F.inj hi hq ((himg i hi a0 a1 a2).trans hx.symm)
          subst this
          exact hnew ⟨a0, a1, a2⟩
  ·
    refine ⟨st, by simp [hlt], hle, hget, hsz, hseen, fun i hi => ?_⟩
    rw [hmove i, ← hch i hi]
    constructor
    · exact Or.inl
    · rintro (a | ⟨a0, a1, a2⟩)
      · exact a
      · exact absurd (by rw [← himg i hi a0 a1 a2]; exact F.lt_m i hi) hlt

private theorem inner_spec (F : Facts m k cnt L T pos par lab) {gens : Array (Array Nat)}
    (hgs : gens.size = k) (hgv : ∀ s < k, ∀ x < m, (gens[s]!)[x]! = L s x) {h : Nat}
    (hh : h < cnt) {st : BSt} (hI : BInv m cnt T par lab h 0 st) :
    BInv m cnt T par lab (h + 1) 0 (Id.run (forIn gens (st.1, st.2) (innerB m h))) := by
  have := forIn_array_yield gens (st.1, st.2) (innerB m h) (BInv m cnt T par lab h)
    (fun j hj st' hP => inner_step F hh (by omega) (fun x hx => by
      rw [← getElem!_pos gens j hj]; exact hgv j (by omega) x hx) hP) hI
  rw [hgs] at this
  obtain ⟨a1, a2, a3, a4, a5⟩ := this
  refine ⟨a1, a2, a3, a4, fun i hi => ?_⟩
  rw [a5 i hi]
  have hlab : 0 < i → lab i < k := fun h0 => (F.tree i h0 hi).2.1
  unfold Lex
  constructor
  · rintro (e | e)
    · exact Or.inl e
    · right
      omega
  · rintro (e | e)
    · exact Or.inl e
    · by_cases h0 : i = 0
      · exact Or.inl h0
      · right
        have := hlab (by omega)
        omega

private theorem outer_spec (F : Facts m k cnt L T pos par lab) {gens : Array (Array Nat)}
    (hgs : gens.size = k) (hgv : ∀ s < k, ∀ x < m, (gens[s]!)[x]! = L s x) {root : Nat}
    (hroot : T 0 = root) :
    BInv m cnt T par lab m 0 (Id.run (forIn (List.range' 0 m)
      (#[root], (Array.replicate m false).set! root true) (outerB m gens))) := by
  refine forIn_range'_yield' m 0 _ (outerB m gens) (fun h st => BInv m cnt T par lab h 0 st)
    (fun h _ st hI => ?_) ?_
  · rw [Nat.zero_add]
    rcases Nat.lt_or_ge h cnt with a | a
    · have hhs : h < st.1.size := by
        rw [hI.2.2.2.2 h a]
        by_cases h0 : h = 0
        · exact Or.inl h0
        · exact Or.inr (Or.inl (F.tree h (by omega) a).1)
      exact ⟨_, by unfold outerB; rw [if_pos hhs], inner_spec F hgs hgv a hI⟩
    · have hns : ¬ h < st.1.size := by have := hI.1; omega
      refine ⟨st, by unfold outerB; rw [if_neg hns], hI.1, hI.2.1, hI.2.2.1, hI.2.2.2.1,
        fun i hi => ?_⟩
      rw [hI.2.2.2.2 i hi]
      have hpar : 0 < i → par i < i := fun h0 => (F.tree i h0 hi).1
      unfold Lex
      constructor
      · rintro (e | e)
        · exact Or.inl e
        · by_cases h0 : i = 0
          · exact Or.inl h0
          · right; left; have := hpar (by omega); omega
      · rintro (e | e)
        · exact Or.inl e
        · by_cases h0 : i = 0
          · exact Or.inl h0
          · right; left; have := hpar (by omega); omega
  ·
    have hr : root < m := hroot ▸ F.lt_m 0 F.pos_cnt
    have h1 : (#[root] : Array Nat).size = 1 := rfl
    unfold BInv
    dsimp only
    refine ⟨by rw [h1]; exact F.pos_cnt, fun i hi => ?_, by simp, fun z hz => ?_, fun i hi => ?_⟩
    · have : i = 0 := by omega
      subst this
      rw [getElem!_pos (#[root] : Array Nat) 0 (by simp)]
      simp [hroot]
    · rw [set_get' (by simp; omega)]
      by_cases e : root = z
      · rw [if_pos e]
        exact iff_of_true rfl ⟨0, by simp, by rw [hroot, e]⟩
      · rw [if_neg e, getElem!_pos (Array.replicate m false) z (by simp; omega),
          Array.getElem_replicate]
        refine iff_of_false (by simp) fun ⟨i, hi, e'⟩ => e ?_
        have : i = 0 := by omega
        subst this
        rw [← hroot, e']
    · rw [h1]
      unfold Lex
      omega

end Search

theorem bfsLK_sound {m root cnt k : Nat} {L : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    {gens : Array (Array Nat)} (hg : gens.size = k ∧ ∀ s < k, ∀ x < m, (gens[s]!)[x]! = L s x)
    (hh : bfsLHdK m root cnt PTS POS PAR LAB = true)
    (hp : ∀ i < cnt, bfsLPtK m cnt k L PTS POS PAR LAB i = true) :
    CFSG.Sporadic.HNOddCore.Native.bfsList m gens root =
      Array.ofFn (n := cnt) fun i => r32 PTS i.val := by
  obtain ⟨-, -, -, hroot, -⟩ := hd_spec hh
  have F := facts_of hh hp
  rw [bfsList_eq]
  have hO := outer_spec F hg.1 hg.2 hroot
  generalize Id.run (forIn (List.range' 0 m) (#[root], (Array.replicate m false).set! root true)
    (outerB m gens)) = st at hO
  obtain ⟨hle, hget, -, -, hch⟩ := hO
  have hsz : st.1.size = cnt := by
    refine Nat.le_antisymm hle ?_
    have := F.pos_cnt
    have := F.cnt_le
    have h1 := (hch (cnt - 1) (by omega)).2 (by
      by_cases h0 : cnt - 1 = 0
      · exact Or.inl h0
      · have := (F.tree (cnt - 1) (by omega) (by omega)).1
        exact Or.inr (Or.inl (by omega)))
    omega
  refine Array.ext (by rw [hsz, Array.size_ofFn]) fun i hi1 hi2 => ?_
  rw [← getElem!_pos st.1 i hi1, hget i hi1, Array.getElem_ofFn]

private abbrev RSt := Array Nat × Array Nat × Array Bool

private def recInner (gens : Array (Array Nat)) (Q P : Array Nat) (j s : Nat) (st : RSt) :
    Id (ForInStep RSt) :=
  if (decide (P[(gens[s]!)[Q[j]!]!]! < Q.size) && decide (j < P[(gens[s]!)[Q[j]!]!]!) &&
      !st.2.2[P[(gens[s]!)[Q[j]!]!]!]!) = true then
    pure (ForInStep.yield (st.1.set! P[(gens[s]!)[Q[j]!]!]! j,
      st.2.1.set! P[(gens[s]!)[Q[j]!]!]! s, st.2.2.set! P[(gens[s]!)[Q[j]!]!]! true))
  else pure (ForInStep.yield (st.1, st.2.1, st.2.2))

private def recOuter (gens : Array (Array Nat)) (Q P : Array Nat) (j : Nat) (st : RSt) :
    Id (ForInStep RSt) :=
  pure (ForInStep.yield
    (Id.run (forIn (List.range' 0 gens.size) (st.1, st.2.1, st.2.2) (recInner gens Q P j))))

private def recRun (gens : Array (Array Nat)) (Q P : Array Nat) : RSt :=
  Id.run (forIn (List.range' 0 Q.size)
    (Array.replicate Q.size 0, Array.replicate Q.size 0, Array.replicate Q.size false)
    (recOuter gens Q P))

private theorem orbitRecs_eq (gens : Array (Array Nat)) (Q P : Array Nat) :
    CFSG.Sporadic.HNOddCore.orbitRecs gens Q P = ((recRun gens Q P).1, (recRun gens Q P).2.1) := by
  unfold CFSG.Sporadic.HNOddCore.orbitRecs recRun
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def RInv (gens : Array (Array Nat)) (Q P : Array Nat) (j0 s0 : Nat) (st : RSt) : Prop :=
  st.1.size = Q.size ∧ st.2.1.size = Q.size ∧ st.2.2.size = Q.size ∧
  (∀ kk < Q.size, st.2.2[kk]! = true → st.1[kk]! < kk ∧ st.2.1[kk]! < gens.size ∧
    (gens[st.2.1[kk]!]!)[Q[st.1[kk]!]!]! = Q[kk]!) ∧
  (∀ j s, Lex j s j0 s0 → s < gens.size → P[(gens[s]!)[Q[j]!]!]! < Q.size →
    j < P[(gens[s]!)[Q[j]!]!]! → st.2.2[P[(gens[s]!)[Q[j]!]!]!]! = true)

private theorem rec_step {gens : Array (Array Nat)} {Q P : Array Nat}
    (hval : ∀ j < Q.size, ∀ s < gens.size, P[(gens[s]!)[Q[j]!]!]! < Q.size →
      Q[P[(gens[s]!)[Q[j]!]!]!]! = (gens[s]!)[Q[j]!]!)
    {j0 s0 : Nat} (hj0 : j0 < Q.size) (hs0 : s0 < gens.size) {st : RSt}
    (hI : RInv gens Q P j0 s0 st) :
    ∃ st', recInner gens Q P j0 s0 st = pure (ForInStep.yield st') ∧
      RInv gens Q P j0 (s0 + 1) st' := by
  obtain ⟨h1, h2, h3, hv, hc⟩ := hI
  have hmove : ∀ j s, Lex j s j0 (s0 + 1) → Lex j s j0 s0 ∨ (j = j0 ∧ s = s0) := by
    intro j s
    unfold Lex
    omega
  have hy0 := hval j0 hj0 s0 hs0
  unfold recInner
  generalize hk : P[(gens[s0]!)[Q[j0]!]!]! = kk0 at hy0
  by_cases hcond : kk0 < Q.size ∧ j0 < kk0 ∧ st.2.2[kk0]! = false
  · obtain ⟨c1, c2, c3⟩ := hcond
    have ht : (decide (kk0 < Q.size) && decide (j0 < kk0) && !st.2.2[kk0]!) = true := by
      simp [c1, c2, c3]
    refine ⟨(st.1.set! kk0 j0, st.2.1.set! kk0 s0, st.2.2.set! kk0 true), by rw [if_pos ht], ?_⟩
    have hy : Q[kk0]! = (gens[s0]!)[Q[j0]!]! := hy0 c1
    unfold RInv
    dsimp only
    refine ⟨by simp [h1], by simp [h2], by simp [h3], fun kk hkk hd => ?_,
      fun j s hl hs hlt hjl => ?_⟩
    · rw [set_get' (by omega)] at hd
      rw [set_get' (by omega), set_get' (by omega)]
      by_cases e : kk0 = kk
      · rw [if_pos e, if_pos e]
        subst e
        exact ⟨c2, hs0, hy.symm⟩
      · rw [if_neg e] at hd
        rw [if_neg e, if_neg e]
        exact hv kk hkk hd
    · rw [set_get' (by omega)]
      rcases hmove j s hl with hl' | ⟨rfl, rfl⟩
      · by_cases e : kk0 = P[(gens[s]!)[Q[j]!]!]!
        · rw [if_pos e]
        · rw [if_neg e]
          exact hc j s hl' hs hlt hjl
      · rw [hk, if_pos rfl]
  · have hf : ¬ (decide (kk0 < Q.size) && decide (j0 < kk0) && !st.2.2[kk0]!) = true := by
      intro h
      rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
      exact hcond ⟨h.1.1, h.1.2, by simpa using h.2⟩
    refine ⟨st, by rw [if_neg hf], h1, h2, h3, hv, fun j s hl hs hlt hjl => ?_⟩
    rcases hmove j s hl with hl' | ⟨rfl, rfl⟩
    · exact hc j s hl' hs hlt hjl
    · rw [hk] at hlt hjl ⊢
      by_contra hd
      exact hcond ⟨hlt, hjl, by simpa using hd⟩

private theorem rec_spec {gens : Array (Array Nat)} {Q P : Array Nat}
    (hval : ∀ j < Q.size, ∀ s < gens.size, P[(gens[s]!)[Q[j]!]!]! < Q.size →
      Q[P[(gens[s]!)[Q[j]!]!]!]! = (gens[s]!)[Q[j]!]!) :
    RInv gens Q P Q.size 0 (recRun gens Q P) := by
  unfold recRun
  refine forIn_range'_yield' Q.size 0 _ (recOuter gens Q P) (fun j st => RInv gens Q P j 0 st)
    (fun j hj st hI => ?_) ?_
  · rw [Nat.zero_add]
    refine ⟨_, rfl, ?_⟩
    have := forIn_range'_yield' gens.size 0 (st.1, st.2.1, st.2.2) (recInner gens Q P j)
      (fun s st' => RInv gens Q P j s st') (fun s hs st' hP => by
        rw [Nat.zero_add]
        exact rec_step hval hj hs hP) hI
    obtain ⟨a1, a2, a3, a4, a5⟩ := this
    refine ⟨a1, a2, a3, a4, fun j' s hl hs hlt hjl => a5 j' s ?_ hs hlt hjl⟩
    unfold Lex at hl ⊢
    omega
  · unfold RInv
    dsimp only
    refine ⟨by simp, by simp, by simp, fun kk hkk hd => ?_, fun j s hl => ?_⟩
    · rw [getElem!_pos (Array.replicate Q.size false) kk (by simp; omega),
        Array.getElem_replicate] at hd
      exact absurd hd (by decide)
    · unfold Lex at hl
      omega

section Orbit

variable {m k cnt : Nat} {L : Nat → Nat → Nat} {T pos par lab : Nat → Nat}

private theorem orbitOK_of (F : Facts m k cnt L T pos par lab) {gens : Array (Array Nat)}
    (hgs : gens.size = k) (hgv : ∀ s < k, ∀ x < m, (gens[s]!)[x]! = L s x)
    (himg : ∀ s < k, ∀ x < m, L s x < m) {Q : Array Nat} (hQs : Q.size = cnt)
    (hQg : ∀ i < cnt, Q[i]! = T i) :
    CFSG.Sporadic.HNOddCore.Native.orbitOK m gens Q = true := by
  obtain ⟨hPs, hPv⟩ := CFSG.KS.PW.posArr_spec (n := m) (R := Q)
    (fun i hi => by rw [hQg i (by omega)]; exact F.lt_m i (by omega))
    (fun i hi j hj e => by
      rw [hQg i (by omega), hQg j (by omega)] at e
      have := F.inj (by omega) (by omega) e
      omega)
  have himgQ : ∀ i < cnt, ∀ s < gens.size, (gens[s]!)[Q[i]!]! = L s (T i) := fun i hi s hs => by
    rw [hQg i hi]
    exact hgv s (by omega) _ (F.lt_m i hi)
  have hcl : ∀ i < cnt, ∀ s < gens.size,
      (CFSG.ONSchreier.Native.posArr m Q)[(gens[s]!)[Q[i]!]!]! < cnt ∧
      Q[(CFSG.ONSchreier.Native.posArr m Q)[(gens[s]!)[Q[i]!]!]!]! = (gens[s]!)[Q[i]!]! := by
    intro i hi s hs
    rw [himgQ i hi s hs]
    obtain ⟨hq, hx, -⟩ := F.close i hi s (by omega) (himg s (by omega) _ (F.lt_m i hi))
    generalize pos (L s (T i)) = q at hq hx
    rw [← hx, ← hQg q hq, hPv q (by omega)]
    exact ⟨hq, rfl⟩
  obtain ⟨-, -, -, hv, hc⟩ := rec_spec (gens := gens) (Q := Q)
    (P := CFSG.ONSchreier.Native.posArr m Q) fun j hj s hs _ => (hcl j (by omega) s hs).2
  unfold CFSG.Sporadic.HNOddCore.Native.orbitOK
  rw [orbitRecs_eq]
  unfold CFSG.Sporadic.HNOddCore.orbitCertOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hc0 := F.pos_cnt
  refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, ?_⟩
  ·
    unfold CFSG.ONSchreier.Native.pointsOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨hPs, CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨by rw [hQg i (by omega)]; exact F.lt_m i (by omega), hPv i hi⟩
  ·
    refine CFSG.ONSchreier.allBelowN_iff.2 fun kk hkk => ?_
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h0 : kk = 0
    · exact Or.inl h0
    · right
      obtain ⟨t1, t2, t3⟩ := F.tree kk (by omega) (by omega)
      have hkP : (CFSG.ONSchreier.Native.posArr m Q)[(gens[lab kk]!)[Q[par kk]!]!]! = kk := by
        rw [himgQ _ (by omega) _ (by omega), t3, ← hQg kk (by omega)]
        exact hPv kk hkk
      have hd := hc (par kk) (lab kk) (Or.inl (by omega)) (by omega) (by rw [hkP]; exact hkk)
        (by rw [hkP]; exact t1)
      rw [hkP] at hd
      obtain ⟨v1, v2, v3⟩ := hv kk hkk hd
      exact ⟨⟨v1, v2⟩, v3⟩
  ·
    refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi =>
      CFSG.ONSchreier.allBelowN_iff.2 fun s hs => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    obtain ⟨c1, c2⟩ := hcl i (by omega) s hs
    exact ⟨by omega, c2⟩

end Orbit

theorem orbitOK_sound {m root cnt k : Nat} {L : Nat → Nat → Nat} {PTS POS PAR LAB : Nat → Nat}
    {gens : Array (Array Nat)} (hg : gens.size = k ∧ ∀ s < k, ∀ x < m, (gens[s]!)[x]! = L s x)
    (himg : ∀ s < k, ∀ x < m, L s x < m)
    (hh : bfsLHdK m root cnt PTS POS PAR LAB = true)
    (hp : ∀ i < cnt, bfsLPtK m cnt k L PTS POS PAR LAB i = true) :
    CFSG.Sporadic.HNOddCore.Native.orbitOK m gens (Array.ofFn (n := cnt) fun i => r32 PTS i.val) =
      true :=
  orbitOK_of (facts_of hh hp) hg.1 hg.2 himg Array.size_ofFn fun _ hi => ofFn_get hi

end CFSG.KS.BfsL

end
