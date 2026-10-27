
module

public import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.L34KSnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.PSL3Four.Native
open CFSG.KS.BfsReplay
open CFSG.KLie.CT (fget)

theorem genStepW_eq (st : Nat → Nat → Nat) (T : Nat → Nat) (ew t row k c : Nat) :
    genStepW st T ew t row k c =
      if c = 0 then 0
      else if fget row k ew < c then
        (if T (fget row k ew) = st k t then c else 0)
      else if fget row k ew = c then (if T c = st k t then c + 1 else 0) else 0 := by
  unfold genStepW
  simp only [strictN_app, nIf_ite, Nat.beq_eq, Nat.blt_eq]

theorem genStepW_zero (st : Nat → Nat → Nat) (T : Nat → Nat) (ew t row k : Nat) :
    genStepW st T ew t row k 0 = 0 := by
  simp only [genStepW_eq, ↓reduceIte]

theorem genStepW_spec {st : Nat → Nat → Nat} {T : Nat → Nat} {ew t row k c r : Nat}
    (hr : genStepW st T ew t row k c = r) (h0 : r ≠ 0) :
    c ≠ 0 ∧ c ≤ r ∧ (∃ j < r, T j = st k t) := by
  rw [genStepW_eq] at hr
  by_cases h1 : c = 0
  · simp only [h1, ↓reduceIte] at hr
    exact absurd hr.symm h0
  simp only [h1, ↓reduceIte] at hr
  by_cases h2 : fget row k ew < c
  · simp only [h2, ↓reduceIte] at hr
    by_cases h3 : T (fget row k ew) = st k t
    · simp only [h3, ↓reduceIte] at hr
      subst hr
      exact ⟨h1, le_refl _, ⟨_, h2, h3⟩⟩
    · simp only [h3, ↓reduceIte] at hr
      exact absurd hr.symm h0
  · simp only [h2, ↓reduceIte] at hr
    by_cases h4 : fget row k ew = c
    · by_cases h5 : T c = st k t
      · simp only [h4, h5, ↓reduceIte] at hr
        subst hr
        exact ⟨h1, Nat.le_succ c, ⟨c, Nat.lt_succ_self c, h5⟩⟩
      · simp only [h4, h5, ↓reduceIte] at hr
        exact absurd hr.symm h0
    · simp only [h4, ↓reduceIte] at hr
      exact absurd hr.symm h0

@[expose] noncomputable def pointFW (st : Nat → Nat → Nat) (T E : Nat → Nat) (ew i len : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih lo c => ih (Nat.succ lo) (genStepW st T ew (T i) (E i) lo c)) len

@[expose] noncomputable def pointRecW (ng : Nat) (st : Nat → Nat → Nat) (T E : Nat → Nat)
    (ew i r : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (genStepW st T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c)
      ih) r

section

variable {ng : Nat} {st : Nat → Nat → Nat} {T E : Nat → Nat} {ew : Nat}

theorem pointRecW_eq (i : Nat) : ∀ r, r ≤ ng → ∀ c,
    pointRecW ng st T E ew i r c = pointFW st T E ew i r (ng - r) c
  | 0, _, _ => rfl
  | r + 1, h, c => by
    have e1 : Nat.sub (Nat.sub ng r) (nat_lit 1) = ng - (r + 1) := by
      change ng - r - 1 = ng - (r + 1)
      omega
    have e2 : Nat.succ (ng - (r + 1)) = ng - r := by omega
    have s1 : pointRecW ng st T E ew i (r + 1) c = pointRecW ng st T E ew i r
        (genStepW st T ew (T i) (E i) (Nat.sub (Nat.sub ng r) (nat_lit 1)) c) := strictN_app _ _
    have s2 : pointFW st T E ew i (r + 1) (ng - (r + 1)) c = pointFW st T E ew i r
        (Nat.succ (ng - (r + 1))) (genStepW st T ew (T i) (E i) (ng - (r + 1)) c) := rfl
    rw [s1, s2, e1, e2, pointRecW_eq i r (by omega)]

theorem pointStepW_eq (i c : Nat) :
    pointStepW ng st T E ew i c = pointFW st T E ew i ng 0 c := by
  have h := pointRecW_eq (ng := ng) (st := st) (T := T) (E := E) (ew := ew) i ng (Nat.le_refl ng) c
  rw [Nat.sub_self] at h
  rw [← h]
  unfold pointStepW
  rw [strictN_app, strictN_app]
  rfl

theorem pointFW_zero (i : Nat) : ∀ len lo, pointFW st T E ew i len lo 0 = 0
  | 0, _ => rfl
  | len + 1, lo => by
    change pointFW st T E ew i len (Nat.succ lo) (genStepW st T ew (T i) (E i) lo 0) = 0
    rw [genStepW_zero]
    exact pointFW_zero i len _

theorem pointFW_add (i : Nat) : ∀ (a b lo c : Nat),
    pointFW st T E ew i (a + b) lo c = pointFW st T E ew i b (lo + a) (pointFW st T E ew i a lo c)
  | 0, b, lo, c => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | a + 1, b, lo, c => by
    have e : Nat.succ lo + a = lo + (a + 1) := by omega
    rw [Nat.add_right_comm]
    change pointFW st T E ew i (a + b) (Nat.succ lo) (genStepW st T ew (T i) (E i) lo c) =
      pointFW st T E ew i b (lo + (a + 1))
        (pointFW st T E ew i a (Nat.succ lo) (genStepW st T ew (T i) (E i) lo c))
    rw [pointFW_add i a b (Nat.succ lo), e]

theorem pointFW_cl (i : Nat) : ∀ len lo c r, pointFW st T E ew i len lo c = r → r ≠ 0 →
    c ≤ r ∧ ∀ k, lo ≤ k → k < lo + len → ∃ j < r, T j = st k (T i)
  | 0, lo, c, r, hr, _ => by
    have e : c = r := hr
    subst e
    exact ⟨le_refl _, fun k a b => absurd b (by omega)⟩
  | len + 1, lo, c, r, hr, h0 => by
    change pointFW st T E ew i len (Nat.succ lo) (genStepW st T ew (T i) (E i) lo c) = r at hr
    have hc0 : genStepW st T ew (T i) (E i) lo c ≠ 0 := by
      intro e
      rw [e, pointFW_zero] at hr
      exact h0 hr.symm
    obtain ⟨-, hle, ⟨j, hj, hjT⟩⟩ := genStepW_spec rfl hc0
    obtain ⟨hle', hcl'⟩ := pointFW_cl i len (Nat.succ lo) _ r hr h0
    refine ⟨le_trans hle hle', fun k a b => ?_⟩
    rcases Nat.lt_or_ge lo k with h | h
    · exact hcl' k (by omega) (by omega)
    · have e : k = lo := by omega
      subst e
      exact ⟨j, lt_of_lt_of_le hj hle', hjT⟩

theorem runFW_succ (len lo c : Nat) :
    runFW ng st T E ew (len + 1) lo c =
      runFW ng st T E ew len (Nat.succ lo) (nIf(Nat.blt lo c, pointStepW ng st T E ew lo c,
        nat_lit 0)) :=
  strictN_app _ _

theorem runFW_zero : ∀ len lo, runFW ng st T E ew len lo 0 = 0
  | 0, _ => rfl
  | len + 1, lo => by
    rw [runFW_succ]
    have hb : Nat.blt lo 0 = false := by
      cases h : Nat.blt lo 0
      · rfl
      · exact absurd (Nat.blt_eq.mp h) (Nat.not_lt_zero lo)
    rw [hb]
    exact runFW_zero len _

theorem runFW_add : ∀ (a b lo c : Nat),
    runFW ng st T E ew (a + b) lo c = runFW ng st T E ew b (lo + a) (runFW ng st T E ew a lo c)
  | 0, b, lo, c => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | a + 1, b, lo, c => by
    have e : Nat.succ lo + a = lo + (a + 1) := by omega
    rw [Nat.add_right_comm, runFW_succ, runFW_succ, runFW_add a b (Nat.succ lo), e]

theorem runFW_blocks (L : Nat) (C : Nat → Nat) : ∀ K,
    (∀ s < K, runSlW ng st T E ew L C s = true) → runFW ng st T E ew (L * K) 0 (C 0) = C K
  | 0, _ => rfl
  | K + 1, h => by
    rw [Nat.mul_succ, runFW_add, runFW_blocks L C K (fun s hs => h s (by omega)), Nat.zero_add]
    exact Nat.eq_of_beq_eq_true (h K (by omega))

theorem runFW_cl : ∀ len lo c r, runFW ng st T E ew len lo c = r → r ≠ 0 →
    (∀ i < lo, ∀ k < ng, ∃ j < c, T j = st k (T i)) →
    c ≤ r ∧ ∀ i < lo + len, ∀ k < ng, ∃ j < r, T j = st k (T i)
  | 0, lo, c, r, hr, _, hcl => by
    have e : c = r := hr
    subst e
    exact ⟨le_refl _, hcl⟩
  | len + 1, lo, c, r, hr, h0, hcl => by
    rw [runFW_succ] at hr
    cases hb : Nat.blt lo c
    · rw [hb] at hr
      change runFW ng st T E ew len (Nat.succ lo) 0 = r at hr
      rw [runFW_zero] at hr
      exact absurd hr.symm h0
    · rw [hb] at hr
      change runFW ng st T E ew len (Nat.succ lo) (pointStepW ng st T E ew lo c) = r at hr
      have hp0 : pointStepW ng st T E ew lo c ≠ 0 := by
        intro e
        rw [e, runFW_zero] at hr
        exact h0 hr.symm
      obtain ⟨hle, hclp⟩ := pointFW_cl lo ng 0 c _ (pointStepW_eq lo c).symm hp0
      have hcl' : ∀ i < Nat.succ lo, ∀ k < ng,
          ∃ j < pointStepW ng st T E ew lo c, T j = st k (T i) := by
        intro i hi k hk
        rcases Nat.lt_or_ge i lo with h | h
        · obtain ⟨j, hj, e⟩ := hcl i h k hk
          exact ⟨j, lt_of_lt_of_le hj hle, e⟩
        · have e : i = lo := by omega
          subst e
          exact hclp k (Nat.zero_le k) (by omega)
      obtain ⟨hle', hcl''⟩ := runFW_cl len (Nat.succ lo) _ r hr h0 hcl'
      exact ⟨le_trans hle hle', fun i hi k hk => hcl'' i (by omega) k hk⟩

theorem pointFW_le {i len lo c r : Nat} (hr : pointFW st T E ew i len lo c = r) (h0 : r ≠ 0) :
    c ≤ r :=
  (pointFW_cl i len lo c r hr h0).1

theorem runFW_le {len lo c r : Nat} (hr : runFW ng st T E ew len lo c = r) (h0 : r ≠ 0) :
    c ≤ r := by
  induction len generalizing lo c with
  | zero => exact Nat.le_of_eq hr
  | succ len ih =>
    rw [runFW_succ] at hr
    cases hb : Nat.blt lo c
    · rw [hb] at hr
      change runFW ng st T E ew len (Nat.succ lo) 0 = r at hr
      rw [runFW_zero] at hr
      exact absurd hr.symm h0
    · rw [hb] at hr
      change runFW ng st T E ew len (Nat.succ lo) (pointStepW ng st T E ew lo c) = r at hr
      have hp0 : pointStepW ng st T E ew lo c ≠ 0 := by
        intro e
        rw [e, runFW_zero] at hr
        exact h0 hr.symm
      exact le_trans (pointFW_le (pointStepW_eq lo c).symm hp0) (ih hr)

end

def PInvW (n w ng : Nat) (step : Nat → Tab → Tab) (T : Nat → Nat) (c : Nat) (s : St) : Prop :=
  s.1.size = c ∧ s.2.1.size = c ∧ s.2.2.1.size = c ∧
    (∀ i < c, s.1[i]! = unpack n w (T i)) ∧
    (∀ x, s.2.2.2.contains x = true ↔ ∃ i < c, unpack n w (T i) = x) ∧
    (∀ i < c, i ≠ 0 → s.2.1[i]! < i ∧ s.2.2.1[i]! < ng ∧
      s.1[i]! = step s.2.2.1[i]! s.1[s.2.1[i]!]!)

structure PinW (n w ng N : Nat) (st : Nat → Nat → Nat) (step : Nat → Tab → Tab) (T : Nat → Nat) :
    Prop where
  canT : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true
  inj : ∀ a < N, ∀ b < N, T a = T b → a = b
  step : ∀ j < ng, ∀ h < N, step j (unpack n w (T h)) = unpack n w (st j (T h))

section Search

variable {n w ng N ew : Nat} {st : Nat → Nat → Nat} {step : Nat → Tab → Tab} {T E : Nat → Nat}

theorem PinW.uinj (P : PinW n w ng N st step T) {a b : Nat} (ha : a < N) (hb : b < N)
    (e : unpack n w (T a) = unpack n w (T b)) : a = b :=
  P.inj a ha b hb (unpack_inj' (P.canT a ha) (P.canT b hb) e)

theorem pinW_inner (P : PinW n w ng N st step T) {h j c : Nat} (hh : h < c) (hj : j < ng)
    {s : St} (hI : PInvW n w ng step T c s)
    (h0 : genStepW st T ew (T h) (E h) j c ≠ 0)
    (hN : genStepW st T ew (T h) (E h) j c ≤ N) :
    ∃ s', innerBody step (unpack n w (T h)) h j s = pure (ForInStep.yield s') ∧
      PInvW n w ng step T (genStepW st T ew (T h) (E h) j c) s' := by
  obtain ⟨h1, h2, h3, hget, hK, htr⟩ := hI
  have hcN : c ≤ N := le_trans (genStepW_spec rfl h0).2.1 hN
  have hy := P.step j hj h (by omega)
  have e := genStepW_eq st T ew (T h) (E h) j c
  generalize fget (E h) j ew = q at e
  generalize hY : st j (T h) = y at e hy
  have hc0 : c ≠ 0 := by omega
  rw [ite_eq_right hc0] at e
  by_cases hlt : q < c
  · rw [ite_eq_left hlt] at e
    by_cases hT : T q = y
    · rw [ite_eq_left hT] at e
      rw [e]
      have hc : s.2.2.2.contains (unpack n w y) = true := (hK _).2 ⟨q, hlt, by rw [hT]⟩
      exact ⟨(s.1, s.2.1, s.2.2.1, s.2.2.2), by simp [innerBody, hy, hc],
        h1, h2, h3, hget, hK, htr⟩
    · rw [ite_eq_right hT] at e
      exact absurd e h0
  · rw [ite_eq_right hlt] at e
    by_cases heq : q = c
    · by_cases hT : T c = y
      · rw [ite_eq_left heq, ite_eq_left hT] at e
        rw [e] at hN ⊢
        have hnc : s.2.2.2.contains (unpack n w y) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          obtain ⟨i, hi, ei⟩ := (hK _).1 hc
          rw [← hT] at ei
          have := P.uinj (by omega) (by omega) ei
          omega
        refine ⟨(s.1.push (unpack n w y), s.2.1.push h, s.2.2.1.push j,
          s.2.2.2.insert (unpack n w y) s.1.size), by simp [innerBody, hy, hnc],
          by simp [h1], by simp [h2], by simp [h3], fun i hi => ?_, fun x => ?_,
          fun i hi hi0 => ?_⟩
        · rcases Nat.lt_or_ge i c with a | a
          · change (s.1.push _)[i]! = _
            rw [push_lt (by omega)]
            exact hget i a
          · have ei : i = s.1.size := by omega
            subst ei
            change (s.1.push _)[s.1.size]! = _
            rw [push_eq, h1, hT]
        · change (s.2.2.2.insert _ _).contains x = true ↔ _
          rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hK]
          constructor
          · rintro (ex | ⟨i, hi, ex⟩)
            · exact ⟨c, by omega, by rw [hT, ex]⟩
            · exact ⟨i, by omega, ex⟩
          · rintro ⟨i, hi, ex⟩
            rcases Nat.lt_or_ge i c with a | a
            · exact Or.inr ⟨i, a, ex⟩
            · have ei : i = c := by omega
              subst ei
              rw [← ex, hT]
              exact Or.inl rfl
        · change (s.2.1.push h)[i]! < i ∧ (s.2.2.1.push j)[i]! < ng ∧
            (s.1.push _)[i]! =
              step (s.2.2.1.push j)[i]! (s.1.push _)[(s.2.1.push h)[i]!]!
          rcases Nat.lt_or_ge i c with a | a
          · obtain ⟨t1, t2, t3⟩ := htr i a hi0
            rw [push_lt (by omega : i < s.2.1.size), push_lt (by omega : i < s.2.2.1.size),
              push_lt (by omega : i < s.1.size), push_lt (by omega : s.2.1[i]! < s.1.size)]
            exact ⟨t1, t2, t3⟩
          · have ei : i = c := by omega
            subst ei
            have e2 : (s.2.1.push h)[i]! = h := by rw [← h2]; exact push_eq
            have e3 : (s.2.2.1.push j)[i]! = j := by rw [← h3]; exact push_eq
            have e1 : (s.1.push (unpack n w y))[i]! = unpack n w y := by rw [← h1]; exact push_eq
            rw [e1, e2, e3, push_lt (by omega : h < s.1.size), hget h hh, hy]
            exact ⟨hh, hj, rfl⟩
      · rw [ite_eq_left heq, ite_eq_right hT] at e
        exact absurd e h0
    · rw [ite_eq_right heq] at e
      exact absurd e h0

theorem pinW_point (P : PinW n w ng N st step T) {h c : Nat} (hh : h < c) {s : St}
    (hI : PInvW n w ng step T c s) (h0 : pointStepW ng st T E ew h c ≠ 0)
    (hN : pointStepW ng st T E ew h c ≤ N) :
    PInvW n w ng step T (pointStepW ng st T E ew h c)
      (Id.run (forIn (List.range' 0 ng) (s.1, s.2.1, s.2.2.1, s.2.2.2)
        (innerBody step (unpack n w (T h)) h))) := by
  rw [pointStepW_eq] at h0 hN ⊢
  have hfin : ∀ j ≤ ng, pointFW st T E ew h j 0 c ≠ 0 ∧ pointFW st T E ew h j 0 c ≤ N := by
    intro j hj
    have e := pointFW_add (st := st) (T := T) (E := E) (ew := ew) h j (ng - j) 0 c
    rw [Nat.add_sub_cancel' hj, Nat.zero_add] at e
    have hj0 : pointFW st T E ew h j 0 c ≠ 0 := by
      intro z
      rw [z, pointFW_zero] at e
      exact h0 e
    exact ⟨hj0, le_trans (pointFW_le e.symm h0) hN⟩
  have := forIn_range'_yield ng 0 (s.1, s.2.1, s.2.2.1, s.2.2.2)
    (innerBody step (unpack n w (T h)) h)
    (fun j s' => PInvW n w ng step T (pointFW st T E ew h j 0 c) s')
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      have e : pointFW st T E ew h (j + 1) 0 c =
          genStepW st T ew (T h) (E h) j (pointFW st T E ew h j 0 c) := by
        rw [pointFW_add h j 1 0 c, Nat.zero_add]
        rfl
      have hc := (hfin (j + 1) (by omega))
      rw [e] at hc ⊢
      have hle := pointFW_le (st := st) (T := T) (E := E) (ew := ew) (i := h) (len := j) (lo := 0)
        (c := c) rfl (hfin j (by omega)).1
      exact pinW_inner P (by omega) hj hP hc.1 hc.2)
    hI
  exact this

theorem pinW_outer (P : PinW n w ng N st step T) {cap : Nat} (hcap : N ≤ cap) (hN0 : N ≠ 0)
    {root : Tab} (hrun : runFW ng st T E ew N 0 1 = N) (hT0 : root = unpack n w (T 0)) :
    PInvW n w ng step T N
      (Id.run (forIn (List.range' 0 cap) (initSt root cap) (outerBody step ng))) := by
  refine forIn_range'_done cap 0 (initSt root cap) (outerBody step ng)
    (fun h s => h ≤ N ∧ ∃ c, h ≤ c ∧ PInvW n w ng step T c s ∧
      runFW ng st T E ew (N - h) h c = N)
    (PInvW n w ng step T N) (fun h hh s hP => ?_) (fun s hP => ?_)
    ⟨Nat.zero_le _, 1, Nat.zero_le _, ?_, by rw [Nat.sub_zero]; exact hrun⟩
  · obtain ⟨hhN, c, hhc, hI, hr⟩ := hP
    rw [Nat.zero_add]
    rcases Nat.lt_or_ge h N with a | a
    · have e : N - h = (N - (h + 1)) + 1 := by omega
      rw [e, runFW_succ] at hr
      cases hb : Nat.blt h c
      · rw [hb] at hr
        change runFW ng st T E ew _ (Nat.succ h) 0 = N at hr
        rw [runFW_zero] at hr
        exact absurd hr.symm hN0
      · rw [hb] at hr
        change runFW ng st T E ew _ (Nat.succ h) (pointStepW ng st T E ew h c) = N at hr
        have hlt : h < c := Nat.blt_eq.mp hb
        have hp0 : pointStepW ng st T E ew h c ≠ 0 := by
          intro z
          rw [z, runFW_zero] at hr
          exact hN0 hr.symm
        have hpN := runFW_le hr hN0
        have hpc := pointFW_le (pointStepW_eq h c).symm hp0
        have hhs : h < s.1.size := by rw [hI.1]; exact hlt
        have hsh : s.1[h]! = unpack n w (T h) := hI.2.2.2.1 h hlt
        refine Or.inl ⟨Id.run (forIn (List.range' 0 ng) (s.1, s.2.1, s.2.2.1, s.2.2.2)
          (innerBody step (unpack n w (T h)) h)), ?_, by omega, _, by omega,
          pinW_point P hlt hI hp0 hpN, hr⟩
        rw [outerBody, ite_eq_left hhs, hsh]
    · have e : h = N := by omega
      subst e
      rw [Nat.sub_self] at hr
      change c = h at hr
      subst hr
      have hns : ¬ c < s.1.size := by rw [hI.1]; exact Nat.lt_irrefl _
      exact Or.inr ⟨_, by simp [outerBody, hns], hI⟩
  · obtain ⟨hcN, c, hc, hI, hr⟩ := hP
    have e : cap = N := by omega
    subst e
    rw [Nat.sub_self] at hr
    change c = cap at hr
    subst hr
    exact hI
  · refine ⟨rfl, rfl, rfl, fun i hi => ?_, fun x => ?_, fun i hi hi0 => absurd hi (by omega)⟩
    · have e : i = 0 := by omega
      subst e
      simp [initSt, hT0]
    · simp only [initSt]
      rw [Std.HashMap.contains_insert, Std.HashMap.contains_emptyWithCapacity, Bool.or_false,
        beq_iff_eq, hT0]
      constructor
      · intro e
        exact ⟨0, by omega, e⟩
      · rintro ⟨i, hi, e⟩
        have : i = 0 := by omega
        subst this
        exact e

end Search

theorem bfs_of_runW {n w ng N ew cap : Nat} {st : Nat → Nat → Nat} {step : Nat → Tab → Tab}
    {T E : Nat → Nat} {root : Tab} (P : PinW n w ng N st step T)
    (hrun : runFW ng st T E ew N 0 1 = N) (hroot : root = unpack n w (T 0)) (hcap : N ≤ cap) :
    (bfs step ng root cap).tabs = Array.ofFn (n := N) (fun i => unpack n w (T i.val)) ∧
      treeOK step ng root (bfs step ng root cap) = true := by
  have hN0 : N ≠ 0 := by
    intro e
    subst e
    have e1 : runFW ng st T E ew 0 0 1 = 1 := rfl
    omega
  have hcl : ∀ i < N, ∀ j < ng, ∃ q < N, T q = st j (T i) := by
    have := (runFW_cl N 0 1 N hrun hN0 (fun i hi => absurd hi (by omega))).2
    intro i hi j hj
    exact this i (by omega) j hj
  have hO := pinW_outer P hcap hN0 hrun hroot
  rw [bfs_eq]
  generalize Id.run (forIn (List.range' 0 cap) (initSt root cap) (outerBody step ng)) = s at hO
  obtain ⟨h1, h2, h3, hget, -, htr⟩ := hO
  have htabs : s.1 = Array.ofFn (n := N) fun i => unpack n w (T i.val) := by
    apply Array.ext
    · simp [h1]
    · intro i hi1 hi2
      rw [Array.getElem_ofFn, ← getElem!_pos s.1 i hi1, hget i (by omega)]
  refine ⟨htabs, ?_⟩
  unfold treeOK
  simp only
  have hinj : ∀ a < s.1.size, ∀ b < s.1.size, s.1[a]! = s.1[b]! → a = b := fun a ha b hb e => by
    rw [hget a (by omega), hget b (by omega)] at e
    exact P.uinj (by omega) (by omega) e
  obtain ⟨hi1, -⟩ := CFSG.KS.BfsReplay.indexOf_spec hinj
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨by omega, by rw [hget 0 (by omega), hroot]⟩,
    CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => ?_⟩
  rw [h1] at hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨?_, CFSG.KS.BfsReplay.allBelow_iff.2 fun j hj => ?_⟩, ?_⟩
  · unfold posOf
    exact hi1 i (by omega)
  · obtain ⟨q, hq, hx⟩ := hcl i hi j hj
    have e : step j s.1[i]! = s.1[q]! := by
      rw [hget i hi, hget q hq, hx, P.step j hj i hi]
    unfold found posOf
    rw [e, hi1 q (by omega)]
    simp [h1, hq]
  · by_cases h0 : i = 0
    · exact Or.inl h0
    · right
      obtain ⟨a1, a2, a3⟩ := htr i hi h0
      exact ⟨⟨a1, a2⟩, a3⟩

end CFSG.KC.L34KSnd

end
