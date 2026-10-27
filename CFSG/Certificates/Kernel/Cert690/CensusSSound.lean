module

public import Certificates.Data.Kernel.Cert690.CensusS
public import CFSG.Certificates.Kernel.Cert690.TreeSound
import CFSG.Certificates.Kernel.Cert690.MulSound

public section

namespace CFSG.KC.C690S

open CFSG.KC.C690 CFSG.KC.Enum

theorem boolRec_eqS (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = (c && t || !c && e) := by
  cases c <;> simp

theorem beq_eqS (a b : Nat) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, decide_eq_true_iff])

theorem blt_eqS (a b : Nat) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_iff])

theorem ble_eqS (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.ble_eq, decide_eq_true_iff])

theorem nIf_eqS (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem strictN_eqS (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem nthS_eq {α : Type} (d : α) (l : List α) (n : Nat) : nthS d l n = l.getD n d := by
  induction l generalizing n with
  | nil => rfl
  | cons x l ih =>
    cases n with
    | zero => rfl
    | succ k => rw [List.getD_cons_succ, ← ih k]; rfl

theorem lenS_eq {α : Type} (l : List α) : lenS l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => change Nat.succ (lenS l) = _; rw [ih]; rfl

theorem allS_eq_true {α : Type} (f : α → Bool) (l : List α) :
    allS f l = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact iff_of_true rfl (fun _ h => absurd h List.not_mem_nil)
  | cons x l ih =>
    change Bool.rec (motive := fun _ => Bool) false (allS f l) (f x) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem memS_eq_true (x : Nat) (l : List Nat) : memS x l = true ↔ x ∈ l := by
  induction l with
  | nil => exact iff_of_false Bool.false_ne_true List.not_mem_nil
  | cons y l ih =>
    change Bool.rec (motive := fun _ => Bool) (memS x l) true (Nat.beq x y) = true ↔ _
    rw [boolRec_eqS, beq_eqS]
    by_cases h : x = y <;> simp [h, ih]

theorem zipS_eq_true {α β : Type} (f : α → β → Bool) (l₁ : List α) (l₂ : List β) :
    zipS f l₁ l₂ = true ↔ List.Forall₂ (fun a b => f a b = true) l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact iff_of_true rfl List.Forall₂.nil
    | cons y l₂ => exact iff_of_false Bool.false_ne_true (fun h => by cases h)
  | cons x l₁ ih =>
    cases l₂ with
    | nil => exact iff_of_false Bool.false_ne_true (fun h => by cases h)
    | cons y l₂ =>
      change Bool.rec (motive := fun _ => Bool) false (zipS f l₁ l₂) (f x y) = true ↔ _
      rw [bAnd_eq, Bool.and_eq_true, ih, List.forall₂_cons]

theorem letS_eq (gens : List Nat) (ng r q : Nat) :
    letS gens ng r q = if q < ng then gens.getD q 0 else r := by
  unfold letS
  rw [nIf_eqS, nthS_eq, blt_eqS]
  simp

theorem lettersS_eq_true (n : Nat) (w : List Nat) : lettersS n w = true ↔ ∀ q ∈ w, q < n := by
  unfold lettersS
  rw [allS_eq_true]
  simp only [blt_eqS, decide_eq_true_eq]

@[expose] def gensS (B : SBase) (g : Nat) : List Nat := B.fg.getD g []

@[expose] def candS (B : SBase) (g : Nat) : Nat := B.fc.getD g 0

@[expose] def lgS (B : SBase) (g : Nat) : List Nat := B.LG.getD (candS B g) []

@[expose] def lcS (B : SBase) (g : Nat) : List Nat := B.LC.getD (candS B g) []

@[expose] def NorS (lg lc : List Nat) (y yi : Nat) : Prop := ∀ x ∈ lg, mulF (mulF y x) yi ∈ lc

@[expose] def BadS (b : Nat) (lg lc : List Nat) (x xi : Nat) : Prop :=
  ¬ (actS x b = b ↔ NorS lg lc x xi) ∨ ((∀ y ∈ lg, mulF x y = mulF y x) ∧ pow128 x ≠ oneF)

@[expose] noncomputable def cListS (wv : List Nat) (cpar : List (Nat × Nat)) : List Nat :=
  cpar.foldl (fun C pq => C ++ [mulF (C.getD pq.1 0) (wv.getD pq.2 0)]) [oneF]

structure CoverFacts (nS spk : Nat) (gens : List Nat) (wg : List (List Nat))
    (cpar : List (Nat × Nat)) (T : List (Nat × Nat)) : Prop where
  letters : ∀ w ∈ wg, ∀ q ∈ w, q < gens.length
  par : ∀ i (hi : i < cpar.length), cpar[i].1 ≤ i ∧ cpar[i].2 < wg.length
  tr : ∀ t ∈ T, t.1 < nS ∧ t.2 < nS ∧ mulF (fS spk t.1) (fS spk t.2) = oneF
  cover : ∀ ρ < nS, ∃ t ∈ T, ∃ k, fS spk ρ = mulF (fS spk t.1)
    ((cListS (wg.map fun w => wvS (nthS 0 gens) w oneF) cpar).getD k 0)

@[expose] def RecOK (B : SBase) (g ci : Nat) (lg lc gens ginv : List Nat) (r ri : Nat)
    (h : List Nat) (ws : List (List Nat)) : Prop :=
  (h.getD 0 9 = 0 ∧ (∀ q ∈ ws.getD 0 [], q < gens.length + 1) ∧
    BadS B.b lg lc (wvS (letS gens gens.length r) (ws.getD 0 []) oneF)
      (wiS (letS ginv gens.length ri) (ws.getD 0 []) oneF)) ∨
  (h.getD 0 9 = 1 ∧ g < h.getD 1 0 ∧ h.getD 1 0 < B.nF ∧ B.fc.getD (h.getD 1 0) 0 = ci ∧
    h.getD 2 0 < B.nS ∧ h.getD 3 0 < B.nS ∧
    mulF (fS B.spk (h.getD 2 0)) (fS B.spk (h.getD 3 0)) = oneF ∧
    NorS lg lc (fS B.spk (h.getD 2 0)) (fS B.spk (h.getD 3 0)) ∧
    List.Forall₂ (fun w x => (∀ q ∈ w, q < gens.length + 1) ∧
        wvS (letS gens gens.length r) w oneF =
          mulF (mulF (fS B.spk (h.getD 2 0)) x) (fS B.spk (h.getD 3 0)))
      ws (B.fg.getD (h.getD 1 0) [])) ∨
  (h.getD 0 9 = 2 ∧ r = oneF)

@[expose] def BothS (gens tg : List Nat) (wa wb : List (List Nat)) : Prop :=
  List.Forall₂ (fun w x => (∀ q ∈ w, q < gens.length) ∧ wvS (nthS 0 gens) w oneF = x) wa tg ∧
  List.Forall₂ (fun w x => (∀ q ∈ w, q < tg.length) ∧ wvS (nthS 0 tg) w oneF = x) wb gens

@[expose] def ClsOK (B : SBase) (gens : List Nat) (h : List Nat) (wa wb : List (List Nat)) :
    Prop :=
  (h.getD 0 0 = 1 ∧ 0 < h.getD 1 0 ∧ h.getD 1 0 < 64 ∧ h.tail.tail.length ≤ 5 ∧
    (∀ x ∈ h.tail.tail, x < 64) ∧ h.getD 1 0 ∈ spanS h.tail.tail [0] ∧
    ∀ x ∈ gens, ∀ y ∈ h.tail.tail, actS x y ∈ spanS h.tail.tail [0]) ∨
  (h.getD 0 0 = 2 ∧ BothS gens B.omg wa wb) ∨
  (h.getD 0 0 = 3 ∧ BothS gens B.og wa wb) ∨
  (h.getD 0 0 = 4 ∧ B.pglOK = true ∧ h.getD 1 0 ∈ B.pglc ∧
    mulF (h.getD 1 0) (h.getD 2 0) = oneF ∧
    BothS gens (B.kpg.map fun x => mulF (mulF (h.getD 1 0) x) (h.getD 2 0)) wa wb)

structure CheckFFacts (B : SBase) (g : Nat) (ginv : List Nat) (wg : List (List Nat))
    (cpar : List (Nat × Nat)) (T : List (Nat × Nat)) (reps : List Nat)
    (recs : List (List (List Nat × List (List Nat))))
    (cls : List Nat × List (List Nat) × List (List Nat)) : Prop where
  lt : g < B.nF
  inv : List.Forall₂ (fun x y => mulF x y = oneF) (gensS B g) ginv
  cover : CoverFacts B.nS B.spk (gensS B g) wg cpar T
  repsSing : ∀ p ∈ reps, p ∈ B.sing
  orbChain : ∀ q ∈ B.sing, ∃ p ∈ reps, ∃ js : List Nat, (∀ j ∈ js, j < (gensS B g).length) ∧
    q = js.foldr (fun j v => actS ((gensS B g).getD j 0) v) p
  recsOK : List.Forall₂ (fun p rs => List.Forall₂ (fun u e =>
      RecOK B g (candS B g) (lgS B g) (lcS B g) (gensS B g) ginv
        (mulF (B.tpT.getD p 0) (fS B.spk u.1)) (mulF (fS B.spk u.2) (B.tpI.getD p 0)) e.1 e.2)
      T rs) reps recs
  clsOK : ClsOK B (gensS B g) cls.1 cls.2.1 cls.2.2

theorem mulF_ltS (a b : Nat) : mulF a b < 2 ^ 36 := by
  have hl : ∀ k, mtF a b k < 2 ^ 36 := mtF_lt a b
  unfold mulF
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hl _) (hl _))
    (Nat.xor_lt_two_pow (hl _) (hl _))) (Nat.xor_lt_two_pow (hl _) (hl _))

theorem oneF_ltS : oneF < 2 ^ 36 := by
  unfold oneF
  norm_num

theorem fS_eqS (c k : Nat) : fS c k = (c >>> (36 * k)) &&& (2 ^ 36 - 1) := rfl

def PackS (c : Nat) (C : List Nat) : Prop :=
  ∀ n, c.testBit n = (C.getD (n / 36) 0).testBit (n % 36)

theorem getD_ltS {C : List Nat} (hC : ∀ x ∈ C, x < 2 ^ 36) (k : Nat) : C.getD k 0 < 2 ^ 36 := by
  rcases lt_or_ge k C.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hC _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    positivity

theorem fS_of_packS {c : Nat} {C : List Nat} (hc : PackS c C) (hC : ∀ x ∈ C, x < 2 ^ 36)
    (k : Nat) : fS c k = C.getD k 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [fS_eqS, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, hc]
  by_cases hj : j < 36
  · have e1 : (36 * k + j) / 36 = k := by omega
    have e2 : (36 * k + j) % 36 = j := by omega
    simp [e1, e2, hj]
  · have : (C.getD k 0).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (getD_ltS hC k)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [this, decide_eq_false hj, Bool.and_false]

theorem packS_snoc {c : Nat} {C : List Nat} (hc : PackS c C) {x : Nat} (hx : x < 2 ^ 36) :
    PackS (c ||| (x <<< (36 * C.length))) (C ++ [x]) := by
  intro n
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, hc]
  rcases lt_trichotomy (n / 36) C.length with h | h | h
  · rw [List.getD_append _ _ _ _ h]
    have : ¬ (n ≥ 36 * C.length) := by omega
    simp [this]
  · have h1 : C.getD (n / 36) 0 = 0 := List.getD_eq_default _ _ (by omega)
    have h2 : (C ++ [x]).getD (n / 36) 0 = x := by
      rw [List.getD_append_right _ _ _ _ (by omega), h, Nat.sub_self]
      rfl
    have h3 : n - 36 * C.length = n % 36 := by omega
    have h4 : n ≥ 36 * C.length := by omega
    rw [h1, h2, h3, decide_eq_true h4, Nat.zero_testBit, Bool.false_or, Bool.true_and]
  · have h1 : C.getD (n / 36) 0 = 0 := List.getD_eq_default _ _ (by omega)
    have h2 : (C ++ [x]).getD (n / 36) 0 = 0 :=
      List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)
    have h3 : x.testBit (n - 36 * C.length) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [h1, h2, h3, Nat.zero_testBit, Bool.and_false, Bool.false_or]

theorem cBuild_consS (wv : List Nat) (pq : Nat × Nat) (cpar : List (Nat × Nat)) (i c : Nat) :
    cBuild wv (pq :: cpar) i c = cBuild wv cpar (i + 1)
      (c ||| (mulF (fS c pq.1) (wv.getD pq.2 0) <<< (36 * i))) := by
  change strictN (Nat.lor c (Nat.shiftLeft (mulF (fS c pq.1) (nthS (nat_lit 0) wv pq.2))
    (Nat.mul (nat_lit 36) i))) (cBuild wv cpar (Nat.succ i)) = _
  rw [strictN_eqS, nthS_eq]
  rfl

theorem cBuild_packS (wv : List Nat) (cpar : List (Nat × Nat)) : ∀ (C : List Nat) (c : Nat),
    PackS c C → (∀ x ∈ C, x < 2 ^ 36) →
    PackS (cBuild wv cpar C.length c)
      (cpar.foldl (fun C pq => C ++ [mulF (C.getD pq.1 0) (wv.getD pq.2 0)]) C) ∧
    ∀ x ∈ cpar.foldl (fun C pq => C ++ [mulF (C.getD pq.1 0) (wv.getD pq.2 0)]) C, x < 2 ^ 36 := by
  induction cpar with
  | nil => exact fun C c hc hC => ⟨hc, hC⟩
  | cons pq cpar ih =>
    intro C c hc hC
    rw [cBuild_consS, fS_of_packS hc hC, List.foldl_cons]
    have hl : C.length + 1 = (C ++ [mulF (C.getD pq.1 0) (wv.getD pq.2 0)]).length := by simp
    rw [hl]
    refine ih _ _ (packS_snoc hc (mulF_ltS _ _)) ?_
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hC x hx
    · rw [List.mem_singleton.mp hx]
      exact mulF_ltS _ _

theorem fS_cBuildS (wv : List Nat) (cpar : List (Nat × Nat)) (k : Nat) :
    fS (cBuild wv cpar 1 oneF) k = (cListS wv cpar).getD k 0 := by
  have h0 : PackS oneF [oneF] := by
    intro n
    by_cases hn : n < 36
    · have e1 : n / 36 = 0 := by omega
      have e2 : n % 36 = n := by omega
      rw [e1, e2]
      rfl
    · have e1 : [oneF].getD (n / 36) 0 = 0 := List.getD_eq_default _ _ (by simp; omega)
      rw [e1, Nat.zero_testBit]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le oneF_ltS
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h1 : ∀ x ∈ [oneF], x < 2 ^ 36 := by
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact oneF_ltS
  obtain ⟨hp, hl⟩ := cBuild_packS wv cpar [oneF] oneF h0 h1
  exact fS_of_packS hp hl k

theorem coverU_bitsS (spk cpk u pz nS : Nat) (hpz : ∀ n, pz.testBit n = true → n = nS)
    (ρs : List Nat) : ∀ (k s n : Nat), (coverU spk cpk u pz ρs k s).testBit n = true →
      s.testBit n = true ∨ n = nS ∨ ∃ k', fS spk n = mulF u (fS cpk k') := by
  induction ρs with
  | nil => exact fun k s n h => Or.inl h
  | cons ρ ρs ih =>
    intro k s n h
    change Nat.testBit (strictN (Nat.lor s (Bool.rec (motive := fun _ => Nat) pz
      (Nat.shiftLeft (nat_lit 1) ρ) (Nat.beq (fS spk ρ) (mulF u (fS cpk k)))))
      (coverU spk cpk u pz ρs (Nat.succ k))) n = true at h
    rw [strictN_eqS, nIf_eqS, beq_eqS] at h
    rcases ih _ _ _ h with h | h | h
    · change (s ||| _).testBit n = true at h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Or.inl h
      · by_cases hm : fS spk ρ = mulF u (fS cpk k)
        · rw [if_pos (by simpa using hm)] at h
          change (1 <<< ρ).testBit n = true at h
          rw [Nat.testBit_shiftLeft] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          have : n = ρ := by
            have := Nat.testBit_one_eq_true_iff_self_eq_zero.mp h.2
            omega
          subst this
          exact Or.inr (Or.inr ⟨k, hm⟩)
        · rw [if_neg (by simpa using hm)] at h
          exact Or.inr (Or.inl (hpz n h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem coverT_bitsS (spk cpk pz nS : Nat) (hpz : ∀ n, pz.testBit n = true → n = nS)
    (T : List (Nat × Nat)) : ∀ (R : List (List Nat)) (s n : Nat),
      (coverT spk cpk pz T R s).testBit n = true →
      s.testBit n = true ∨ n = nS ∨ ∃ t ∈ T, ∃ k, fS spk n = mulF (fS spk t.1) (fS cpk k) := by
  have hor : ∀ s n, (Nat.lor s pz).testBit n = true → s.testBit n = true ∨ n = nS := by
    intro s n h
    change (s ||| pz).testBit n = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    exact h.imp id (hpz n)
  induction T with
  | nil =>
    intro R s n h
    cases R with
    | nil => exact Or.inl h
    | cons r R => exact (hor s n h).imp id Or.inl
  | cons t T ih =>
    intro R s n h
    cases R with
    | nil => exact (hor s n h).imp id Or.inl
    | cons ρs R =>
      change Nat.testBit (strictN (coverU spk cpk (fS spk t.1) pz ρs (nat_lit 0) s)
        (coverT spk cpk pz T R)) n = true at h
      rw [strictN_eqS] at h
      rcases ih R _ n h with h | h | ⟨t', ht', k, hk⟩
      · rcases coverU_bitsS spk cpk _ pz nS hpz ρs _ _ _ h with h | h | ⟨k, hk⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨t, List.mem_cons_self, k, hk⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨t', List.mem_cons_of_mem _ ht', k, hk⟩)

def ChS (reps gens : List Nat) (q : Nat) : Prop :=
  ∃ p ∈ reps, ∃ js : List Nat, (∀ j ∈ js, j < gens.length) ∧
    q = js.foldr (fun j v => actS (gens.getD j 0) v) p

theorem orbS_invS (sing reps gens qs : List Nat) (ng : Nat) (hng : ng = gens.length) :
    ∀ (l : List (Nat × Nat × Nat)) (D : List Nat) (seen : Nat),
      qs = D ++ l.map (fun e => e.1) → D.Nodup → (∀ x ∈ D, x ∈ sing) →
      (∀ x ∈ D, ChS reps gens x) → (∀ x, seen.testBit x = true ↔ x ∈ D) →
      orbS sing reps gens qs ng sing.length l D.length seen = true →
      ∀ q ∈ sing, ChS reps gens q := by
  intro l
  induction l with
  | nil =>
    intro D seen _ hD hDs hDc _ h
    change Nat.beq D.length sing.length = true at h
    rw [beq_eqS, decide_eq_true_eq] at h
    intro q hq
    have hperm := (hD.subperm hDs).perm_of_length_le (by omega)
    exact hDc q (hperm.mem_iff.mpr hq)
  | cons e l ih =>
    intro D seen hq hD hDs hDc hs h
    obtain ⟨q, a, j⟩ := e
    change bAnd(memS q sing, bAnd(Nat.beq (fld(seen, q, nat_lit 1)) (nat_lit 0),
      bAnd(bIf(Nat.beq j (nat_lit 0), memS q reps,
        bAnd(bAnd(Nat.blt a D.length, Nat.ble j ng),
          Nat.beq (actS (nthS (nat_lit 0) gens (Nat.sub j (nat_lit 1))) (nthS (nat_lit 0) qs a)) q)),
      orbS sing reps gens qs ng sing.length l (Nat.succ D.length)
        (Nat.lor seen (Nat.shiftLeft (nat_lit 1) q))))) = true at h
    rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      memS_eq_true] at h
    obtain ⟨hqs, hfresh, hpar, hrest⟩ := h
    have hnot : q ∉ D := by
      intro hm
      have h1 := (hs q).mpr hm
      have e : seen.testBit q = ((seen >>> q) &&& 1 != 0) := by
        rw [Nat.and_comm]
        rfl
      rw [e] at h1
      change (Nat.land (Nat.shiftRight seen q) 1 != 0) = true at h1
      rw [Nat.eq_of_beq_eq_true hfresh] at h1
      exact Bool.false_ne_true h1
    have hch : ChS reps gens q := by
      by_cases hj : j = 0
      · have e0 : Nat.beq j (nat_lit 0) = true := by
          rw [beq_eqS]
          exact decide_eq_true hj
        rw [e0] at hpar
        dsimp only at hpar
        exact ⟨q, (memS_eq_true _ _).mp hpar, [], fun _ h => absurd h List.not_mem_nil, rfl⟩
      · have e0 : Nat.beq j (nat_lit 0) = false := by
          rw [beq_eqS]
          exact decide_eq_false hj
        rw [e0] at hpar
        dsimp only at hpar
        rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, blt_eqS, ble_eqS, beq_eqS,
          decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq, nthS_eq, nthS_eq] at hpar
        obtain ⟨⟨ha, hjn⟩, hact⟩ := hpar
        have hqa : qs.getD a 0 = D[a] := by
          rw [hq, List.getD_append _ _ _ _ ha, List.getD_eq_getElem _ _ ha]
        rw [hqa] at hact
        obtain ⟨p, hp, js, hjs, hx⟩ := hDc _ (List.getElem_mem ha)
        refine ⟨p, hp, (j - 1) :: js, ?_, ?_⟩
        · intro i hi
          rcases List.mem_cons.mp hi with hi | hi
          · omega
          · exact hjs i hi
        · rw [List.foldr_cons, ← hx]
          exact hact.symm
    have hl : (D ++ [q]).length = Nat.succ D.length := by simp
    rw [← hl] at hrest
    refine ih (D ++ [q]) _ (by rw [hq, List.map_cons, List.append_assoc]; rfl) ?_ ?_ ?_ ?_ hrest
    · exact List.nodup_append_comm.mpr (List.nodup_cons.mpr ⟨hnot, hD⟩)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hDs x hx
      · rw [List.mem_singleton.mp hx]
        exact hqs
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hDc x hx
      · rw [List.mem_singleton.mp hx]
        exact hch
    · intro x
      change (seen ||| 1 <<< q).testBit x = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, hs, Nat.testBit_shiftLeft, Bool.and_eq_true,
        decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero, List.mem_append,
        List.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by omega)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by omega)

theorem coverT_sound (nS spk : Nat) (wv : List Nat) (cpar : List (Nat × Nat))
    (T : List (Nat × Nat)) (ranks : List (List Nat))
    (h : Nat.beq (coverT spk (cBuild wv cpar 1 oneF) (Nat.shiftLeft 1 nS) T ranks 0)
      (Nat.sub (Nat.shiftLeft 1 nS) 1) = true) :
    ∀ ρ < nS, ∃ t ∈ T, ∃ k, fS spk ρ = mulF (fS spk t.1) ((cListS wv cpar).getD k 0) := by
  intro ρ hρ
  have hpz : ∀ n, (Nat.shiftLeft 1 nS).testBit n = true → n = nS := by
    intro n hn
    change (1 <<< nS).testBit n = true at hn
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
      Nat.testBit_one_eq_true_iff_self_eq_zero] at hn
    omega
  rw [beq_eqS, decide_eq_true_eq] at h
  have hb : (coverT spk (cBuild wv cpar 1 oneF) (Nat.shiftLeft 1 nS) T ranks 0).testBit ρ =
      true := by
    rw [h]
    change (1 <<< nS - 1).testBit ρ = true
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hρ
  rcases coverT_bitsS spk _ _ nS hpz T ranks 0 ρ hb with h0 | h0 | ⟨t, ht, k, hk⟩
  · rw [Nat.zero_testBit] at h0
    exact absurd h0 Bool.false_ne_true
  · omega
  · exact ⟨t, ht, k, by rw [hk, fS_cBuildS]⟩

theorem orbS_sound (sing reps gens : List Nat) (orb : List (Nat × Nat × Nat))
    (h : orbS sing reps gens (orb.map fun e => e.1) (lenS gens) (lenS sing) orb 0 0 = true) :
    ∀ q ∈ sing, ∃ p ∈ reps, ∃ js : List Nat, (∀ j ∈ js, j < gens.length) ∧
      q = js.foldr (fun j v => actS (gens.getD j 0) v) p := by
  rw [lenS_eq sing] at h
  exact orbS_invS sing reps gens _ (lenS gens) (lenS_eq gens) orb [] 0 (by simp) List.nodup_nil
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun x => by simp) h

theorem cparS_sound (nw : Nat) (cpar : List (Nat × Nat)) (i : Nat)
    (h : cparS nw cpar i = true) :
    ∀ j (hj : j < cpar.length), cpar[j].1 ≤ i + j ∧ cpar[j].2 < nw := by
  induction cpar generalizing i with
  | nil => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | cons pq cpar ih =>
    change Bool.rec (motive := fun _ => Bool) false (cparS nw cpar (Nat.succ i))
      (Bool.rec (motive := fun _ => Bool) false (Nat.blt pq.2 nw) (Nat.ble pq.1 i)) = true at h
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, ble_eqS, blt_eqS,
      decide_eq_true_eq, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    intro j hj
    cases j with
    | zero => exact ⟨by simpa using h1, h2⟩
    | succ j =>
      obtain ⟨a, b⟩ := ih (Nat.succ i) h3 j (by simpa using hj)
      exact ⟨by simp only [List.getElem_cons_succ]; omega, by simpa using b⟩

theorem coverS_sound {nS spk : Nat} {gens : List Nat} {wg : List (List Nat)}
    {cpar : List (Nat × Nat)} {T : List (Nat × Nat)} {ranks : List (List Nat)}
    (h : coverS nS spk gens wg cpar T ranks = true) : CoverFacts nS spk gens wg cpar T := by
  unfold coverS at h
  simp only [bAnd_eq, Bool.and_eq_true, strictB_eq] at h
  obtain ⟨hl, hp, ht, hc⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw q hq
    have := (allS_eq_true _ _).mp hl w hw
    rw [lettersS_eq_true, lenS_eq] at this
    exact this q hq
  · intro i hi
    have := cparS_sound _ _ 0 hp i hi
    rw [lenS_eq, Nat.zero_add] at this
    exact this
  · intro t ht'
    have := (allS_eq_true _ _).mp ht t ht'
    simp only [bAnd_eq, Bool.and_eq_true, blt_eqS, beq_eqS, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · exact coverT_sound nS spk _ cpar T ranks hc

theorem norS_iff (lg lc : List Nat) (y yi : Nat) : norS lg lc y yi = true ↔ NorS lg lc y yi := by
  unfold norS NorS
  rw [allS_eq_true]
  simp only [memS_eq_true]

theorem notOneS_iff (p : Nat) : notOneS p = true ↔ p ≠ oneF := by
  unfold notOneS
  rw [boolRec_eqS, beq_eqS]
  by_cases h : p = oneF <;> simp [h]

theorem badK_iff (b : Nat) (lg lc : List Nat) (x xi a : Nat) :
    badK b lg lc x xi a = true ↔
      ¬ (a = b ↔ NorS lg lc x xi) ∨ ((∀ y ∈ lg, mulF x y = mulF y x) ∧ pow128 x ≠ oneF) := by
  have hn := norS_iff lg lc x xi
  have hc : allS (fun y => Nat.beq (mulF x y) (mulF y x)) lg = true ↔
      ∀ y ∈ lg, mulF x y = mulF y x := by
    rw [allS_eq_true]
    simp only [beq_eqS, decide_eq_true_eq]
  have hp := notOneS_iff (pow128 x)
  unfold badK
  rw [strictB_eq]
  generalize norS lg lc x xi = n at hn ⊢
  generalize allS (fun y => Nat.beq (mulF x y) (mulF y x)) lg = m at hc ⊢
  generalize notOneS (pow128 x) = q at hp ⊢
  rw [← hn, ← hc, ← hp]
  beta_reduce
  by_cases h : a = b <;> cases n <;> cases m <;> cases q <;> simp [h, beq_eqS]

theorem badS_iff (b : Nat) (lg lc : List Nat) (x xi : Nat) :
    badS b lg lc x xi = true ↔ BadS b lg lc x xi := by
  unfold badS
  rw [strictB_eq, badK_iff]
  exact Iff.rfl

theorem closeW_iff (L : Nat → Nat) (na n ni : Nat) (ws : List (List Nat)) (tg : List Nat) :
    closeW L na n ni ws tg = true ↔ List.Forall₂ (fun w x => (∀ q ∈ w, q < na) ∧
      wvS L w oneF = mulF (mulF n x) ni) ws tg := by
  unfold closeW
  rw [zipS_eq_true]
  simp only [bAnd_eq, Bool.and_eq_true, lettersS_eq_true, beq_eqS, decide_eq_true_eq]

theorem closK_sound {lg lc : List Nat} {L : Nat → Nat} {na : Nat} {ws : List (List Nat)}
    {tg : List Nat} {n ni p : Nat} (H : closK lg lc L na ws tg n ni p = true) :
    p = oneF ∧ NorS lg lc n ni ∧ List.Forall₂ (fun w x => (∀ q ∈ w, q < na) ∧
      wvS L w oneF = mulF (mulF n x) ni) ws tg := by
  unfold closK at H
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, beq_eqS, decide_eq_true_eq,
    norS_iff, closeW_iff] at H
  exact H

theorem recS_sound {b nS spk nF g ci : Nat} {lg lc fc : List Nat} {fg : List (List Nat)}
    {gens ginv : List Nat} {r ri : Nat} {h : List Nat} {ws : List (List Nat)}
    (B : SBase) (hb : B.b = b) (hnS : B.nS = nS) (hspk : B.spk = spk) (hnF : B.nF = nF)
    (hfc : B.fc = fc) (hfg : B.fg = fg)
    (H : recS b nS spk nF g ci lg lc fc fg gens ginv r ri h ws = true) :
    RecOK B g ci lg lc gens ginv r ri h ws := by
  subst hb hnS hspk hnF hfc hfg
  unfold recS at H
  simp only [nthS_eq, lenS_eq] at H
  unfold RecOK
  obtain hT | hT | hT | hT : h.getD 0 9 = 0 ∨ h.getD 0 9 = 1 ∨ h.getD 0 9 = 2 ∨
      3 ≤ h.getD 0 9 := by omega
  · rw [hT] at H
    have e0 : Nat.beq 0 0 = true := rfl
    rw [e0] at H
    dsimp only at H
    simp only [bAnd_eq, Bool.and_eq_true, strictB_eq, lettersS_eq_true, badS_iff] at H
    exact Or.inl ⟨hT, H.1, H.2⟩
  · rw [hT] at H
    have e0 : Nat.beq 1 0 = false := rfl
    have e1 : Nat.beq 1 1 = true := rfl
    rw [e0, e1] at H
    dsimp only at H
    simp only [bAnd_eq, Bool.and_eq_true, strictB_eq, blt_eqS, beq_eqS, decide_eq_true_eq] at H
    obtain ⟨⟨h1, h2⟩, h3, ⟨h4, h5⟩, H⟩ := H
    obtain ⟨h6, h7, h8⟩ := closK_sound H
    exact Or.inr (Or.inl ⟨hT, h1, h2, h3, h4, h5, h6, h7, h8⟩)
  · rw [hT] at H
    have e0 : Nat.beq 2 0 = false := rfl
    have e1 : Nat.beq 2 1 = false := rfl
    have e2 : Nat.beq 2 2 = true := rfl
    rw [e0, e1, e2] at H
    dsimp only at H
    exact Or.inr (Or.inr ⟨hT, Nat.eq_of_beq_eq_true H⟩)
  · exfalso
    have e0 : Nat.beq (h.getD 0 9) 0 = false := by
      rw [beq_eqS]
      exact decide_eq_false (by omega)
    have e1 : Nat.beq (h.getD 0 9) 1 = false := by
      rw [beq_eqS]
      exact decide_eq_false (by omega)
    have e2 : Nat.beq (h.getD 0 9) 2 = false := by
      rw [beq_eqS]
      exact decide_eq_false (by omega)
    rw [e0, e1, e2] at H
    dsimp only at H
    exact Bool.false_ne_true H

theorem recsT_sound {b nS spk nF g ci : Nat} {lg lc fc : List Nat} {fg : List (List Nat)}
    {gens ginv : List Nat} {t ti : Nat} {T : List (Nat × Nat)}
    {rs : List (List Nat × List (List Nat))}
    (B : SBase) (hb : B.b = b) (hnS : B.nS = nS) (hspk : B.spk = spk) (hnF : B.nF = nF)
    (hfc : B.fc = fc) (hfg : B.fg = fg)
    (H : recsT b nS spk nF g ci lg lc fc fg gens ginv t ti T rs = true) :
    List.Forall₂ (fun u e => RecOK B g ci lg lc gens ginv (mulF t (fS spk u.1))
      (mulF (fS spk u.2) ti) e.1 e.2) T rs := by
  unfold recsT at H
  rw [zipS_eq_true] at H
  refine H.imp fun u e he => ?_
  simp only [strictB_eq] at he
  exact recS_sound B hb hnS hspk hnF hfc hfg he

theorem bothS_iff (gens tg : List Nat) (wa wb : List (List Nat)) :
    bothS gens tg wa wb = true ↔ BothS gens tg wa wb := by
  unfold bothS BothS
  simp only [bAnd_eq, Bool.and_eq_true, zipS_eq_true, lettersS_eq_true, lenS_eq, beq_eqS,
    decide_eq_true_eq]

theorem clsS_sound {B : SBase} {gens h : List Nat} {wa wb : List (List Nat)}
    (H : clsS B.pglOK B.og B.omg B.kpg B.pglc gens h wa wb = true) : ClsOK B gens h wa wb := by
  unfold clsS at H
  simp only [nthS_eq, lenS_eq, bAnd_eq] at H
  simp only [boolRec_eqS, beq_eqS, blt_eqS, ble_eqS, Bool.and_false, Bool.or_false,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, memS_eq_true, allS_eq_true, bothS_iff] at H
  unfold ClsOK
  rcases H with ⟨t1, ⟨h0, h64⟩, h5, hB, hv, hW⟩ | ⟨-, ⟨t2, hb2⟩ | ⟨-, ⟨t3, hb3⟩ |
    ⟨-, hp, t4, hc, hci, hb4⟩⟩⟩
  · exact Or.inl ⟨t1, h0, h64, h5, hB, hv, hW⟩
  · exact Or.inr (Or.inl ⟨t2, hb2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨t3, hb3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨t4, hp, hc, hci, hb4⟩))

theorem checkF_sound {B : SBase} {g : Nat} {ginv : List Nat} {wg : List (List Nat)}
    {cpar : List (Nat × Nat)} {T : List (Nat × Nat)} {orb : List (Nat × Nat × Nat)}
    {reps : List Nat} {ranks : List (List Nat)}
    {recs : List (List (List Nat × List (List Nat)))}
    {cls : List Nat × List (List Nat) × List (List Nat)}
    (h : checkF B g ginv wg cpar T orb reps ranks recs cls = true) :
    CheckFFacts B g ginv wg cpar T reps recs cls := by
  unfold checkF at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hg, hinv, hcov, hreps, horb, hrecs, hcls⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [blt_eqS, decide_eq_true_eq] at hg
    exact hg
  · rw [zipS_eq_true] at hinv
    simp only [beq_eqS, decide_eq_true_eq] at hinv
    rw [nthS_eq] at hinv
    exact hinv
  · rw [nthS_eq] at hcov
    exact coverS_sound hcov
  · rw [allS_eq_true] at hreps
    simp only [memS_eq_true] at hreps
    exact hreps
  · rw [nthS_eq] at horb
    exact orbS_sound B.sing reps _ orb horb
  · rw [zipS_eq_true] at hrecs
    refine hrecs.imp fun p rs hp => ?_
    simp only [nthS_eq] at hp
    exact recsT_sound B rfl rfl rfl rfl rfl rfl hp
  · rw [nthS_eq] at hcls
    exact clsS_sound hcls

theorem checkAt_sound {B : SBase} {lo : Nat} {ginv : List (List Nat)}
    {wg : List (List (List Nat))} {cpar : List (List (Nat × Nat))} {T : List (List (Nat × Nat))}
    {orb : List (List (Nat × Nat × Nat))} {reps : List (List Nat)}
    {ranks : List (List (List Nat))} {recs : List (List (List (List Nat × List (List Nat))))}
    {cls : List (List Nat × List (List Nat) × List (List Nat))} {i : Nat}
    (h : checkAt B lo ginv wg cpar T orb reps ranks recs cls i = true) :
    CheckFFacts B (lo + i) (ginv.getD i []) (wg.getD i []) (cpar.getD i []) (T.getD i [])
      (reps.getD i []) (recs.getD i []) (cls.getD i ([], [], [])) := by
  unfold checkAt at h
  simp only [nthS_eq] at h
  exact checkF_sound h

end CFSG.KC.C690S

end
