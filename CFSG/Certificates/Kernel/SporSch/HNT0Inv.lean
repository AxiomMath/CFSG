module

public import CFSG.Certificates.Kernel.SporSch.HNT0Enum
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2DfsSound
public import Certificates.Data.Kernel.SporSch.HNT0P
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.HNT0

open CFSG.KC.Enum CFSG.KS CFSG.KS.EnumBase CFSG.KS.PEnum CFSG.KS.BaseEq CFSG.KC.LL
  CFSG.KC.LL.HNX CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5

@[expose] def adjT (AL : ℕ → ℕ) (m i j : ℕ) : Bool :=
  decide (i < m) && decide (j < m) && Nat.beq fld(AL i, j, 1) 1

@[expose] def prT (PR : ℕ → ℕ) (i j : ℕ) : ℕ := fld(PR i, Nat.mul 10 j, 1023)

theorem fldW_eq' (r o w : Nat) : fldW r o w = r / 2 ^ o % 2 ^ w := by
  unfold fldW
  change (r >>> o) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem bit_eq (x k : ℕ) : fld(x, k, 1) = if x.testBit k then 1 else 0 := by
  change (x >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [h]

theorem bit_le (x k : ℕ) : fld(x, k, 1) = 0 ∨ fld(x, k, 1) = 1 := by
  rw [bit_eq]
  split <;> simp

theorem pg8_lt (p j : ℕ) : pg 8 255 p j < 2 ^ 8 := by
  have h := CFSG.KS.PF.pg_lt 8 p j
  rwa [mask8] at h

theorem pg8_of_fld {X i : ℕ} {g : ℕ → ℕ} (hX : CFSG.KS.PF.Fld 8 X g) (hg : g i < 2 ^ 8) :
    pg 8 255 X i = g i := by
  have h := CFSG.KS.PF.pg_of_fld hX hg
  rwa [mask8] at h

theorem fld_keyL (t : ℕ) : ∀ ps : List ℕ,
    CFSG.KS.PF.Fld 8 (keyL 8 255 ps t) (fun i => (ps.map (pg 8 255 t)).getD i 0)
  | [] => CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_zero 8) fun i => by simp
  | p :: ps => by
    have h := CFSG.KS.PF.fld_or (CFSG.KS.PF.fld_one (w := 8) (pg8_lt t p))
      (CFSG.KS.PF.fld_shl 1 (fld_keyL t ps))
    rw [Nat.mul_one] at h
    change CFSG.KS.PF.Fld 8 (Nat.lor (pg 8 255 t p) (Nat.shiftLeft (keyL 8 255 ps t) 8)) _
    refine CFSG.KS.PF.fld_congr h fun i => ?_
    rcases i with _ | i <;> simp

theorem pg_keyL {t : ℕ} {ps : List ℕ} {i : ℕ} (hi : i < ps.length) :
    pg 8 255 (keyL 8 255 ps t) i = pg 8 255 t ps[i] := by
  have e : (ps.map (pg 8 255 t)).getD i 0 = pg 8 255 t ps[i] := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [pg8_of_fld (fld_keyL t ps) (by rw [e]; exact pg8_lt _ _), e]

theorem fld_appK (t k : ℕ) : ∀ np : ℕ, CFSG.KS.PF.Fld 8 (appK 8 255 np t k)
    (fun i => if i < np then pg 8 255 t (pg 8 255 k i) else 0)
  | 0 => CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_zero 8) fun i => by simp
  | np + 1 => by
    have h := CFSG.KS.PF.fld_or (fld_appK t k np)
      (CFSG.KS.PF.fld_shl np (CFSG.KS.PF.fld_one (w := 8) (pg8_lt t (pg 8 255 k np))))
    change CFSG.KS.PF.Fld 8 (Nat.lor (appK 8 255 np t k)
      (Nat.shiftLeft (pg 8 255 t (pg 8 255 k np)) (Nat.mul 8 np))) _
    refine CFSG.KS.PF.fld_congr h fun i => ?_
    rcases lt_trichotomy i np with h1 | rfl | h1
    · have h2 : ¬ np ≤ i := by omega
      simp [h1, h2, show i < np + 1 by omega]
    · simp
    · simp [show ¬ i < np by omega, show ¬ i < np + 1 by omega, show i - np ≠ 0 by omega,
        h1.le]

theorem appK_eq_iff {t k t' k' np : ℕ} : appK 8 255 np t k = appK 8 255 np t' k' ↔
    ∀ i < np, pg 8 255 t (pg 8 255 k i) = pg 8 255 t' (pg 8 255 k' i) := by
  constructor
  · intro e i hi
    have h1 := pg8_of_fld (i := i) (fld_appK t k np) (by simp only [hi, ↓reduceIte]; exact pg8_lt _ _)
    have h2 := pg8_of_fld (i := i) (fld_appK t' k' np)
      (by simp only [hi, ↓reduceIte]; exact pg8_lt _ _)
    simp only [hi, ↓reduceIte] at h1 h2
    rw [← h1, ← h2, e]
  · intro h
    refine CFSG.KS.PF.eq_of_fld (by norm_num) (fld_appK t k np) ?_
    refine CFSG.KS.PF.fld_congr (fld_appK t' k' np) fun i => ?_
    by_cases hi : i < np
    · simp only [hi, ↓reduceIte]
      exact (h i hi).symm
    · simp only [hi, ↓reduceIte]

theorem keyL_eq_appK_iff {ps : List ℕ} {t a k : ℕ} :
    keyL 8 255 ps t = appK 8 255 ps.length a k ↔
      ∀ i (hi : i < ps.length), pg 8 255 t ps[i] = pg 8 255 a (pg 8 255 k i) := by
  constructor
  · intro e i hi
    have h2 := pg8_of_fld (i := i) (fld_appK a k ps.length)
      (by simp only [hi, ↓reduceIte]; exact pg8_lt _ _)
    simp only [hi, ↓reduceIte] at h2
    rw [← pg_keyL hi, e, h2]
  · intro h
    refine CFSG.KS.PF.eq_of_fld (by norm_num) (fld_keyL t ps) ?_
    refine CFSG.KS.PF.fld_congr (fld_appK a k ps.length) fun i => ?_
    by_cases hi : i < ps.length
    · simp [hi, List.getD_eq_getElem?_getD, h i hi]
    · simp [hi, List.getD_eq_getElem?_getD]

theorem lenK_eq {α : Type} : ∀ l : List α, lenK l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenK l) = _
    rw [lenK_eq l, List.length_cons]

theorem maskL_testBit : ∀ (l : List ℕ) (x : ℕ), (maskL l).testBit x = decide (x ∈ l)
  | [], x => by simp [maskL]
  | y :: l, x => by
    change ((1 <<< y) ||| maskL l).testBit x = _
    rw [Nat.testBit_or, maskL_testBit l x, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.testBit_two_pow]
    by_cases h : y = x
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem allL_iff {ps : List ℕ} {f : ℕ → Bool} : allL ps f = true ↔ ∀ p ∈ ps, f p = true := by
  induction ps with
  | nil => simp [allL]
  | cons q ps ih =>
    change bAnd(f q, allL ps f) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem invK_iff {ps : List ℕ} {t : ℕ} : invK 8 255 ps t = true ↔
    (∀ p ∈ ps, pg 8 255 t (pg 8 255 t p) = p) ∧ ∃ p ∈ ps, pg 8 255 t p ≠ p := by
  unfold invK
  rw [bAnd_eq, Bool.and_eq_true, sqFixK_iff, bIf_eq]
  refine and_congr Iff.rfl ?_
  by_cases h : allL ps (fun p => Nat.beq (pg 8 255 t p) p) = true
  · rw [if_pos h]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and, not_not]
    exact fun p hp => Nat.eq_of_beq_eq_true (allL_spec h p hp)
  · rw [if_neg h]
    simp only [true_iff]
    rw [allL_iff] at h
    push Not at h
    obtain ⟨p, hp, e⟩ := h
    exact ⟨p, hp, fun h' => e (by rw [h']; exact Nat.beq_refl p)⟩

theorem censK_spec {ps : List ℕ} {T : ℕ → ℕ} {IM k : ℕ} (h : censK 8 255 ps T IM k = true) :
    IM.testBit k = true ↔ invK 8 255 ps (T k) = true := by
  unfold censK at h
  rw [strictB_eq, strictB_eq, bIf_eq, bit_eq] at h
  by_cases hb : IM.testBit k = true <;> by_cases hi : invK 8 255 ps (T k) = true <;>
    simp [hb, hi, Nat.beq_eq] at h ⊢

theorem invLK_spec {ps : List ℕ} {N kw : ℕ} {T IL : ℕ → ℕ} {KB : ℕ} :
    ∀ (l : List ℕ) (a lo : ℕ), invLK 8 255 ps N kw T IL KB l a lo = true →
      l.Pairwise (· < ·) ∧ (∀ x ∈ l, lo ≤ x ∧ x < N) ∧ ∀ i (hi : i < l.length),
        IL (a + i) = T l[i] ∧ fldW KB (Nat.mul kw (a + i)) kw = keyL 8 255 ps (T l[i])
  | [], _, _, _ => ⟨List.Pairwise.nil, by simp, fun i hi => absurd hi (by simp)⟩
  | x :: l, a, lo, h => by
    change bAnd(Nat.ble lo x, bAnd(Nat.blt x N, strictB (T x) fun t =>
      bAnd(Nat.beq (IL a) t, bAnd(Nat.beq (fldW KB (Nat.mul kw a) kw) (keyL 8 255 ps t),
        invLK 8 255 ps N kw T IL KB l (Nat.succ a) (Nat.succ x))))) = true at h
    simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, ble_eq, blt_eq, decide_eq_true_eq] at h
    obtain ⟨hlo, hN, hIL, hKB, hrest⟩ := h
    obtain ⟨hp, hb, hf⟩ := invLK_spec l (a + 1) (x + 1) hrest
    refine ⟨List.Pairwise.cons (fun y hy => (hb y hy).1) hp, ?_, fun i hi => ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨hlo, hN⟩
      · exact ⟨by have := (hb y hy).1; omega, (hb y hy).2⟩
    · rcases i with _ | i
      · exact ⟨Nat.eq_of_beq_eq_true hIL, Nat.eq_of_beq_eq_true hKB⟩
      · have e := hf i (by simpa using hi)
        rw [show a + 1 + i = a + (i + 1) by omega] at e
        exact e

theorem pairK_spec {na np kw : ℕ} {IL : ℕ → ℕ} {KB a ta ka row pr b : ℕ}
    (h : pairK na 8 255 np kw IL KB a ta ka row pr b = true) :
    (b ≠ a ∧ appK 8 255 np ta (fldW KB (Nat.mul kw b) kw) = appK 8 255 np (IL b) ka →
      fld(row, b, 1) = 1 ∧ fld(pr, Nat.mul 10 b, 1023) < na ∧
      fldW KB (Nat.mul kw fld(pr, Nat.mul 10 b, 1023)) kw =
        appK 8 255 np ta (fldW KB (Nat.mul kw b) kw) ∧
      (fld(row, Nat.add 1024 b, 1) = 1 ↔ b < fld(pr, Nat.mul 10 b, 1023))) ∧
    (¬ (b ≠ a ∧ appK 8 255 np ta (fldW KB (Nat.mul kw b) kw) = appK 8 255 np (IL b) ka) →
      fld(row, b, 1) = 0 ∧ fld(row, Nat.add 1024 b, 1) = 0 ∧ fld(pr, Nat.mul 10 b, 1023) = 0) := by
  unfold pairK at h
  simp only [strictB_eq] at h
  have key : (b ≠ a ∧ appK 8 255 np ta (fldW KB (Nat.mul kw b) kw) = appK 8 255 np (IL b) ka) ↔
      (Nat.beq b a = false ∧ Nat.beq (appK 8 255 np ta (fldW KB (Nat.mul kw b) kw))
        (appK 8 255 np (IL b) ka) = true) := by
    rw [beq_eq, beq_eq]
    simp
  rw [key]
  cases e1 : Nat.beq b a <;>
    cases e2 : Nat.beq (appK 8 255 np ta (fldW KB (Nat.mul kw b) kw)) (appK 8 255 np (IL b) ka) <;>
    rw [e1, e2] at h <;> dsimp only at h <;>
    simp only [bAnd_eq, Bool.and_eq_true, beq_eq, blt_eq, decide_eq_true_eq] at h <;>
    simp only [Bool.false_eq_true, and_false, false_and, and_true, false_implies, not_false_eq_true,
      true_implies, not_true_eq_false, and_self] <;> first
    | exact h
    | (obtain ⟨h1, h2, h3, h4⟩ := h
       refine ⟨h1, h2, h3, ?_⟩
       rw [h4]
       by_cases e3 : b < fld(pr, Nat.mul 10 b, 1023)
       · rw [decide_eq_true e3]
         exact ⟨fun _ => e3, fun _ => rfl⟩
       · rw [decide_eq_false e3]
         exact ⟨fun h => absurd h (by decide), fun h => absurd h e3⟩)
    | simp_all

theorem adjK_spec {na : ℕ} {ps : List ℕ} {IL AL PR : ℕ → ℕ} {KB a : ℕ}
    (h : adjK na 8 255 ps 24 IL AL PR KB a = true) :
    AL a < 2 ^ (1024 + na) ∧ ∀ b < na, pairK na 8 255 ps.length 24 IL KB a (IL a)
      (keyL 8 255 ps (IL a)) (AL a) (PR a) b = true := by
  unfold adjK at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, blt_eq, decide_eq_true_eq] at h
  obtain ⟨h1, -, -, h4⟩ := h
  have e : Nat.shiftLeft 1 (Nat.add 1024 na) = 2 ^ (1024 + na) := by
    change 1 <<< (1024 + na) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  refine ⟨by rw [e] at h1; exact h1, fun b hb => ?_⟩
  rw [← lenK_eq]
  exact allN_spec h4 b hb

section Graph

variable {Γ : Type*} [Group Γ] {V : Type*} [MulAction Γ V]
variable {pt : ℕ → V} {n N m ng : ℕ} {gens : ℕ → Γ} {ι : ℕ → Γ} {BP INV : List ℕ}
  {T IL AL PR : ℕ → ℕ} {KB : ℕ}

structure EnumFacts (pt : ℕ → V) (n N ng : ℕ) (gens : ℕ → Γ) (ι : ℕ → Γ) (BP : List ℕ)
    (T : ℕ → ℕ) : Prop where
  rep : ∀ k < N, Rep pt n (ι k) (T k)
  mem : ∀ k < N, ι k ∈ genSub gens ng
  surj : ∀ x ∈ genSub gens ng, ∃ k < N, ι k = x
  base : ∀ x ∈ genSub gens ng, ∀ y ∈ genSub gens ng, (∀ p ∈ BP, x • pt p = y • pt p) → x = y
  ptinj : ∀ i < n, ∀ j < n, pt i = pt j → i = j
  bp : ∀ p ∈ BP, p < n

variable (hE : EnumFacts pt n N ng gens ι BP T)
include hE

theorem EnumFacts.sq_iff {k : ℕ} (hk : k < N) :
    ι k * ι k = 1 ↔ ∀ p ∈ BP, pg 8 255 (T k) (pg 8 255 (T k) p) = p := by
  have hr := hE.rep k hk
  constructor
  · intro e p hp
    have h1 := (hr p (hE.bp p hp))
    have h2 := hr _ h1.1
    refine hE.ptinj _ h2.1 _ (hE.bp p hp) ?_
    rw [← h2.2, ← h1.2, ← mul_smul, e, one_smul]
  · intro h
    refine hE.base _ (mul_mem (hE.mem k hk) (hE.mem k hk)) _ (one_mem _) fun p hp => ?_
    have h1 := hr p (hE.bp p hp)
    rw [mul_smul, h1.2, (hr _ h1.1).2, h p hp, one_smul]

theorem EnumFacts.ne_one_iff {k : ℕ} (hk : k < N) :
    ι k ≠ 1 ↔ ∃ p ∈ BP, pg 8 255 (T k) p ≠ p := by
  have hr := hE.rep k hk
  constructor
  · intro hne
    by_contra hc
    push Not at hc
    refine hne (hE.base _ (hE.mem k hk) _ (one_mem _) fun p hp => ?_)
    rw [(hr p (hE.bp p hp)).2, hc p hp, one_smul]
  · rintro ⟨p, hp, hne⟩ e
    have h1 := hr p (hE.bp p hp)
    rw [e, one_smul] at h1
    exact hne (hE.ptinj _ h1.1 _ (hE.bp p hp) h1.2.symm)

theorem EnumFacts.inv_iff (hcens : ∀ k < N, censK 8 255 BP T (maskL INV) k = true) {k : ℕ}
    (hk : k < N) : (ι k * ι k = 1 ∧ ι k ≠ 1) ↔ k ∈ INV := by
  rw [hE.sq_iff hk, hE.ne_one_iff hk, ← invK_iff, ← censK_spec (hcens k hk), maskL_testBit,
    decide_eq_true_iff]

theorem EnumFacts.smul_mul {k l : ℕ} (hk : k < N) (hl : l < N) {i : ℕ} (hi : i < BP.length) :
    (ι k * ι l) • pt BP[i] = pt (pg 8 255 (T k) (pg 8 255 (keyL 8 255 BP (T l)) i)) := by
  rw [pg_keyL hi, mul_smul, (hE.rep l hl _ (hE.bp _ (List.getElem_mem hi))).2,
    (hE.rep k hk _ (hE.rep l hl _ (hE.bp _ (List.getElem_mem hi))).1).2]

theorem EnumFacts.mul_eq_iff {k l k' l' : ℕ} (hk : k < N) (hl : l < N) (hk' : k' < N)
    (hl' : l' < N) : ι k * ι l = ι k' * ι l' ↔
      appK 8 255 BP.length (T k) (keyL 8 255 BP (T l)) =
        appK 8 255 BP.length (T k') (keyL 8 255 BP (T l')) := by
  rw [appK_eq_iff]
  constructor
  · intro e i hi
    have h : (ι k * ι l) • pt BP[i] = (ι k' * ι l') • pt BP[i] := by rw [e]
    rw [hE.smul_mul hk hl hi, hE.smul_mul hk' hl' hi] at h
    refine hE.ptinj _ ?_ _ ?_ h
    · rw [pg_keyL hi]
      exact (hE.rep k hk _ (hE.rep l hl _ (hE.bp _ (List.getElem_mem hi))).1).1
    · rw [pg_keyL hi]
      exact (hE.rep k' hk' _ (hE.rep l' hl' _ (hE.bp _ (List.getElem_mem hi))).1).1
  · intro h
    refine hE.base _ (mul_mem (hE.mem k hk) (hE.mem l hl)) _
      (mul_mem (hE.mem k' hk') (hE.mem l' hl')) fun p hp => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    rw [hE.smul_mul hk hl hi, hE.smul_mul hk' hl' hi, h i hi]

theorem EnumFacts.eq_mul_iff {p k l : ℕ} (hp : p < N) (hk : k < N) (hl : l < N) :
    ι p = ι k * ι l ↔ keyL 8 255 BP (T p) = appK 8 255 BP.length (T k) (keyL 8 255 BP (T l)) := by
  rw [keyL_eq_appK_iff]
  constructor
  · intro e i hi
    have h1 := hE.rep p hp _ (hE.bp _ (List.getElem_mem hi))
    have h : ι p • pt BP[i] = (ι k * ι l) • pt BP[i] := by rw [e]
    rw [hE.smul_mul hk hl hi, h1.2] at h
    refine hE.ptinj _ h1.1 _ ?_ h
    rw [pg_keyL hi]
    exact (hE.rep k hk _ (hE.rep l hl _ (hE.bp _ (List.getElem_mem hi))).1).1
  · intro h
    refine hE.base _ (hE.mem p hp) _ (mul_mem (hE.mem k hk) (hE.mem l hl)) fun q hq => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
    rw [hE.smul_mul hk hl hi, (hE.rep p hp _ (hE.bp _ (List.getElem_mem hi))).2, h i hi]

theorem EnumFacts.setting (hinj : ∀ k < N, ∀ l < N, ι k = ι l → k = l)
    (hcens : ∀ k < N, censK 8 255 BP T (maskL INV) k = true)
    (hinvL : invLK 8 255 BP N 24 T IL KB INV 0 0 = true) (hm : INV.length = m)
    (hadj : ∀ a < m, adjK m 8 255 BP 24 IL AL PR KB a = true) :
    Setting m (fun a => ι (INV.getD a 0)) (adjT AL m) (prT PR) ∧
    ∀ a < m, ∀ b < m,
      fld(AL a, Nat.add 1024 b, 1) = if adjT AL m a b = true ∧ b < prT PR a b then 1 else 0 := by
  obtain ⟨hpw, hb, hf⟩ := invLK_spec INV 0 0 hinvL
  have hx : ∀ a < m, INV.getD a 0 < N ∧ IL a = T (INV.getD a 0) ∧
      fldW KB (Nat.mul 24 a) 24 = keyL 8 255 BP (T (INV.getD a 0)) := by
    intro a ha
    have ha' : a < INV.length := by omega
    have e : INV.getD a 0 = INV[a] := by simp [List.getD_eq_getElem?_getD, ha']
    obtain ⟨h1, h2⟩ := hf a ha'
    rw [Nat.zero_add] at h1 h2
    exact ⟨e ▸ (hb _ (List.getElem_mem ha')).2, e ▸ h1, e ▸ h2⟩
  have hsq : ∀ a < m, ι (INV.getD a 0) * ι (INV.getD a 0) = 1 ∧ ι (INV.getD a 0) ≠ 1 := by
    intro a ha
    have ha' : a < INV.length := by omega
    have e : INV.getD a 0 = INV[a] := by simp [List.getD_eq_getElem?_getD, ha']
    rw [hE.inv_iff hcens (hx a ha).1, e]
    exact List.getElem_mem ha'
  have hpair : ∀ a < m, ∀ b < m,
      ((b ≠ a ∧ ι (INV.getD a 0) * ι (INV.getD b 0) = ι (INV.getD b 0) * ι (INV.getD a 0)) →
        fld(AL a, b, 1) = 1 ∧ prT PR a b < m ∧
        ι (INV.getD (prT PR a b) 0) = ι (INV.getD a 0) * ι (INV.getD b 0) ∧
        (fld(AL a, Nat.add 1024 b, 1) = 1 ↔ b < prT PR a b)) ∧
      (¬ (b ≠ a ∧ ι (INV.getD a 0) * ι (INV.getD b 0) = ι (INV.getD b 0) * ι (INV.getD a 0)) →
        fld(AL a, b, 1) = 0 ∧ fld(AL a, Nat.add 1024 b, 1) = 0) := by
    intro a ha b hb'
    have hs := pairK_spec ((adjK_spec (hadj a ha)).2 b hb')
    obtain ⟨xa, ia, ka⟩ := hx a ha
    obtain ⟨xb, ib, kb⟩ := hx b hb'
    rw [ia, kb, ib, ← hE.mul_eq_iff xa xb xb xa] at hs
    refine ⟨fun hc => ?_, fun hc => ⟨(hs.2 hc).1, (hs.2 hc).2.1⟩⟩
    obtain ⟨h1, h2, h3, h4⟩ := hs.1 hc
    obtain ⟨xp, -, kp⟩ := hx _ h2
    rw [kp, ← hE.eq_mul_iff xp xa xb] at h3
    exact ⟨h1, h2, h3, h4⟩
  have hadj_iff : ∀ i j, adjT AL m i j = true ↔ i < m ∧ j < m ∧
      ι (INV.getD i 0) * ι (INV.getD j 0) = ι (INV.getD j 0) * ι (INV.getD i 0) ∧
      ∃ k < m, ι (INV.getD k 0) = ι (INV.getD i 0) * ι (INV.getD j 0) := by
    intro i j
    unfold adjT
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_eq]
    constructor
    · rintro ⟨⟨hi, hj⟩, hbit⟩
      by_cases hc : j ≠ i ∧ ι (INV.getD i 0) * ι (INV.getD j 0) =
          ι (INV.getD j 0) * ι (INV.getD i 0)
      · obtain ⟨-, h2, h3, -⟩ := (hpair i hi j hj).1 hc
        exact ⟨hi, hj, hc.2, _, h2, h3⟩
      · rw [((hpair i hi j hj).2 hc).1] at hbit
        exact absurd hbit (by decide)
    · rintro ⟨hi, hj, hc, k, hk, hkv⟩
      have hji : j ≠ i := by
        rintro rfl
        exact (hsq k hk).2 (by rw [hkv, (hsq j hj).1])
      exact ⟨⟨hi, hj⟩, ((hpair i hi j hj).1 ⟨hji, hc⟩).1⟩
  refine ⟨⟨fun i j hi hj e => ?_, hsq, hadj_iff, fun i j h => ?_⟩, fun a ha b hb' => ?_⟩
  · have hi' : i < INV.length := by omega
    have hj' : j < INV.length := by omega
    have e1 : INV.getD i 0 = INV[i] := by simp [List.getD_eq_getElem?_getD, hi']
    have e2 : INV.getD j 0 = INV[j] := by simp [List.getD_eq_getElem?_getD, hj']
    have hij := hinj _ (hx i hi).1 _ (hx j hj).1 e
    rw [e1, e2] at hij
    exact (List.Nodup.getElem_inj_iff hpw.nodup).1 hij
  · obtain ⟨hi, hj, hc, -⟩ := (hadj_iff i j).1 h
    have hji : j ≠ i := by
      intro e
      rw [e] at h
      obtain ⟨-, -, -, k, hk, hkv⟩ := (hadj_iff i i).1 h
      exact (hsq k hk).2 (by rw [hkv, (hsq i hi).1])
    obtain ⟨-, h2, h3, -⟩ := (hpair i hi j hj).1 ⟨hji, hc⟩
    exact ⟨h2, h3⟩
  · by_cases hc : b ≠ a ∧ ι (INV.getD a 0) * ι (INV.getD b 0) =
        ι (INV.getD b 0) * ι (INV.getD a 0)
    · obtain ⟨h1, h2, h3, h4⟩ := (hpair a ha b hb').1 hc
      have hadjab : adjT AL m a b = true := by
        unfold adjT
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_eq]
        exact ⟨⟨ha, hb'⟩, h1⟩
      rcases bit_le (AL a) (Nat.add 1024 b) with e | e
      · rw [e]
        have : ¬ b < prT PR a b := fun hlt => absurd (h4.2 hlt) (by rw [e]; decide)
        simp [this]
      · rw [e]
        simp [hadjab, h4.1 e]
    · obtain ⟨h1, h2⟩ := (hpair a ha b hb').2 hc
      have hn : adjT AL m a b = false := by
        unfold adjT
        rw [show Nat.beq fld(AL a, b, 1) 1 = false by rw [h1]; rfl]
        simp
      rw [h2]
      simp [hn]

end Graph

end CFSG.KS.HNT0

end
