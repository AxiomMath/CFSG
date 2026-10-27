module

public import CFSG.Certificates.Kernel.D4QK.TwinSound
public import CFSG.Certificates.Kernel.S63K.ConjTreeSound

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.D4QK

open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.LargeExtraspecial.S63
open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
open CFSG.Quasithin.Background.Harris.R1.D4Vert (bfsPl)
open CFSG.KS.SporSch.M24 (gtPinK gtStepK bfsK bfsRowK bfsRunK)
open CFSG.KC.Co1B (mulWK)

abbrev IStateP := Std.HashMap (Array ℕ) Unit × Array (Array ℕ) × Array (ℕ × ℕ)

@[expose] def innerP (gs : Array (Array ℕ)) (y : Array ℕ) (i k : ℕ) (s : IStateP) :
    Id (ForInStep IStateP) :=
  if (!s.1.contains (mulR y gs[k]!)) = true then
    pure (ForInStep.yield (s.1.insert (mulR y gs[k]!) (), s.2.1.push (mulR y gs[k]!),
      s.2.2.push (i, k)))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2))

abbrev OStateP := Std.HashMap (Array ℕ) Unit × Array (Array ℕ) × Array (ℕ × ℕ) × ℕ

@[expose] def outerP (gs : Array (Array ℕ)) (_ : Unit) (s : OStateP) : Id (ForInStep OStateP) :=
  if s.2.2.2 < s.2.1.size then
    pure (ForInStep.yield ((fun t : IStateP => (t.1, t.2.1, t.2.2, s.2.2.2 + 1))
      (Id.run (forIn [:gs.size] (s.1, s.2.1, s.2.2.1) (innerP gs s.2.1[s.2.2.2]! s.2.2.2)))))
  else pure (ForInStep.done s)

@[expose] def runP (gs : Array (Array ℕ)) (s : OStateP) : OStateP :=
  Id.run (forIn Lean.Loop.mk s (outerP gs))

@[expose] def stepP (gs : Array (Array ℕ)) (y : Array ℕ) (i : ℕ) (s : IStateP) (k : ℕ) : IStateP :=
  if (!s.1.contains (mulR y gs[k]!)) = true then
    (s.1.insert (mulR y gs[k]!) (), s.2.1.push (mulR y gs[k]!), s.2.2.push (i, k))
  else s

theorem innerP_eq (gs : Array (Array ℕ)) (y : Array ℕ) (i : ℕ) (s : IStateP) :
    Id.run (forIn [:gs.size] s (innerP gs y i)) = (List.range' 0 gs.size).foldl (stepP gs y i) s := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply forIn_yield
  intro k t
  unfold innerP stepP
  split <;> rfl

@[expose] def withHP (t : IStateP) (h : ℕ) : OStateP := (t.1, t.2.1, t.2.2, h)

@[expose] def toIP (r : OStateP) : IStateP := (r.1, r.2.1, r.2.2.1)

theorem runP_unfold (gs : Array (Array ℕ)) (s : IStateP) (h : ℕ) :
    runP gs (withHP s h) = if h < s.2.1.size then
      runP gs (withHP ((List.range' 0 gs.size).foldl (stepP gs s.2.1[h]! h) s) (h + 1))
      else withHP s h := by
  unfold runP
  simp only [Id.run]
  rw [loop_unfold]
  unfold outerP withHP
  dsimp only
  by_cases hc : h < s.2.1.size
  · rw [if_pos hc, if_pos hc]
    dsimp only [pure]
    rw [innerP_eq]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem bfsPl_eq_run (gs : Array (Array ℕ)) :
    bfsPl gs = (fun r : OStateP => r.2.2.1.toList)
      (runP gs (withHP (((∅ : Std.HashMap (Array ℕ) Unit).insert oneR ()), #[oneR], #[]) 0)) :=
  rfl

variable {GM P PAR LAB W : ℕ → ℕ} {ng N : ℕ}

structure PMatch (P PAR LAB : ℕ → ℕ) (N c : ℕ) (s : IStateP) : Prop where
  size : s.2.1.size = c
  pts : ∀ i < c, s.2.1[i]! = unpackR 24 (P i)
  psize : s.2.2.size + 1 = c
  pairs : ∀ i, i + 1 < c → s.2.2[i]! = (PAR (1 + i), LAB (1 + i))
  seen : SeenOK P N s.1 c

@[expose] def PTree (GM P PAR LAB : ℕ → ℕ) (ng c : ℕ) : Prop :=
  ∀ i, 0 < i → i < c → PAR i < i ∧ LAB i < ng ∧ P i = gtStepK GM (P (PAR i)) (LAB i)

theorem matchP_push {c : ℕ} {s : IStateP} (hP : ∀ i < N, P i < 2 ^ 576)
    (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) (hs : PMatch P PAR LAB N c s) (hc : c < N) :
    PMatch P PAR LAB N (c + 1)
      (s.1.insert (unpackR 24 (P c)) (), s.2.1.push (unpackR 24 (P c)), s.2.2.push (PAR c, LAB c)) := by
  obtain ⟨hsz, hpts, hpsz, hpairs, hseen⟩ := hs
  refine ⟨by simp [hsz], fun i hi => ?_, by simp; omega, fun i hi => ?_, seen_ins hP hinj hseen hc⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [push_lt _ _ (by omega)]
      exact hpts i hi
    · rw [← hsz, push_size, hsz]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · rw [push_lt _ _ (by omega)]
      exact hpairs i hi
    · have e : i = s.2.2.size := by omega
      subst e
      rw [push_size, show 1 + s.2.2.size = c by omega]

theorem rowP_succ (F : ℕ → ℕ → ℕ) (h k l c : ℕ) :
    bfsRowK F P PAR LAB W ng h (k + 1) l c =
      if W (h * ng + l) < c then
        (if P (W (h * ng + l)) = F (P h) l then bfsRowK F P PAR LAB W ng h k (l + 1) c
          else 0)
      else if W (h * ng + l) = c ∧ P c = F (P h) l ∧ PAR c = h ∧ LAB c = l then
        bfsRowK F P PAR LAB W ng h k (l + 1) (c + 1)
      else 0 := by
  change strictN (W (Nat.add (Nat.mul h ng) l)) (fun w =>
      strictN (F (P h) l) fun y =>
      nIf(Nat.blt w c, nIf(Nat.beq (P w) y, bfsRowK F P PAR LAB W ng h k (Nat.succ l) c,
        nat_lit 0),
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (P c) y, bAnd(Nat.beq (PAR c) h, Nat.beq (LAB c) l))),
          bfsRowK F P PAR LAB W ng h k (Nat.succ l) (Nat.succ c), nat_lit 0))) = _
  simp only [CFSG.KS.SporSch.M24.MatL.strictN_eq, CFSG.KS.SporSch.M24.MatL.nIf_eq,
    CFSG.KS.SporSch.M24.MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]
  rfl

theorem rowP_mono (F : ℕ → ℕ → ℕ) (h : ℕ) :
    ∀ k l c, bfsRowK F P PAR LAB W ng h k l c ≠ 0 → c ≤ bfsRowK F P PAR LAB W ng h k l c := by
  intro k
  induction k with
  | zero => intro l c _; exact Nat.le_refl c
  | succ k ih =>
    intro l c hne
    rw [rowP_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact ih _ _ hne
      · exact absurd rfl hne
    · rw [if_neg ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact Nat.le_of_succ_le (ih _ _ hne)
      · exact absurd rfl hne

theorem runP_succ (F : ℕ → ℕ → ℕ) (cap fuel h c : ℕ) :
    bfsRunK F P PAR LAB W ng cap (fuel + 1) h c =
      if h < c ∧ c < cap then
        (if bfsRowK F P PAR LAB W ng h ng 0 c = 0 then 0
         else bfsRunK F P PAR LAB W ng cap fuel (h + 1) (bfsRowK F P PAR LAB W ng h ng 0 c))
      else c := by
  change nIf(bAnd(Nat.blt h c, Nat.blt c cap),
      strictN (bfsRowK F P PAR LAB W ng h ng (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0,
          bfsRunK F P PAR LAB W ng cap fuel (Nat.succ h) c'), c) = _
  simp only [CFSG.KS.SporSch.M24.MatL.strictN_eq, CFSG.KS.SporSch.M24.MatL.nIf_eq,
    CFSG.KS.SporSch.M24.MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]

theorem runP_mono (F : ℕ → ℕ → ℕ) (cap : ℕ) :
    ∀ fuel h c, bfsRunK F P PAR LAB W ng cap fuel h c ≠ 0 →
      c ≤ bfsRunK F P PAR LAB W ng cap fuel h c := by
  intro fuel
  induction fuel with
  | zero => intro h c hne; exact absurd rfl hne
  | succ fuel ih =>
    intro h c hne
    rw [runP_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · exact absurd rfl hne
      · rw [if_neg ‹_›]
        exact Nat.le_trans (rowP_mono F h ng 0 c ‹_›) (ih _ _ hne)
    · rw [if_neg ‹_›]

theorem stepP_eq {gs : Array (Array ℕ)} (hg : ∀ l < ng, gs[l]! = unpackR 24 (GM l)) (x : ℕ)
    {l : ℕ} (hl : l < ng) : mulR (unpackR 24 x) gs[l]! = unpackR 24 (gtStepK GM x l) := by
  rw [hg l hl, mulR_unpackR]
  rfl

theorem rowP_replay {gs : Array (Array ℕ)} (hg : ∀ l < ng, gs[l]! = unpackR 24 (GM l))
    (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) {h : ℕ} :
    ∀ k l c (s : IStateP), l + k ≤ ng → h < c →
      PMatch P PAR LAB N c s → PTree GM P PAR LAB ng c →
      bfsRowK (gtStepK GM) P PAR LAB W ng h k l c ≠ 0 →
      bfsRowK (gtStepK GM) P PAR LAB W ng h k l c ≤ N →
      PMatch P PAR LAB N (bfsRowK (gtStepK GM) P PAR LAB W ng h k l c)
          ((List.range' l k).foldl (stepP gs (unpackR 24 (P h)) h) s) ∧
        PTree GM P PAR LAB ng (bfsRowK (gtStepK GM) P PAR LAB W ng h k l c) := by
  intro k
  induction k with
  | zero =>
    intro l c s _ _ hs ht _ _
    exact ⟨hs, ht⟩
  | succ k ih =>
    intro l c s hlk hhc hs ht hne hle
    have hmono := rowP_mono (P := P) (PAR := PAR) (LAB := LAB) (W := W) (ng := ng)
      (gtStepK GM) h (k + 1) l c hne
    rw [List.range'_succ, List.foldl_cons]
    rw [rowP_succ] at hne hle hmono ⊢
    unfold stepP
    rw [stepP_eq hg _ (by omega)]
    by_cases hw : W (h * ng + l) < c
    · rw [if_pos hw] at hne hle hmono ⊢
      by_cases hp : P (W (h * ng + l)) = gtStepK GM (P h) l
      · rw [if_pos hp] at hne hle hmono ⊢
        rw [← hp, hs.seen _ (by omega), decide_eq_true hw]
        exact ih (l + 1) c s (by omega) hhc hs ht hne hle
      · rw [if_neg hp] at hne
        exact absurd rfl hne
    · rw [if_neg hw] at hne hle hmono ⊢
      by_cases hn : W (h * ng + l) = c ∧ P c = gtStepK GM (P h) l ∧ PAR c = h ∧ LAB c = l
      · rw [if_pos hn] at hne hle hmono ⊢
        obtain ⟨hwc, hpc, hpar, hlab⟩ := hn
        have hcN : c < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
          (Nat.le_trans (rowP_mono (gtStepK GM) h k (l + 1) (c + 1) hne) hle)
        rw [← hpc, hs.seen _ hcN, decide_eq_false (Nat.lt_irrefl c)]
        simp only [Bool.not_false, ↓reduceIte]
        have hm := matchP_push hP hinj hs hcN
        rw [hpar, hlab] at hm
        refine ih (l + 1) (c + 1) _ (by omega) (by omega) hm (fun i h0 hi => ?_) hne hle
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ht i h0 hi
        · exact ⟨by omega, by omega, by rw [hpar, hlab, hpc]⟩
      · rw [if_neg hn] at hne
        exact absurd rfl hne

theorem runP_replay {gs : Array (Array ℕ)} (hng : gs.size = ng)
    (hg : ∀ l < ng, gs[l]! = unpackR 24 (GM l)) (hN : 0 < N)
    (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) :
    ∀ fuel h c (s : IStateP), c ≤ N →
      PMatch P PAR LAB N c s → PTree GM P PAR LAB ng c →
      bfsRunK (gtStepK GM) P PAR LAB W ng (N + 1) fuel h c = N →
      PMatch P PAR LAB N N (toIP (runP gs (withHP s h))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s _ _ _ hr
    have : bfsRunK (gtStepK GM) P PAR LAB W ng (N + 1) 0 h c = 0 := rfl
    omega
  | succ fuel ih =>
    intro h c s hcN hs ht hr
    have hmono := runP_mono (P := P) (PAR := PAR) (LAB := LAB) (W := W)
      (ng := ng) (gtStepK GM) (N + 1) (fuel + 1) h c (by omega)
    rw [runP_unfold, hs.size]
    rw [runP_succ] at hr hmono
    by_cases hc : h < c
    · have hc' : h < c ∧ c < N + 1 := ⟨hc, by omega⟩
      rw [if_pos hc'] at hr hmono
      rw [if_pos hc]
      by_cases h0 : bfsRowK (gtStepK GM) P PAR LAB W ng h ng 0 c = 0
      · rw [if_pos h0] at hr
        omega
      · rw [if_neg h0] at hr hmono
        have hle : bfsRowK (gtStepK GM) P PAR LAB W ng h ng 0 c ≤ N :=
          hr ▸ runP_mono (gtStepK GM) (N + 1) fuel (h + 1) _ (by omega)
        rw [hs.pts h hc, hng]
        obtain ⟨hs', ht'⟩ := rowP_replay (W := W) hg hP hinj ng 0 c s (by omega) hc hs ht h0 hle
        exact ih (h + 1) _ _ hle hs' ht' hr
    · have hc' : ¬ (h < c ∧ c < N + 1) := fun e => hc e.1
      rw [if_neg hc'] at hr
      rw [if_neg hc]
      subst hr
      exact hs

theorem startP_match (hN : 0 < N) (hP : ∀ i < N, P i < 2 ^ 576)
    (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) (hroot : oneR = unpackR 24 (P 0)) :
    PMatch P PAR LAB N 1 (((∅ : Std.HashMap (Array ℕ) Unit).insert oneR ()), #[oneR], #[]) := by
  refine ⟨rfl, fun i hi => ?_, rfl, fun i hi => absurd hi (by omega), ?_⟩
  · obtain rfl : i = 0 := by omega
    exact hroot
  · intro w hw
    rw [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, hroot,
      unpack_ne hP hinj hN hw]
    by_cases e : 0 = w
    · subst e
      simp
    · rw [decide_eq_false e, decide_eq_false (by omega)]

theorem bfsPl_of_K {gs : Array (Array ℕ)} {S : ℕ → ℕ} (hng : gs.size = ng)
    (hg : ∀ l < ng, gs[l]! = unpackR 24 (GM l))
    (h : gtPinK GM ng (N + 1) N P PAR LAB W S = true) :
    bfsPl gs = (List.range (N - 1)).map fun i => (PAR (1 + i), LAB (1 + i)) := by
  have hb := h
  unfold gtPinK at hb
  rw [bAnd_eq', Bool.and_eq_true] at hb
  have hk := hb.1
  unfold bfsK at hk
  simp only [bAnd_eq', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hk
  obtain ⟨hN, hP0, -, -, hd, hr⟩ := hk
  obtain ⟨hP, hinj⟩ := bfsDistK_sound hd
  have hroot : oneR = unpackR 24 (P 0) := by rw [hP0, idM_eq, oneR_eq]
  have hs := startP_match (PAR := PAR) (LAB := LAB) hN hP hinj hroot
  have hm := runP_replay (W := W) hng hg hN hP hinj (N + 1) 0 1 _ (by omega) hs
    (fun i h0 hi => absurd hi (by omega)) hr
  rw [bfsPl_eq_run]
  have e := eq_ofFn (toIP (runP gs (withHP (((∅ : Std.HashMap (Array ℕ) Unit).insert oneR ()),
    #[oneR], #[]) 0))).2.2 (fun i => (PAR (1 + i), LAB (1 + i))) (N - 1) (by have := hm.psize; omega)
    (fun i hi => hm.pairs i (by omega))
  change (toIP _).2.2.toList = _
  rw [e, Array.toList_ofFn, List.ofFn_eq_map]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp

end CFSG.KC.D4QK

end
