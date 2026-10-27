module

public import CFSG.Certificates.Kernel.S63K.ConjTreeSound

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.S63K

open CFSG.KC.Co1F2 CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native CFSG.KS.SporSch.M24
open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2

variable {F : ℕ → ℕ → ℕ} {P PAR LAB W : ℕ → ℕ} {ng N : ℕ}

theorem rowF_succ (h k l c : ℕ) :
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
  simp only [MatL.strictN_eq, MatL.nIf_eq,
    MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]
  rfl

theorem rowF_mono (h : ℕ) :
    ∀ k l c, bfsRowK F P PAR LAB W ng h k l c ≠ 0 → c ≤ bfsRowK F P PAR LAB W ng h k l c := by
  intro k
  induction k with
  | zero => intro l c _; exact Nat.le_refl c
  | succ k ih =>
    intro l c hne
    rw [rowF_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact ih _ _ hne
      · exact absurd rfl hne
    · rw [if_neg ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact Nat.le_of_succ_le (ih _ _ hne)
      · exact absurd rfl hne

theorem runF_succ (cap fuel h c : ℕ) :
    bfsRunK F P PAR LAB W ng cap (fuel + 1) h c =
      if h < c ∧ c < cap then
        (if bfsRowK F P PAR LAB W ng h ng 0 c = 0 then 0
         else bfsRunK F P PAR LAB W ng cap fuel (h + 1) (bfsRowK F P PAR LAB W ng h ng 0 c))
      else c := by
  change nIf(bAnd(Nat.blt h c, Nat.blt c cap),
      strictN (bfsRowK F P PAR LAB W ng h ng (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0,
          bfsRunK F P PAR LAB W ng cap fuel (Nat.succ h) c'), c) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq,
    MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]

theorem runF_mono (cap : ℕ) :
    ∀ fuel h c, bfsRunK F P PAR LAB W ng cap fuel h c ≠ 0 →
      c ≤ bfsRunK F P PAR LAB W ng cap fuel h c := by
  intro fuel
  induction fuel with
  | zero => intro h c hne; exact absurd rfl hne
  | succ fuel ih =>
    intro h c hne
    rw [runF_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · exact absurd rfl hne
      · rw [if_neg ‹_›]
        exact Nat.le_trans (rowF_mono h ng 0 c ‹_›) (ih _ _ hne)
    · rw [if_neg ‹_›]

theorem rowF_clos (h : ℕ) : ∀ k l c, bfsRowK F P PAR LAB W ng h k l c ≠ 0 →
    ∀ j, l ≤ j → j < l + k → W (h * ng + j) < bfsRowK F P PAR LAB W ng h k l c ∧
      P (W (h * ng + j)) = F (P h) j := by
  intro k
  induction k with
  | zero => intro l c _ j h1 h2; omega
  | succ k ih =>
    intro l c hne j h1 h2
    rw [rowF_succ] at hne ⊢
    split at hne
    · rename_i hw
      rw [if_pos hw]
      split at hne
      · rename_i hp
        rw [if_pos hp]
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact ⟨Nat.lt_of_lt_of_le hw (rowF_mono h _ _ _ hne), hp⟩
        · exact ih _ _ hne j (by omega) (by omega)
      · exact absurd rfl hne
    · rename_i hw
      rw [if_neg hw]
      split at hne
      · rename_i hp
        rw [if_pos hp]
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · rw [hp.1]
          exact ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self c) (rowF_mono h _ _ _ hne), hp.2.1⟩
        · exact ih _ _ hne j (by omega) (by omega)
      · exact absurd rfl hne

theorem runF_clos (cap : ℕ) : ∀ fuel h c, bfsRunK F P PAR LAB W ng cap fuel h c ≠ 0 →
    bfsRunK F P PAR LAB W ng cap fuel h c < cap →
    ∀ h', h ≤ h' → h' < bfsRunK F P PAR LAB W ng cap fuel h c → ∀ l < ng,
      W (h' * ng + l) < bfsRunK F P PAR LAB W ng cap fuel h c ∧
        P (W (h' * ng + l)) = F (P h') l := by
  intro fuel
  induction fuel with
  | zero => intro h c hne; exact absurd rfl hne
  | succ fuel ih =>
    intro h c hne hcap h' hh' hlt l hl
    rw [runF_succ] at hne hcap hlt ⊢
    split at hne
    · rename_i hc
      rw [if_pos hc] at hcap hlt ⊢
      split at hne
      · exact absurd rfl hne
      · rename_i hr
        rw [if_neg hr] at hcap hlt ⊢
        rcases Nat.eq_or_lt_of_le hh' with rfl | hh'
        · obtain ⟨h1, h2⟩ := rowF_clos _ ng 0 c hr l (Nat.zero_le _) (by omega)
          exact ⟨Nat.lt_of_lt_of_le h1 (runF_mono cap fuel _ _ hne), h2⟩
        · exact ih _ _ hne hcap h' hh' hlt l hl
    · rename_i hc
      rw [if_neg hc] at hcap hlt
      exact absurd ⟨by omega, hcap⟩ hc

theorem clos_of_run (hr : bfsRunK F P PAR LAB W ng (N + 1) (N + 1) 0 1 = N) (hN : 0 < N) :
    ∀ h < N, ∀ l < ng, W (h * ng + l) < N ∧ P (W (h * ng + l)) = F (P h) l := by
  have hc := runF_clos (F := F) (P := P) (PAR := PAR) (LAB := LAB) (W := W) (ng := ng) (N + 1)
    (N + 1) 0 1 (by rw [hr]; omega) (by rw [hr]; omega)
  rw [hr] at hc
  exact fun h hh l hl => hc h (Nat.zero_le _) hh l hl

@[expose] def innerC (gs : Array (Array ℕ)) (y : Array ℕ) (i k : ℕ) (s : IState) :
    Id (ForInStep IState) :=
  if (!s.1.contains (conjR gs[k]! y)) = true then
    pure (ForInStep.yield (s.1.insert (conjR gs[k]! y) (), s.2.1.push (conjR gs[k]! y),
      s.2.2.1.push i, s.2.2.2.push k))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

@[expose] def outerC (gs : Array (Array ℕ)) (_ : Unit) (s : OState) : Id (ForInStep OState) :=
  if s.2.2.2.2 < s.2.1.size then
    pure (ForInStep.yield ((fun t : IState => (t.1, t.2.1, t.2.2.1, t.2.2.2, s.2.2.2.2 + 1))
      (Id.run (forIn [:gs.size] (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
        (innerC gs s.2.1[s.2.2.2.2]! s.2.2.2.2)))))
  else pure (ForInStep.done s)

@[expose] def runC (gs : Array (Array ℕ)) (s : OState) : OState :=
  Id.run (forIn Lean.Loop.mk s (outerC gs))

@[expose] def stepC (gs : Array (Array ℕ)) (y : Array ℕ) (i : ℕ) (s : IState) (k : ℕ) : IState :=
  if (!s.1.contains (conjR gs[k]! y)) = true then
    (s.1.insert (conjR gs[k]! y) (), s.2.1.push (conjR gs[k]! y), s.2.2.1.push i, s.2.2.2.push k)
  else s

theorem innerC_eq (gs : Array (Array ℕ)) (y : Array ℕ) (i : ℕ) (s : IState) :
    Id.run (forIn [:gs.size] s (innerC gs y i)) =
      (List.range' 0 gs.size).foldl (stepC gs y i) s := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply forIn_yield
  intro k t
  unfold innerC stepC
  split <;> rfl

theorem runC_unfold (gs : Array (Array ℕ)) (s : IState) (h : ℕ) :
    runC gs (withH s h) = if h < s.2.1.size then
      runC gs (withH ((List.range' 0 gs.size).foldl (stepC gs s.2.1[h]! h) s) (h + 1))
      else withH s h := by
  unfold runC
  simp only [Id.run]
  rw [loop_unfold]
  unfold outerC withH
  dsimp only
  by_cases hc : h < s.2.1.size
  · rw [if_pos hc, if_pos hc]
    dsimp only [pure]
    rw [innerC_eq]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem classBFS_eq_run (gs : Array (Array ℕ)) (x : Array ℕ) :
    classBFS gs x = (fun r : OState => (r.2.1, r.2.2.1, r.2.2.2.1))
      (runC gs (withH (((∅ : Std.HashMap (Array ℕ) Unit).insert x ()), #[x], #[0], #[0]) 0)) :=
  rfl

variable {G : ℕ → ℕ}

@[expose] def FTree (F : ℕ → ℕ → ℕ) (P PAR LAB : ℕ → ℕ) (ng c : ℕ) : Prop :=
  ∀ i, 0 < i → i < c → PAR i < i ∧ LAB i < ng ∧ P i = F (P (PAR i)) (LAB i)

theorem cj_eq {gs : Array (Array ℕ)} (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l)) (x : ℕ) {l : ℕ}
    (hl : l < ng) : conjR gs[l]! (unpackR 24 x) = unpackR 24 (cjStepK G x l) := by
  rw [hg l hl, conjR_unpackR]

theorem rowC_replay {gs : Array (Array ℕ)} (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l))
    (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) {h : ℕ} :
    ∀ k l c (s : IState), l + k ≤ ng → h < c →
      EMatch P PAR LAB N c s → FTree (cjStepK G) P PAR LAB ng c →
      bfsRowK (cjStepK G) P PAR LAB W ng h k l c ≠ 0 →
      bfsRowK (cjStepK G) P PAR LAB W ng h k l c ≤ N →
      EMatch P PAR LAB N (bfsRowK (cjStepK G) P PAR LAB W ng h k l c)
          ((List.range' l k).foldl (stepC gs (unpackR 24 (P h)) h) s) ∧
        FTree (cjStepK G) P PAR LAB ng (bfsRowK (cjStepK G) P PAR LAB W ng h k l c) := by
  intro k
  induction k with
  | zero =>
    intro l c s _ _ hs ht _ _
    exact ⟨hs, ht⟩
  | succ k ih =>
    intro l c s hlk hhc hs ht hne hle
    have hmono := rowF_mono (F := cjStepK G) (P := P) (PAR := PAR) (LAB := LAB) (W := W)
      (ng := ng) h (k + 1) l c hne
    rw [List.range'_succ, List.foldl_cons]
    rw [rowF_succ] at hne hle hmono ⊢
    unfold stepC
    rw [cj_eq hg _ (by omega)]
    by_cases hw : W (h * ng + l) < c
    · rw [if_pos hw] at hne hle hmono ⊢
      by_cases hp : P (W (h * ng + l)) = cjStepK G (P h) l
      · rw [if_pos hp] at hne hle hmono ⊢
        have hcN : c ≤ N := Nat.le_trans hmono hle
        rw [← hp, hs.seen _ (by omega), decide_eq_true hw]
        exact ih (l + 1) c s (by omega) hhc hs ht hne hle
      · rw [if_neg hp] at hne
        exact absurd rfl hne
    · rw [if_neg hw] at hne hle hmono ⊢
      by_cases hn : W (h * ng + l) = c ∧ P c = cjStepK G (P h) l ∧ PAR c = h ∧ LAB c = l
      · rw [if_pos hn] at hne hle hmono ⊢
        obtain ⟨hwc, hpc, hpar, hlab⟩ := hn
        have hcN : c < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
          (Nat.le_trans (rowF_mono h k (l + 1) (c + 1) hne) hle)
        rw [← hpc, hs.seen _ hcN, decide_eq_false (Nat.lt_irrefl c)]
        simp only [Bool.not_false, ↓reduceIte]
        have hm := match_push hP hinj hs hcN
        rw [hpar, hlab] at hm
        refine ih (l + 1) (c + 1) _ (by omega) (by omega) hm (fun i h0 hi => ?_) hne hle
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ht i h0 hi
        · exact ⟨by omega, by omega, by rw [hpar, hlab, hpc]⟩
      · rw [if_neg hn] at hne
        exact absurd rfl hne

theorem runC_replay {gs : Array (Array ℕ)} (hng : gs.size = ng)
    (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l)) (hN : 0 < N)
    (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) :
    ∀ fuel h c (s : IState), c ≤ N →
      EMatch P PAR LAB N c s → FTree (cjStepK G) P PAR LAB ng c →
      bfsRunK (cjStepK G) P PAR LAB W ng (N + 1) fuel h c = N →
      EMatch P PAR LAB N N (toI (runC gs (withH s h))) ∧ FTree (cjStepK G) P PAR LAB ng N := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s _ _ _ hr
    have : bfsRunK (cjStepK G) P PAR LAB W ng (N + 1) 0 h c = 0 := rfl
    omega
  | succ fuel ih =>
    intro h c s hcN hs ht hr
    have hmono := runF_mono (F := cjStepK G) (P := P) (PAR := PAR) (LAB := LAB) (W := W)
      (ng := ng) (N + 1) (fuel + 1) h c (by omega)
    rw [runC_unfold, hs.size]
    rw [runF_succ] at hr hmono
    by_cases hc : h < c
    · have hc' : h < c ∧ c < N + 1 := ⟨hc, by omega⟩
      rw [if_pos hc'] at hr hmono
      rw [if_pos hc]
      by_cases h0 : bfsRowK (cjStepK G) P PAR LAB W ng h ng 0 c = 0
      · rw [if_pos h0] at hr
        omega
      · rw [if_neg h0] at hr hmono
        have hle : bfsRowK (cjStepK G) P PAR LAB W ng h ng 0 c ≤ N :=
          hr ▸ runF_mono (N + 1) fuel (h + 1) _ (by omega)
        rw [hs.pts h hc, hng]
        obtain ⟨hs', ht'⟩ := rowC_replay (W := W) hg hP hinj ng 0 c s (by omega) hc hs ht h0 hle
        exact ih (h + 1) _ _ hle hs' ht' hr
    · have hc' : ¬ (h < c ∧ c < N + 1) := fun e => hc e.1
      rw [if_neg hc'] at hr
      rw [if_neg hc]
      subst hr
      exact ⟨hs, ht⟩

theorem startC_match {x : Array ℕ} (hN : 0 < N) (hP : ∀ i < N, P i < 2 ^ 576)
    (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) (hroot : x = unpackR 24 (P 0))
    (hpar0 : PAR 0 = 0) (hlab0 : LAB 0 = 0) :
    EMatch P PAR LAB N 1 (((∅ : Std.HashMap (Array ℕ) Unit).insert x ()), #[x], #[0], #[0]) := by
  refine ⟨rfl, fun i hi => ?_, rfl, fun i hi => ?_, rfl, fun i hi => ?_, ?_⟩
  · obtain rfl : i = 0 := by omega
    exact hroot
  · obtain rfl : i = 0 := by omega
    exact hpar0.symm
  · obtain rfl : i = 0 := by omega
    exact hlab0.symm
  · intro w hw
    rw [Std.HashMap.contains_insert, Std.HashMap.contains_empty, Bool.or_false, hroot,
      unpack_ne hP hinj hN hw]
    by_cases e : 0 = w
    · subst e
      simp
    · rw [decide_eq_false e, decide_eq_false (by omega)]

structure ClassK (G P PAR LAB W S : ℕ → ℕ) (ng N : ℕ) : Prop where
  pos : 0 < N
  par0 : PAR 0 = 0
  lab0 : LAB 0 = 0
  dist : bfsDistK P S N = true
  run : bfsRunK (cjStepK G) P PAR LAB W ng (N + 1) (N + 1) 0 1 = N

variable {S : ℕ → ℕ}

theorem bfsKF_sound {cap R : ℕ} (h : bfsK F P PAR LAB W S ng cap N R = true) :
    0 < N ∧ P 0 = R ∧ PAR 0 = 0 ∧ LAB 0 = 0 ∧ bfsDistK P S N = true ∧
      bfsRunK F P PAR LAB W ng cap (N + 1) 0 1 = N := by
  unfold bfsK at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem classK_of_bfsK {R : ℕ} (h : bfsK (cjStepK G) P PAR LAB W S ng (N + 1) N R = true) :
    ClassK G P PAR LAB W S ng N ∧ P 0 = R := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bfsKF_sound h
  exact ⟨⟨h1, h3, h4, h5, h6⟩, h2⟩

theorem classBFS_of_K {gs : Array (Array ℕ)} {x : Array ℕ} (hng : gs.size = ng)
    (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l)) (hx : x = unpackR 24 (P 0))
    (hK : ClassK G P PAR LAB W S ng N) :
    classBFS gs x = (ElG P N, Array.ofFn (n := N) (fun i => PAR i.val),
        Array.ofFn (n := N) (fun i => LAB i.val)) ∧
      FTree (cjStepK G) P PAR LAB ng N ∧ (∀ i < N, P i < 2 ^ 576) ∧
      ∀ a < N, ∀ b < N, P a = P b → a = b := by
  obtain ⟨hP, hinj⟩ := bfsDistK_sound hK.dist
  have hs := startC_match hK.pos hP hinj hx hK.par0 hK.lab0
  have hN := hK.pos
  obtain ⟨hm, ht⟩ := runC_replay (W := W) hng hg hN hP hinj (N + 1) 0 1 _ (by omega) hs
    (fun i h0 hi => absurd hi (by omega)) hK.run
  refine ⟨?_, ht, hP, hinj⟩
  rw [classBFS_eq_run]
  exact final_eq _ hm

@[expose] noncomputable def CkG (P PAR LAB : ℕ → ℕ) (N : ℕ) : ClassData :=
  { T := ElG P N, P := Array.ofFn (n := N) (fun i => PAR i.val),
    K := Array.ofFn (n := N) (fun i => LAB i.val), idx := lookup (mkIdx (ElG P N)) }

theorem mkClass_of_K {gs : Array (Array ℕ)} {x : Array ℕ} (hng : gs.size = ng)
    (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l)) (hx : x = unpackR 24 (P 0))
    (hK : ClassK G P PAR LAB W S ng N) : mkClass gs x = CkG P PAR LAB N := by
  unfold mkClass
  rw [(classBFS_of_K hng hg hx hK).1]
  rfl

theorem idx_of_C (hK : ClassK G P PAR LAB W S ng N) {w : ℕ} (hw : w < N) :
    lookup (mkIdx (ElG P N)) (unpackR 24 (P w)) = w :=
  lookup_mkIdx (bfsDistK_sound hK.dist).1 (bfsDistK_sound hK.dist).2 hw

theorem clos_of_C (hK : ClassK G P PAR LAB W S ng N) :
    ∀ h < N, ∀ l < ng, W (h * ng + l) < N ∧ P (W (h * ng + l)) = cjStepK G (P h) l :=
  clos_of_run hK.run hK.pos

theorem classTreeOK_of_K {gs : Array (Array ℕ)} {x : Array ℕ} (hng : gs.size = ng)
    (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l)) (hx : x = unpackR 24 (P 0))
    (hK : ClassK G P PAR LAB W S ng N) :
    classTreeOK gs x (CkG P PAR LAB N).T (CkG P PAR LAB N).P (CkG P PAR LAB N).K
      (CkG P PAR LAB N).idx = true := by
  have F := classBFS_of_K hng hg hx hK
  have hsz : (CkG P PAR LAB N).T.size = N := by simp [CkG, ElG]
  have hN := hK.pos
  unfold classTreeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hsz]
  refine ⟨⟨hN, ?_⟩, ?_⟩
  · change (ElG P N)[0]! = x
    rw [elG_get hN, hx]
  · refine allLt_iff.2 fun i hi => ?_
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    change (validR (ElG P N)[i]! = true ∧ lookup (mkIdx (ElG P N)) (ElG P N)[i]! = i) ∧ (i = 0 ∨
      (((CkG P PAR LAB N).P[i]! < i ∧ (CkG P PAR LAB N).K[i]! < gs.size) ∧
        (ElG P N)[i]! = conjR gs[(CkG P PAR LAB N).K[i]!]! (ElG P N)[(CkG P PAR LAB N).P[i]!]!))
    rw [elG_get hi, validR_unpackR, idx_of_C hK hi, hng]
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    by_cases h0 : i = 0
    · exact Or.inl h0
    · right
      obtain ⟨h1, h2, h3⟩ := F.2.1 i (by omega) hi
      have ep : (CkG P PAR LAB N).P[i]! = PAR i := by simp [CkG, getElem!_pos, hi]
      have ek : (CkG P PAR LAB N).K[i]! = LAB i := by simp [CkG, getElem!_pos, hi]
      rw [ep, ek, elG_get (by omega), cj_eq hg _ h2, ← h3]
      exact ⟨⟨h1, h2⟩, rfl⟩

end CFSG.KC.S63K

end
