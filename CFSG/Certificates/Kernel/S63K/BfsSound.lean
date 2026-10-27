module

public import CFSG.Certificates.Kernel.S63K.Pack
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.S63K

open CFSG.KC.Co1F2 CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native CFSG.KS.SporSch.M24
open CFSG.KC.Enum CFSG.KS

abbrev IState := Std.HashMap (Array ℕ) Unit × Array (Array ℕ) × Array ℕ × Array ℕ

@[expose] def innerE (gs : Array (Array ℕ)) (y : Array ℕ) (i k : ℕ) (s : IState) :
    Id (ForInStep IState) :=
  if (!s.1.contains (mulR gs[k]! y)) = true then
    pure (ForInStep.yield (s.1.insert (mulR gs[k]! y) (), s.2.1.push (mulR gs[k]! y),
      s.2.2.1.push i, s.2.2.2.push k))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

abbrev OState := Std.HashMap (Array ℕ) Unit × Array (Array ℕ) × Array ℕ × Array ℕ × ℕ

@[expose] def outerE (gs : Array (Array ℕ)) (_ : Unit) (s : OState) : Id (ForInStep OState) :=
  if s.2.2.2.2 < s.2.1.size then
    pure (ForInStep.yield ((fun t : IState => (t.1, t.2.1, t.2.2.1, t.2.2.2, s.2.2.2.2 + 1))
      (Id.run (forIn [:gs.size] (s.1, s.2.1, s.2.2.1, s.2.2.2.1)
        (innerE gs s.2.1[s.2.2.2.2]! s.2.2.2.2)))))
  else pure (ForInStep.done s)

@[expose] def runE (gs : Array (Array ℕ)) (s : OState) : OState :=
  Id.run (forIn Lean.Loop.mk s (outerE gs))

@[expose] def stepE (gs : Array (Array ℕ)) (y : Array ℕ) (i : ℕ) (s : IState) (k : ℕ) : IState :=
  if (!s.1.contains (mulR gs[k]! y)) = true then
    (s.1.insert (mulR gs[k]! y) (), s.2.1.push (mulR gs[k]! y), s.2.2.1.push i, s.2.2.2.push k)
  else s

theorem forIn_yield {β : Type} (g : β → ℕ → β) (f : ℕ → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g b a)) :
    ∀ (l : List ℕ) (init : β), forIn (m := Id) l init f = l.foldl g init
  | [], _ => rfl
  | a :: l, init => by
    rw [List.forIn_cons, hf]
    exact forIn_yield g f hf l (g init a)

theorem inner_eq (gs : Array (Array ℕ)) (y : Array ℕ) (i : ℕ) (s : IState) :
    Id.run (forIn [:gs.size] s (innerE gs y i)) = (List.range' 0 gs.size).foldl (stepE gs y i) s := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply forIn_yield
  intro k t
  unfold innerE stepE
  split <;> rfl

theorem loop_unfold {β : Type} (f : Unit → β → Id (ForInStep β)) (b : β) :
    forIn (m := Id) Lean.Loop.mk b f =
      (match f () b with | .done v => v | .yield v => forIn (m := Id) Lean.Loop.mk v f) :=
  Lean.Loop.forIn_eq_of_monadTail

@[expose] def withH (t : IState) (h : ℕ) : OState := (t.1, t.2.1, t.2.2.1, t.2.2.2, h)

@[expose] def toI (r : OState) : IState := (r.1, r.2.1, r.2.2.1, r.2.2.2.1)

theorem runE_unfold (gs : Array (Array ℕ)) (s : IState) (h : ℕ) :
    runE gs (withH s h) = if h < s.2.1.size then
      runE gs (withH ((List.range' 0 gs.size).foldl (stepE gs s.2.1[h]! h) s) (h + 1))
      else withH s h := by
  unfold runE
  simp only [Id.run]
  rw [loop_unfold]
  unfold outerE withH
  dsimp only
  by_cases hc : h < s.2.1.size
  · rw [if_pos hc, if_pos hc]
    dsimp only [pure]
    rw [inner_eq]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem enumBFS_eq_run (gs : Array (Array ℕ)) :
    enumBFS gs = (fun r : OState => (r.2.1, r.2.2.1, r.2.2.2.1))
      (runE gs (withH (((∅ : Std.HashMap (Array ℕ) Unit).insert oneR ()), #[oneR], #[0], #[0]) 0)) :=
  rfl

variable {G P PAR LAB W : ℕ → ℕ} {ng N : ℕ}

@[expose] noncomputable def stepK (G : ℕ → ℕ) (x l : ℕ) : ℕ := CFSG.KC.F2W.mulW 24 (G l) x

@[expose] def SeenOK (P : ℕ → ℕ) (N : ℕ) (t : Std.HashMap (Array ℕ) Unit) (c : ℕ) : Prop :=
  ∀ w < N, t.contains (unpackR 24 (P w)) = decide (w < c)

structure EMatch (P PAR LAB : ℕ → ℕ) (N c : ℕ) (s : IState) : Prop where
  size : s.2.1.size = c
  pts : ∀ i < c, s.2.1[i]! = unpackR 24 (P i)
  psize : s.2.2.1.size = c
  par : ∀ i < c, s.2.2.1[i]! = PAR i
  lsize : s.2.2.2.size = c
  lab : ∀ i < c, s.2.2.2[i]! = LAB i
  seen : SeenOK P N s.1 c

@[expose] def ETree (G P PAR LAB : ℕ → ℕ) (ng c : ℕ) : Prop :=
  ∀ i, 0 < i → i < c → PAR i < i ∧ LAB i < ng ∧ P i = stepK G (P (PAR i)) (LAB i)

theorem push_lt {β : Type} [Inhabited β] (a : Array β) (x : β) {j : ℕ} (h : j < a.size) :
    (a.push x)[j]! = a[j]! := by
  rw [getElem!_pos (a.push x) j (by rw [Array.size_push]; omega), getElem!_pos a j h,
    Array.getElem_push_lt h]

theorem push_size {β : Type} [Inhabited β] (a : Array β) (x : β) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem unpack_ne (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b)
    {a b : ℕ} (ha : a < N) (hb : b < N) :
    (unpackR 24 (P a) == unpackR 24 (P b)) = decide (a = b) := by
  rw [beq_unpackR, Nat.mod_eq_of_lt (hP a ha), Nat.mod_eq_of_lt (hP b hb)]
  by_cases h : a = b
  · subst h
    simp
  · rw [decide_eq_false h]
    cases e : Nat.beq (P a) (P b)
    · rfl
    · exact absurd (hinj a ha b hb (Nat.eq_of_beq_eq_true e)) h

theorem seen_ins (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b)
    {t : Std.HashMap (Array ℕ) Unit} {c : ℕ} (ht : SeenOK P N t c) (hc : c < N) :
    SeenOK P N (t.insert (unpackR 24 (P c)) ()) (c + 1) := by
  intro w hw
  rw [Std.HashMap.contains_insert, unpack_ne hP hinj hc hw, ht w hw]
  by_cases h : c = w
  · subst h
    simp
  · simp only [decide_eq_false h, Bool.false_or, decide_eq_decide]
    omega

theorem match_push {c : ℕ} {s : IState} (hP : ∀ i < N, P i < 2 ^ 576)
    (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) (hs : EMatch P PAR LAB N c s) (hc : c < N) :
    EMatch P PAR LAB N (c + 1)
      (s.1.insert (unpackR 24 (P c)) (), s.2.1.push (unpackR 24 (P c)), s.2.2.1.push (PAR c),
        s.2.2.2.push (LAB c)) := by
  obtain ⟨hsz, hpts, hpsz, hpar, hlsz, hlab, hseen⟩ := hs
  refine ⟨by simp [hsz], fun i hi => ?_, by simp [hpsz], fun i hi => ?_, by simp [hlsz],
    fun i hi => ?_, seen_ins hP hinj hseen hc⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [push_lt _ _ (by omega)]
      exact hpts i hi
    · rw [← hsz, push_size, hsz]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [push_lt _ _ (by omega)]
      exact hpar i hi
    · rw [← hpsz, push_size, hpsz]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [push_lt _ _ (by omega)]
      exact hlab i hi
    · rw [← hlsz, push_size, hlsz]

theorem bfsRowK_zero (h l c : ℕ) : bfsRowK (stepK G) P PAR LAB W ng h 0 l c = c := rfl

theorem bfsRowK_succ (h k l c : ℕ) :
    bfsRowK (stepK G) P PAR LAB W ng h (k + 1) l c =
      if W (h * ng + l) < c then
        (if P (W (h * ng + l)) = stepK G (P h) l then bfsRowK (stepK G) P PAR LAB W ng h k (l + 1) c
          else 0)
      else if W (h * ng + l) = c ∧ P c = stepK G (P h) l ∧ PAR c = h ∧ LAB c = l then
        bfsRowK (stepK G) P PAR LAB W ng h k (l + 1) (c + 1)
      else 0 := by
  change strictN (W (Nat.add (Nat.mul h ng) l)) (fun w =>
      strictN (stepK G (P h) l) fun y =>
      nIf(Nat.blt w c, nIf(Nat.beq (P w) y, bfsRowK (stepK G) P PAR LAB W ng h k (Nat.succ l) c,
        nat_lit 0),
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (P c) y, bAnd(Nat.beq (PAR c) h, Nat.beq (LAB c) l))),
          bfsRowK (stepK G) P PAR LAB W ng h k (Nat.succ l) (Nat.succ c), nat_lit 0))) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq,
    MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]
  rfl

theorem bfsRowK_mono (h : ℕ) :
    ∀ k l c, bfsRowK (stepK G) P PAR LAB W ng h k l c ≠ 0 →
      c ≤ bfsRowK (stepK G) P PAR LAB W ng h k l c := by
  intro k
  induction k with
  | zero => intro l c _; exact Nat.le_refl c
  | succ k ih =>
    intro l c hne
    rw [bfsRowK_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact ih _ _ hne
      · exact absurd rfl hne
    · rw [if_neg ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact Nat.le_of_succ_le (ih _ _ hne)
      · exact absurd rfl hne

theorem bfsRunK_succ (cap fuel h c : ℕ) :
    bfsRunK (stepK G) P PAR LAB W ng cap (fuel + 1) h c =
      if h < c ∧ c < cap then
        (if bfsRowK (stepK G) P PAR LAB W ng h ng 0 c = 0 then 0
         else bfsRunK (stepK G) P PAR LAB W ng cap fuel (h + 1)
           (bfsRowK (stepK G) P PAR LAB W ng h ng 0 c))
      else c := by
  change nIf(bAnd(Nat.blt h c, Nat.blt c cap),
      strictN (bfsRowK (stepK G) P PAR LAB W ng h ng (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0,
          bfsRunK (stepK G) P PAR LAB W ng cap fuel (Nat.succ h) c'), c) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq,
    MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]

theorem bfsRunK_mono (cap : ℕ) :
    ∀ fuel h c, bfsRunK (stepK G) P PAR LAB W ng cap fuel h c ≠ 0 →
      c ≤ bfsRunK (stepK G) P PAR LAB W ng cap fuel h c := by
  intro fuel
  induction fuel with
  | zero => intro h c hne; exact absurd rfl hne
  | succ fuel ih =>
    intro h c hne
    rw [bfsRunK_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · exact absurd rfl hne
      · rw [if_neg ‹_›]
        exact Nat.le_trans (bfsRowK_mono h ng 0 c ‹_›) (ih _ _ hne)
    · rw [if_neg ‹_›]

theorem step_eq {gs : Array (Array ℕ)} (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l)) (x : ℕ) {l : ℕ}
    (hl : l < ng) : mulR gs[l]! (unpackR 24 x) = unpackR 24 (stepK G x l) := by
  rw [hg l hl, mulR_unpackR]
  rfl

theorem row_replay {gs : Array (Array ℕ)} (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l))
    (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) {h : ℕ} :
    ∀ k l c (s : IState), l + k ≤ ng → h < c →
      EMatch P PAR LAB N c s → ETree G P PAR LAB ng c →
      bfsRowK (stepK G) P PAR LAB W ng h k l c ≠ 0 → bfsRowK (stepK G) P PAR LAB W ng h k l c ≤ N →
      EMatch P PAR LAB N (bfsRowK (stepK G) P PAR LAB W ng h k l c)
          ((List.range' l k).foldl (stepE gs (unpackR 24 (P h)) h) s) ∧
        ETree G P PAR LAB ng (bfsRowK (stepK G) P PAR LAB W ng h k l c) := by
  intro k
  induction k with
  | zero =>
    intro l c s _ _ hs ht _ _
    exact ⟨hs, ht⟩
  | succ k ih =>
    intro l c s hlk hhc hs ht hne hle
    have hmono := bfsRowK_mono (G := G) (P := P) (PAR := PAR) (LAB := LAB) (W := W)
      (ng := ng) h (k + 1) l c hne
    rw [List.range'_succ, List.foldl_cons]
    rw [bfsRowK_succ] at hne hle hmono ⊢
    unfold stepE
    rw [step_eq hg _ (by omega)]
    by_cases hw : W (h * ng + l) < c
    · rw [if_pos hw] at hne hle hmono ⊢
      by_cases hp : P (W (h * ng + l)) = stepK G (P h) l
      · rw [if_pos hp] at hne hle hmono ⊢
        have hcN : c ≤ N := Nat.le_trans hmono hle
        rw [← hp, hs.seen _ (by omega), decide_eq_true hw]
        exact ih (l + 1) c s (by omega) hhc hs ht hne hle
      · rw [if_neg hp] at hne
        exact absurd rfl hne
    · rw [if_neg hw] at hne hle hmono ⊢
      by_cases hn : W (h * ng + l) = c ∧ P c = stepK G (P h) l ∧ PAR c = h ∧ LAB c = l
      · rw [if_pos hn] at hne hle hmono ⊢
        obtain ⟨hwc, hpc, hpar, hlab⟩ := hn
        have hcN : c < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
          (Nat.le_trans (bfsRowK_mono h k (l + 1) (c + 1) hne) hle)
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

theorem run_replay {gs : Array (Array ℕ)} (hng : gs.size = ng)
    (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l)) (hN : 0 < N)
    (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) :
    ∀ fuel h c (s : IState), c ≤ N →
      EMatch P PAR LAB N c s → ETree G P PAR LAB ng c →
      bfsRunK (stepK G) P PAR LAB W ng (N + 1) fuel h c = N →
      EMatch P PAR LAB N N (toI (runE gs (withH s h))) ∧ ETree G P PAR LAB ng N := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s _ _ _ hr
    have : bfsRunK (stepK G) P PAR LAB W ng (N + 1) 0 h c = 0 := rfl
    omega
  | succ fuel ih =>
    intro h c s hcN hs ht hr
    have hmono := bfsRunK_mono (G := G) (P := P) (PAR := PAR) (LAB := LAB) (W := W)
      (ng := ng) (N + 1) (fuel + 1) h c (by omega)
    rw [runE_unfold, hs.size]
    rw [bfsRunK_succ] at hr hmono
    by_cases hc : h < c
    · have hc' : h < c ∧ c < N + 1 := ⟨hc, by omega⟩
      rw [if_pos hc'] at hr hmono
      rw [if_pos hc]
      by_cases h0 : bfsRowK (stepK G) P PAR LAB W ng h ng 0 c = 0
      · rw [if_pos h0] at hr
        omega
      · rw [if_neg h0] at hr hmono
        have hle : bfsRowK (stepK G) P PAR LAB W ng h ng 0 c ≤ N :=
          hr ▸ bfsRunK_mono (N + 1) fuel (h + 1) _ (by omega)
        rw [hs.pts h hc, hng]
        obtain ⟨hs', ht'⟩ := row_replay (W := W) hg hP hinj ng 0 c s (by omega) hc hs ht h0 hle
        exact ih (h + 1) _ _ hle hs' ht' hr
    · have hc' : ¬ (h < c ∧ c < N + 1) := fun e => hc e.1
      rw [if_neg hc'] at hr
      rw [if_neg hc]
      subst hr
      exact ⟨hs, ht⟩

theorem eq_ofFn {β : Type} [Inhabited β] (a : Array β) (f : ℕ → β) (N : ℕ)
    (hs : a.size = N) (h : ∀ i < N, a[i]! = f i) : a = Array.ofFn (n := N) fun i => f i.val := by
  apply Array.ext
  · rw [hs, Array.size_ofFn]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← h i (by omega), getElem!_pos a i h1]

theorem bfsK_sound {S : ℕ → ℕ} {cap R : ℕ}
    (h : bfsK (stepK G) P PAR LAB W S ng cap N R = true) :
    0 < N ∧ P 0 = R ∧ PAR 0 = 0 ∧ LAB 0 = 0 ∧ bfsDistK P S N = true ∧
      bfsRunK (stepK G) P PAR LAB W ng cap (N + 1) 0 1 = N := by
  unfold bfsK at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem strict_of {S : ℕ → ℕ} (h : ∀ k, k + 1 < N → P (S k) < P (S (k + 1))) :
    ∀ a b, a < b → b < N → P (S a) < P (S b) := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
    · exact Nat.lt_trans (ih hab (by omega)) (h b hb)
    · exact h a hb

theorem bfsDistK_sound {S : ℕ → ℕ} (h : bfsDistK P S N = true) :
    (∀ i < N, P i < 2 ^ 576) ∧ ∀ a < N, ∀ b < N, P a = P b → a = b := by
  unfold bfsDistK at h
  rw [MatL.allN_iff] at h
  have h' : ∀ k < N, S k < N ∧ P k < 2 ^ 576 ∧ (k + 1 = N ∨ P (S k) < P (S (k + 1))) := by
    intro k hk
    have := h k hk
    simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at this
    refine ⟨this.1, ?_, ?_⟩
    · have e : Nat.shiftLeft 1 576 = 2 ^ 576 := Nat.one_shiftLeft 576
      rw [← e]; exact this.2.1
    · have h3 := this.2.2
      by_cases hk1 : k + 1 = N
      · exact Or.inl hk1
      · right
        have hb : Nat.beq (Nat.succ k) N = false := by
          cases e : Nat.beq (Nat.succ k) N
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true e) hk1
        rw [hb] at h3
        simpa using h3
  have hst := strict_of (P := P) (S := S) (N := N) fun k hk =>
    ((h' k (by omega)).2.2.resolve_left (by omega))
  refine ⟨fun i hi => (h' i hi).2.1, ?_⟩
  let f : Fin N → Fin N := fun k => ⟨S k.val, (h' k.val k.2).1⟩
  have hinj : Function.Injective f := by
    intro a b e
    have e' : S a.val = S b.val := congrArg Fin.val e
    apply Fin.ext
    rcases Nat.lt_trichotomy a.val b.val with hab | hab | hab
    · have := hst _ _ hab b.2; rw [e'] at this; omega
    · exact hab
    · have := hst _ _ hab a.2; rw [e'] at this; omega
  have hsurj := Finite.surjective_of_injective hinj
  intro a ha b hb e
  obtain ⟨a', ha'⟩ := hsurj ⟨a, ha⟩
  obtain ⟨b', hb'⟩ := hsurj ⟨b, hb⟩
  have ea : S a'.val = a := congrArg Fin.val ha'
  have eb : S b'.val = b := congrArg Fin.val hb'
  rcases Nat.lt_trichotomy a'.val b'.val with hab | hab | hab
  · have := hst _ _ hab b'.2; rw [ea, eb] at this; omega
  · rw [← ea, ← eb, hab]
  · have := hst _ _ hab a'.2; rw [ea, eb] at this; omega

theorem start_match (hN : 0 < N) (hP : ∀ i < N, P i < 2 ^ 576)
    (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) (hroot : oneR = unpackR 24 (P 0))
    (hpar0 : PAR 0 = 0) (hlab0 : LAB 0 = 0) :
    EMatch P PAR LAB N 1 (((∅ : Std.HashMap (Array ℕ) Unit).insert oneR ()), #[oneR], #[0], #[0]) := by
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

theorem final_eq (R : OState) (hm : EMatch P PAR LAB N N (toI R)) :
    (fun r : OState => (r.2.1, r.2.2.1, r.2.2.2.1)) R =
      (Array.ofFn (n := N) (fun i => unpackR 24 (P i.val)),
        Array.ofFn (n := N) (fun i => PAR i.val), Array.ofFn (n := N) (fun i => LAB i.val)) := by
  have h1 := eq_ofFn (toI R).2.1 (fun i => unpackR 24 (P i)) N hm.size hm.pts
  have h2 := eq_ofFn (toI R).2.2.1 PAR N hm.psize hm.par
  have h3 := eq_ofFn (toI R).2.2.2 LAB N hm.lsize hm.lab
  change (R.2.1, R.2.2.1, R.2.2.2.1) = _
  change R.2.1 = _ at h1
  change R.2.2.1 = _ at h2
  change R.2.2.2.1 = _ at h3
  rw [h1, h2, h3]

theorem mkIdx_eq (L : Array (Array ℕ)) :
    mkIdx L = (List.range' 0 L.size).foldl (fun m i => m.insert L[i]! i) ∅ := by
  unfold mkIdx
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply forIn_yield
  intro i t
  rfl

theorem mkIdx_fold (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) :
    ∀ c ≤ N, ∀ w < N,
      ((List.range' 0 c).foldl (fun m i => m.insert (Array.ofFn (n := N)
        (fun i => unpackR 24 (P i.val)))[i]! i) (∅ : Std.HashMap (Array ℕ) ℕ)).getD
        (unpackR 24 (P w)) 0 = if w < c then w else 0 := by
  intro c
  induction c with
  | zero =>
    intro _ w _
    simp
  | succ c ih =>
    intro hc w hw
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getD_insert, Nat.zero_add, Nat.one_mul]
    have hget : (Array.ofFn (n := N) (fun i => unpackR 24 (P i.val)))[c]! = unpackR 24 (P c) := by
      rw [getElem!_pos _ c (by simp; omega)]
      simp
    rw [hget, unpack_ne hP hinj (by omega) hw, ih (by omega) w hw]
    by_cases e : c = w
    · subst e
      simp
    · simp only [decide_eq_false e, Bool.false_eq_true, ↓reduceIte]
      by_cases hwc : w < c
      · rw [if_pos hwc, if_pos (by omega)]
      · rw [if_neg hwc, if_neg (by omega)]

theorem lookup_mkIdx (hP : ∀ i < N, P i < 2 ^ 576) (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b)
    {w : ℕ} (hw : w < N) :
    lookup (mkIdx (Array.ofFn (n := N) (fun i => unpackR 24 (P i.val)))) (unpackR 24 (P w)) = w := by
  unfold lookup
  rw [mkIdx_eq, Array.size_ofFn, mkIdx_fold hP hinj N le_rfl w hw, if_pos hw]

@[expose] noncomputable def ipK (X : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, q => q
  | n + 1, p, q => if p % 2 ^ 576 = idP then q else ipK X n (CFSG.KC.F2W.mulW 24 p X) p

theorem idP_lt : idP < 2 ^ 576 := by
  unfold idP
  decide

theorem enumBFS_of_K {gs : Array (Array ℕ)} {S : ℕ → ℕ} (hng : gs.size = ng)
    (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l))
    (h : bfsK (stepK G) P PAR LAB W S ng (N + 1) N idP = true) :
    enumBFS gs = (Array.ofFn (n := N) (fun i => unpackR 24 (P i.val)),
        Array.ofFn (n := N) (fun i => PAR i.val), Array.ofFn (n := N) (fun i => LAB i.val)) ∧
      ETree G P PAR LAB ng N ∧ (∀ i < N, P i < 2 ^ 576) ∧
      ∀ a < N, ∀ b < N, P a = P b → a = b := by
  obtain ⟨hN, hP0, hpar0, hlab0, hd, hr⟩ := bfsK_sound h
  obtain ⟨hP, hinj⟩ := bfsDistK_sound hd
  have hroot : oneR = unpackR 24 (P 0) := by rw [hP0, oneR_eq]
  have hs := start_match hN hP hinj hroot hpar0 hlab0
  obtain ⟨hm, ht⟩ := run_replay (W := W) hng hg hN hP hinj (N + 1) 0 1 _ (by omega) hs
    (fun i h0 hi => absurd hi (by omega)) hr
  refine ⟨?_, ht, hP, hinj⟩
  rw [enumBFS_eq_run]
  exact final_eq _ hm

end CFSG.KC.S63K

end
