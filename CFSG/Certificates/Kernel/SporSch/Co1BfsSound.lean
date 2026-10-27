module

public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas
public import CFSG.Sporadic.Co1Block.CentCheck
public import CFSG.Certificates.Kernel.Co1BMulSound
import all Certificates.Data.CFSGNative.Co1.TwoB
import all Certificates.Data.CFSGNative.Co1.Involutions

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KS.Raw CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block.Native

@[expose] noncomputable def bfsTree (N : Nat) (P PAR LAB : Nat → Nat) : GTree :=
  ⟨Array.ofFn (n := N) fun i => unpack 24 24 (P i.val), Array.ofFn (n := N) fun i => PAR i.val,
    Array.ofFn (n := N) fun i => LAB i.val⟩

@[expose] noncomputable def gensArr (ng : Nat) (GM : Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := ng) fun l => unpack 24 24 (GM l.val)

theorem bfsMemK_sound {P S : Nat → Nat} {N K : Nat} (h : bfsMemK P S N K = true) :
    bfsPosK P S N K < N ∧ P (bfsPosK P S N K) = K := by
  unfold bfsMemK at h
  rw [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem contains_bfsTree {N : Nat} {P PAR LAB : Nat → Nat} {x : Array Nat} {w : Nat} (hw : w < N)
    (hx : unpack 24 24 (P w) = x) : (bfsTree N P PAR LAB).pts.contains x = true := by
  rw [Array.contains_iff_mem]
  simp only [bfsTree, Array.mem_ofFn]
  exact ⟨⟨w, hw⟩, hx⟩

theorem unpackR_eq_unpack (X : Nat) : CFSG.KC.Co1F2.unpackR 24 X = unpack 24 24 X := by
  apply Array.ext
  · rw [MatL.unpack_size]
    simp [CFSG.KC.Co1F2.unpackR]
  · intro i h₁ h₂
    rw [MatL.unpack_getElem]
    simp [CFSG.KC.Co1F2.unpackR, MatL.rowV]

theorem mul_unpackW (X Y : Nat) : CFSG.Sporadic.Co1Schreier.Native.mul (unpack 24 24 X)
    (unpack 24 24 Y) = unpack 24 24 (CFSG.KC.Co1B.mulWK X Y) := by
  rw [← unpackR_eq_unpack, ← unpackR_eq_unpack, ← unpackR_eq_unpack]
  exact CFSG.KC.F2W.mul_unpackW X Y

section Replays

open CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.SmallF2.Native
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co1Block.Native

section Gen

variable {α σ : Type} [Inhabited α]

private def co1BfsInner (stp : α → Nat → α) (mem : σ → α → Bool) (ins : σ → α → Nat → σ)
    (h l : Nat) (s : Array α × Array Nat × Array Nat × σ) :
    Id (ForInStep (Array α × Array Nat × Array Nat × σ)) :=
  if (!mem s.2.2.2 (stp s.1[h]! l)) = true then
    pure (ForInStep.yield (s.1.push (stp s.1[h]! l), s.2.1.push h, s.2.2.1.push l,
      ins s.2.2.2 (stp s.1[h]! l) s.1.size))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

private def co1BfsOuter (stp : α → Nat → α) (mem : σ → α → Bool) (ins : σ → α → Nat → σ)
    (ng cap : Nat) (_ : Unit) (s : Array α × Array Nat × Array Nat × σ × Nat) :
    Id (ForInStep (Array α × Array Nat × Array Nat × σ × Nat)) :=
  if (decide (s.2.2.2.2 < s.1.size) && decide (s.1.size < cap)) = true then
    pure (ForInStep.yield ((fun t : Array α × Array Nat × Array Nat × σ =>
      (t.1, t.2.1, t.2.2.1, t.2.2.2, s.2.2.2.2 + 1))
      (Id.run (forIn [:ng] (s.1, s.2.1, s.2.2.1, s.2.2.2.1) (co1BfsInner stp mem ins s.2.2.2.2)))))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2))

private def co1BfsRun (stp : α → Nat → α) (mem : σ → α → Bool) (ins : σ → α → Nat → σ)
    (ng cap : Nat) (s : Array α × Array Nat × Array Nat × σ × Nat) :
    Array α × Array Nat × Array Nat × σ × Nat :=
  Id.run (forIn Lean.Loop.mk s (co1BfsOuter stp mem ins ng cap))

private def co1BfsIStep (stp : α → Nat → α) (mem : σ → α → Bool) (ins : σ → α → Nat → σ)
    (h : Nat) (s : Array α × Array Nat × Array Nat × σ) (l : Nat) :
    Array α × Array Nat × Array Nat × σ :=
  if (!mem s.2.2.2 (stp s.1[h]! l)) = true then
    (s.1.push (stp s.1[h]! l), s.2.1.push h, s.2.2.1.push l, ins s.2.2.2 (stp s.1[h]! l) s.1.size)
  else s

private theorem co1Bfs_forIn_yield {β : Type} (g : β → Nat → β) (f : Nat → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g b a)) :
    ∀ (l : List Nat) (init : β), forIn (m := Id) l init f = l.foldl g init
  | [], _ => rfl
  | a :: l, init => by
    rw [List.forIn_cons, hf]
    exact co1Bfs_forIn_yield g f hf l (g init a)

private theorem co1Bfs_inner_eq (stp : α → Nat → α) (mem : σ → α → Bool) (ins : σ → α → Nat → σ)
    (h ng : Nat) (s : Array α × Array Nat × Array Nat × σ) :
    Id.run (forIn [:ng] s (co1BfsInner stp mem ins h)) =
      (List.range' 0 ng).foldl (co1BfsIStep stp mem ins h) s := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply co1Bfs_forIn_yield
  intro l t
  unfold co1BfsInner co1BfsIStep
  split <;> rfl

private theorem co1Bfs_loop_unfold {β : Type} (f : Unit → β → Id (ForInStep β)) (b : β) :
    forIn (m := Id) Lean.Loop.mk b f =
      (match f () b with | .done v => v | .yield v => forIn (m := Id) Lean.Loop.mk v f) :=
  Lean.Loop.forIn_eq_of_monadTail

private theorem co1BfsRun_unfold (stp : α → Nat → α) (mem : σ → α → Bool) (ins : σ → α → Nat → σ)
    (ng cap : Nat) (s : Array α × Array Nat × Array Nat × σ) (h : Nat) :
    co1BfsRun stp mem ins ng cap (s.1, s.2.1, s.2.2.1, s.2.2.2, h) =
      if h < s.1.size ∧ s.1.size < cap then
        co1BfsRun stp mem ins ng cap
          ((fun t : Array α × Array Nat × Array Nat × σ => (t.1, t.2.1, t.2.2.1, t.2.2.2, h + 1))
            ((List.range' 0 ng).foldl (co1BfsIStep stp mem ins h) s))
      else (s.1, s.2.1, s.2.2.1, s.2.2.2, h) := by
  unfold co1BfsRun
  simp only [Id.run]
  rw [co1Bfs_loop_unfold]
  unfold co1BfsOuter
  dsimp only
  by_cases hc : h < s.1.size ∧ s.1.size < cap
  · rw [if_pos (by simp [hc.1, hc.2]), if_pos hc]
    dsimp only [pure]
    rw [co1Bfs_inner_eq]
  · rw [if_neg (by simpa using hc), if_neg hc]
    rfl

end Gen

section Kernel

variable {F : Nat → Nat → Nat} {P PAR LAB W : Nat → Nat} {ng : Nat}

private theorem co1Bfs_bfsRowK_zero (h l c : Nat) : bfsRowK F P PAR LAB W ng h 0 l c = c := rfl

private theorem co1Bfs_bfsRowK_succ (h k l c : Nat) :
    bfsRowK F P PAR LAB W ng h (k + 1) l c =
      if W (h * ng + l) < c then
        (if P (W (h * ng + l)) = F (P h) l then bfsRowK F P PAR LAB W ng h k (l + 1) c else 0)
      else if W (h * ng + l) = c ∧ P c = F (P h) l ∧ PAR c = h ∧ LAB c = l then
        bfsRowK F P PAR LAB W ng h k (l + 1) (c + 1)
      else 0 := by
  show strictN (W (Nat.add (Nat.mul h ng) l)) (fun w => strictN (F (P h) l) fun y =>
      nIf(Nat.blt w c, nIf(Nat.beq (P w) y, bfsRowK F P PAR LAB W ng h k (Nat.succ l) c, nat_lit 0),
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (P c) y, bAnd(Nat.beq (PAR c) h, Nat.beq (LAB c) l))),
          bfsRowK F P PAR LAB W ng h k (Nat.succ l) (Nat.succ c), nat_lit 0))) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]
  rfl

private theorem co1Bfs_bfsRowK_mono (h : Nat) :
    ∀ k l c, bfsRowK F P PAR LAB W ng h k l c ≠ 0 → c ≤ bfsRowK F P PAR LAB W ng h k l c := by
  intro k
  induction k with
  | zero => intro l c _; exact Nat.le_refl c
  | succ k ih =>
    intro l c hne
    rw [co1Bfs_bfsRowK_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact ih _ _ hne
      · exact absurd rfl hne
    · rw [if_neg ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact Nat.le_of_succ_le (ih _ _ hne)
      · exact absurd rfl hne

private theorem co1Bfs_bfsRunK_zero (cap h c : Nat) : bfsRunK F P PAR LAB W ng cap 0 h c = 0 := rfl

private theorem co1Bfs_bfsRunK_succ (cap fuel h c : Nat) :
    bfsRunK F P PAR LAB W ng cap (fuel + 1) h c =
      if h < c ∧ c < cap then
        (if bfsRowK F P PAR LAB W ng h ng 0 c = 0 then 0
         else bfsRunK F P PAR LAB W ng cap fuel (h + 1) (bfsRowK F P PAR LAB W ng h ng 0 c))
      else c := by
  show nIf(bAnd(Nat.blt h c, Nat.blt c cap),
      strictN (bfsRowK F P PAR LAB W ng h ng (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, bfsRunK F P PAR LAB W ng cap fuel (Nat.succ h) c'), c) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]

private theorem co1Bfs_bfsRunK_mono (cap : Nat) :
    ∀ fuel h c, bfsRunK F P PAR LAB W ng cap fuel h c ≠ 0 →
      c ≤ bfsRunK F P PAR LAB W ng cap fuel h c := by
  intro fuel
  induction fuel with
  | zero => intro h c hne; exact absurd rfl hne
  | succ fuel ih =>
    intro h c hne
    rw [co1Bfs_bfsRunK_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · exact absurd rfl hne
      · rw [if_neg ‹_›]
        exact Nat.le_trans (co1Bfs_bfsRowK_mono h ng 0 c ‹_›) (Nat.le_of_lt_succ
          (Nat.lt_succ_of_le (ih _ _ hne)))
    · rw [if_neg ‹_›]

end Kernel

section Replay

variable {α σ : Type} [Inhabited α]

private structure Co1BfsMatch (enc : Nat → α) (P PAR LAB : Nat → Nat) (SeenOK : σ → Nat → Prop) (c : Nat)
    (s : Array α × Array Nat × Array Nat × σ) : Prop where
  size : s.1.size = c
  pts : ∀ i < c, s.1[i]! = enc (P i)
  psize : s.2.1.size = c
  par : ∀ i < c, s.2.1[i]! = PAR i
  lsize : s.2.2.1.size = c
  lab : ∀ i < c, s.2.2.1[i]! = LAB i
  seen : SeenOK s.2.2.2 c

private def Co1BfsTree (F : Nat → Nat → Nat) (P PAR LAB : Nat → Nat) (ng c : Nat) : Prop :=
  ∀ i, 0 < i → i < c → PAR i < i ∧ LAB i < ng ∧ P i = F (P (PAR i)) (LAB i)

private theorem co1Bfs_push_lt {β : Type} [Inhabited β] (a : Array β) (x : β) {j : Nat} (h : j < a.size) :
    (a.push x)[j]! = a[j]! := by
  rw [getElem!_pos (a.push x) j (by rw [Array.size_push]; omega), getElem!_pos a j h,
    Array.getElem_push_lt h]

private theorem co1Bfs_push_size {β : Type} [Inhabited β] (a : Array β) (x : β) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

variable {stp : α → Nat → α} {mem : σ → α → Bool} {ins : σ → α → Nat → σ} {enc : Nat → α}
  {SeenOK : σ → Nat → Prop} {F : Nat → Nat → Nat} {P PAR LAB W : Nat → Nat} {ng N : Nat}

private theorem co1Bfs_push_match {c : Nat} {s : Array α × Array Nat × Array Nat × σ}
    (hs : Co1BfsMatch enc P PAR LAB SeenOK c s) {h l : Nat} (hh : PAR c = h) (hl : LAB c = l)
    (hσ : SeenOK (ins s.2.2.2 (enc (P c)) c) (c + 1)) :
    Co1BfsMatch enc P PAR LAB SeenOK (c + 1)
      (s.1.push (enc (P c)), s.2.1.push h, s.2.2.1.push l, ins s.2.2.2 (enc (P c)) s.1.size) := by
  obtain ⟨hsz, hpts, hpsz, hpar, hlsz, hlab, -⟩ := hs
  refine ⟨by simp [hsz], fun i hi => ?_, by simp [hpsz], fun i hi => ?_, by simp [hlsz],
    fun i hi => ?_, by rw [hsz]; exact hσ⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [co1Bfs_push_lt _ _ (by omega)]; exact hpts i hi
    · rw [← hsz, co1Bfs_push_size, hsz]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [co1Bfs_push_lt _ _ (by omega)]; exact hpar i hi
    · rw [← hpsz, co1Bfs_push_size, hpsz, hh]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [co1Bfs_push_lt _ _ (by omega)]; exact hlab i hi
    · rw [← hlsz, co1Bfs_push_size, hlsz, hl]

private theorem co1Bfs_row (hstp : ∀ x l, l < ng → stp (enc x) l = enc (F x l))
    (hmem : ∀ t c w, SeenOK t c → c ≤ N → w < N → mem t (enc (P w)) = decide (w < c))
    (hins : ∀ t c, SeenOK t c → c < N → SeenOK (ins t (enc (P c)) c) (c + 1)) {h : Nat} :
    ∀ k l c (s : Array α × Array Nat × Array Nat × σ), l + k ≤ ng → h < c →
      Co1BfsMatch enc P PAR LAB SeenOK c s → Co1BfsTree F P PAR LAB ng c →
      bfsRowK F P PAR LAB W ng h k l c ≠ 0 → bfsRowK F P PAR LAB W ng h k l c ≤ N →
      Co1BfsMatch enc P PAR LAB SeenOK (bfsRowK F P PAR LAB W ng h k l c)
          ((List.range' l k).foldl (co1BfsIStep stp mem ins h) s) ∧
        Co1BfsTree F P PAR LAB ng (bfsRowK F P PAR LAB W ng h k l c) := by
  intro k
  induction k with
  | zero =>
    intro l c s _ _ hs ht _ _
    exact ⟨hs, ht⟩
  | succ k ih =>
    intro l c s hlk hhc hs ht hne hle
    have hmono := co1Bfs_bfsRowK_mono (F := F) (P := P) (PAR := PAR) (LAB := LAB) (W := W)
      (ng := ng) h (k + 1) l c hne
    rw [List.range'_succ, List.foldl_cons]
    have hy : stp s.1[h]! l = enc (F (P h) l) := by
      rw [hs.pts h hhc, hstp _ _ (by omega)]
    rw [co1Bfs_bfsRowK_succ] at hne hle hmono ⊢
    unfold co1BfsIStep
    rw [hy]
    by_cases hw : W (h * ng + l) < c
    · rw [if_pos hw] at hne hle hmono ⊢
      by_cases hp : P (W (h * ng + l)) = F (P h) l
      · rw [if_pos hp] at hne hle hmono ⊢
        have hcN : c ≤ N := Nat.le_trans hmono hle
        rw [← hp, hmem _ _ _ hs.seen hcN (by omega), decide_eq_true hw]
        exact ih (l + 1) c s (by omega) hhc hs ht hne hle
      · rw [if_neg hp] at hne
        exact absurd rfl hne
    · rw [if_neg hw] at hne hle hmono ⊢
      by_cases hn : W (h * ng + l) = c ∧ P c = F (P h) l ∧ PAR c = h ∧ LAB c = l
      · rw [if_pos hn] at hne hle hmono ⊢
        obtain ⟨hwc, hpc, hpar, hlab⟩ := hn
        have hcN : c < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
          (Nat.le_trans (co1Bfs_bfsRowK_mono h k (l + 1) (c + 1) hne) hle)
        rw [← hpc, hmem _ _ _ hs.seen (by omega) hcN, decide_eq_false (Nat.lt_irrefl c)]
        simp only [Bool.not_false, ↓reduceIte]
        refine ih (l + 1) (c + 1) _ (by omega) (by omega)
          (co1Bfs_push_match hs hpar hlab (hins _ _ hs.seen hcN)) (fun i h0 hi => ?_) hne hle
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ht i h0 hi
        · exact ⟨by omega, by omega, by rw [hpar, hlab, hpc]⟩
      · rw [if_neg hn] at hne
        exact absurd rfl hne

private theorem co1Bfs_run (hstp : ∀ x l, l < ng → stp (enc x) l = enc (F x l))
    (hmem : ∀ t c w, SeenOK t c → c ≤ N → w < N → mem t (enc (P w)) = decide (w < c))
    (hins : ∀ t c, SeenOK t c → c < N → SeenOK (ins t (enc (P c)) c) (c + 1)) {cap : Nat}
    (hN : 0 < N) :
    ∀ fuel h c (s : Array α × Array Nat × Array Nat × σ),
      Co1BfsMatch enc P PAR LAB SeenOK c s → Co1BfsTree F P PAR LAB ng c →
      bfsRunK F P PAR LAB W ng cap fuel h c = N →
      Co1BfsMatch enc P PAR LAB SeenOK N
          ((fun r : Array α × Array Nat × Array Nat × σ × Nat => (r.1, r.2.1, r.2.2.1, r.2.2.2.1))
            (co1BfsRun stp mem ins ng cap (s.1, s.2.1, s.2.2.1, s.2.2.2, h))) ∧
        Co1BfsTree F P PAR LAB ng N := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s _ _ hr
    rw [co1Bfs_bfsRunK_zero] at hr
    omega
  | succ fuel ih =>
    intro h c s hs ht hr
    have hmono := co1Bfs_bfsRunK_mono (F := F) (P := P) (PAR := PAR) (LAB := LAB) (W := W)
      (ng := ng) cap (fuel + 1) h c (by omega)
    rw [co1BfsRun_unfold, hs.size]
    rw [co1Bfs_bfsRunK_succ] at hr hmono
    by_cases hc : h < c ∧ c < cap
    · rw [if_pos hc] at hr hmono
      rw [if_pos hc]
      by_cases h0 : bfsRowK F P PAR LAB W ng h ng 0 c = 0
      · rw [if_pos h0] at hr; omega
      · rw [if_neg h0] at hr hmono
        have hle : bfsRowK F P PAR LAB W ng h ng 0 c ≤ N :=
          hr ▸ co1Bfs_bfsRunK_mono cap fuel (h + 1) _ (by omega)
        obtain ⟨hs', ht'⟩ := co1Bfs_row (stp := stp) (mem := mem) (ins := ins) (W := W) hstp hmem
          hins ng 0 c s (by omega) hc.1 hs ht h0 hle
        exact ih (h + 1) _ _ hs' ht' hr
    · rw [if_neg hc] at hr
      rw [if_neg hc]
      subst hr
      exact ⟨hs, ht⟩

private theorem co1Bfs_eq_ofFn {β : Type} [Inhabited β] (a : Array β) (f : Nat → β) (N : Nat)
    (hs : a.size = N) (h : ∀ i < N, a[i]! = f i) : a = Array.ofFn (n := N) fun i => f i.val := by
  apply Array.ext
  · rw [hs, Array.size_ofFn]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← h i (by omega), getElem!_pos a i h1]

private theorem co1Bfs_replay (hstp : ∀ x l, l < ng → stp (enc x) l = enc (F x l))
    (hmem : ∀ t c w, SeenOK t c → c ≤ N → w < N → mem t (enc (P w)) = decide (w < c))
    (hins : ∀ t c, SeenOK t c → c < N → SeenOK (ins t (enc (P c)) c) (c + 1)) {cap : Nat}
    {σ0 : σ} (hσ0 : SeenOK σ0 1) (hpar0 : PAR 0 = 0) (hlab0 : LAB 0 = 0) (hN : 0 < N)
    (hr : bfsRunK F P PAR LAB W ng cap (N + 1) 0 1 = N) :
    (co1BfsRun stp mem ins ng cap (#[enc (P 0)], #[0], #[0], σ0, 0)).1 =
        (Array.ofFn (n := N) fun i => enc (P i.val)) ∧
      (co1BfsRun stp mem ins ng cap (#[enc (P 0)], #[0], #[0], σ0, 0)).2.1 =
        (Array.ofFn (n := N) fun i => PAR i.val) ∧
      (co1BfsRun stp mem ins ng cap (#[enc (P 0)], #[0], #[0], σ0, 0)).2.2.1 =
        (Array.ofFn (n := N) fun i => LAB i.val) ∧
      Co1BfsTree F P PAR LAB ng N := by
  have hs : Co1BfsMatch enc P PAR LAB SeenOK 1 (#[enc (P 0)], #[0], #[0], σ0) := by
    refine ⟨rfl, fun i hi => ?_, rfl, fun i hi => ?_, rfl, fun i hi => ?_, hσ0⟩ <;>
      obtain rfl : i = 0 := by omega
    · rfl
    · exact hpar0.symm
    · exact hlab0.symm
  obtain ⟨hm, ht⟩ := co1Bfs_run (stp := stp) (mem := mem) (ins := ins) (W := W) hstp hmem hins hN
    (N + 1) 0 1 _ hs (fun i h0 hi => absurd hi (by omega)) hr
  exact ⟨co1Bfs_eq_ofFn _ _ N hm.size hm.pts, co1Bfs_eq_ofFn _ _ N hm.psize hm.par,
    co1Bfs_eq_ofFn _ _ N hm.lsize hm.lab, ht⟩

end Replay

private theorem co1Bfs_foldr_rowV (X : Nat) : ∀ m j : Nat,
    ((List.range' j m).map (MatL.rowV X)).foldr (fun r acc => r + 16777216 * acc) 0 =
      X / 2 ^ (24 * j) % 2 ^ (24 * m)
  | 0, j => by simp only [List.range'_zero, List.map_nil, List.foldr_nil, Nat.mul_zero,
      Nat.pow_zero, Nat.mod_one]
  | m + 1, j => by
    rw [List.range'_succ, List.map_cons, List.foldr_cons, co1Bfs_foldr_rowV X m (j + 1)]
    unfold MatL.rowV
    have e1 : 2 ^ (24 * (j + 1)) = 2 ^ (24 * j) * 2 ^ 24 := by
      rw [← Nat.pow_add, Nat.mul_succ]
    have e2 : 2 ^ (24 * (m + 1)) = 2 ^ 24 * 2 ^ (24 * m) := by
      rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
    rw [e1, e2, ← Nat.div_div_eq_div_mul, Nat.mod_mul]
    rfl

private theorem co1Bfs_unpack_toList (X : Nat) :
    (unpack 24 24 X).toList = (List.range' 0 24).map (MatL.rowV X) := by
  apply List.ext_getElem
  · simp [MatL.unpack_size]
  · intro i h1 h2
    rw [Array.getElem_toList, MatL.unpack_getElem, List.getElem_map, List.getElem_range']
    simp

private theorem co1Bfs_rowsKey_unpack {X : Nat} (hX : X < 2 ^ 576) : rowsKey (unpack 24 24 X) = X := by
  unfold rowsKey
  rw [co1Bfs_unpack_toList, co1Bfs_foldr_rowV]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt hX

private theorem co1Bfs_unpack_inj {X Y : Nat} (hX : X < 2 ^ 576) (hY : Y < 2 ^ 576)
    (h : unpack 24 24 X = unpack 24 24 Y) : X = Y := by
  rw [← co1Bfs_rowsKey_unpack hX, ← co1Bfs_rowsKey_unpack hY, h]

private theorem co1Bfs_validRows_unpack (X : Nat) : validRows (unpack 24 24 X) = true := by
  simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨MatL.unpack_size X, fun i hi => ?_⟩
  rw [MatL.unpack_getElem]
  exact (MatL.rowV_lt X i).trans_eq (by norm_num)

private theorem co1Bfs_gensArr_get {ng : Nat} {GM : Nat → Nat} {l : Nat} (hl : l < ng) :
    (gensArr ng GM)[l]! = unpack 24 24 (GM l) := by
  rw [getElem!_pos (gensArr ng GM) l (by simp [gensArr, hl])]
  simp [gensArr]

private theorem co1Bfs_allIn_eq_true {lo hi : Nat} {p : Nat → Bool} :
    CFSG.Sporadic.Th.Native.allIn lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  unfold CFSG.Sporadic.Th.Native.allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hlo hhi
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' hlo] using this
  · rintro h ⟨k, hk⟩ _
    exact h (lo + k) (by omega) (by omega)

private theorem co1Bfs_strictInc {L : List Nat} (hs : L.Pairwise (fun a b => keyLe a b = true))
    (hn : L.Nodup) : strictInc L = true := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t =>
      have hab : keyLe a b = true := List.rel_of_pairwise_cons hs List.mem_cons_self
      have hne : a ≠ b := fun e => (List.nodup_cons.1 hn).1 (e ▸ List.mem_cons_self)
      simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ih (List.Pairwise.of_cons hs) (List.Nodup.of_cons hn)⟩
      simp only [keyLe, decide_eq_true_eq] at hab
      omega

private theorem co1Bfs_distinctKeys {N : Nat} {P : Nat → Nat} (hP : ∀ i < N, P i < 2 ^ 576)
    (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) :
    distinctKeys ((Array.ofFn (n := N) fun i => unpack 24 24 (P i.val)).toList.map rowsKey) =
      true := by
  unfold distinctKeys
  rw [Array.toList_ofFn, List.map_ofFn]
  have hnd : (List.ofFn (rowsKey ∘ fun i : Fin N => unpack 24 24 (P i.val))).Nodup := by
    rw [List.nodup_ofFn]
    intro a b e
    simp only [Function.comp_apply, co1Bfs_rowsKey_unpack (hP _ a.2),
      co1Bfs_rowsKey_unpack (hP _ b.2)] at e
    exact Fin.ext (hinj _ a.2 _ b.2 e)
  apply co1Bfs_strictInc
  · apply List.pairwise_mergeSort
    · intro a b c h1 h2
      simp only [keyLe, decide_eq_true_eq] at h1 h2 ⊢
      omega
    · intro a b
      simp only [keyLe, Bool.or_eq_true, decide_eq_true_eq]
      omega
  · exact (List.mergeSort_perm _ _).nodup_iff.2 hnd

private theorem co1Bfs_bfsK_sound {F : Nat → Nat → Nat} {P PAR LAB W S : Nat → Nat} {ng cap N R : Nat}
    (h : bfsK F P PAR LAB W S ng cap N R = true) :
    0 < N ∧ P 0 = R ∧ PAR 0 = 0 ∧ LAB 0 = 0 ∧ bfsDistK P S N = true ∧
      bfsRunK F P PAR LAB W ng cap (N + 1) 0 1 = N := by
  unfold bfsK at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

private theorem co1Bfs_strict {P S : Nat → Nat} {N : Nat}
    (h : ∀ k, k + 1 < N → P (S k) < P (S (k + 1))) : ∀ a b, a < b → b < N → P (S a) < P (S b) := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
    · exact Nat.lt_trans (ih hab (by omega)) (h b hb)
    · exact h a hb

private theorem co1Bfs_bfsDistK_sound {P S : Nat → Nat} {N : Nat} (h : bfsDistK P S N = true) :
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
  have hst := co1Bfs_strict (P := P) (S := S) (N := N) fun k hk =>
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

private theorem gtBFS_eq_co1BfsRun (G : Array (Array Nat)) (cap : Nat) :
    gtBFS G cap = (fun s : Array (Array Nat) × Array Nat × Array Nat × Std.HashSet (Array Nat) × Nat =>
      (⟨s.1, s.2.1, s.2.2.1⟩ : GTree))
      (co1BfsRun (fun x l => mulRows 24 x G[l]!) (fun s y => s.contains y) (fun s y _ => s.insert y)
        G.size cap (#[idRows 24], #[0], #[0], (∅ : Std.HashSet (Array Nat)).insert (idRows 24), 0)) := by
  rfl

private theorem conjBFS_eq_co1BfsRun (G Gi : Array (Array Nat)) (root : Array Nat) (cap : Nat) :
    conjBFS G Gi root cap = (fun s : Array (Array Nat) × Array Nat × Array Nat × Std.HashMap Nat Nat × Nat =>
      (⟨s.1, s.2.1, s.2.2.1⟩ : ConjCert))
      (co1BfsRun (fun x l => conjRows G[l]! Gi[l]! x) (fun s y => s.contains (rowsKey y))
        (fun s y n => s.insert (rowsKey y) n)
        G.size cap (#[root], #[0], #[0], (∅ : Std.HashMap Nat Nat).insert (rowsKey root) 0, 0)) := by
  unfold conjBFS co1BfsRun co1BfsOuter co1BfsInner
  simp only [Id.run]
  rfl

private theorem co1Bfs_bfsTree_pts {N : Nat} {P PAR LAB : Nat → Nat} {i : Nat} (hi : i < N) :
    (bfsTree N P PAR LAB).pts[i]! = unpack 24 24 (P i) := by
  rw [getElem!_pos _ i (by simp [bfsTree, hi])]
  simp [bfsTree]

private theorem co1Bfs_bfsTree_par {N : Nat} {P PAR LAB : Nat → Nat} {i : Nat} (hi : i < N) :
    (bfsTree N P PAR LAB).par[i]! = PAR i := by
  rw [getElem!_pos _ i (by simp [bfsTree, hi])]
  simp [bfsTree]

private theorem co1Bfs_bfsTree_lab {N : Nat} {P PAR LAB : Nat → Nat} {i : Nat} (hi : i < N) :
    (bfsTree N P PAR LAB).lab[i]! = LAB i := by
  rw [getElem!_pos _ i (by simp [bfsTree, hi])]
  simp [bfsTree]

private theorem co1Bfs_gtClosK_sound {GM P W : Nat → Nat} {ng N : Nat} (h : gtClosK GM P W ng N = true) :
    ∀ i < N, ∀ l < ng, W (i * ng + l) < N ∧ P (W (i * ng + l)) = gtStepK GM (P i) l := by
  intro i hi l hl
  unfold gtClosK at h
  have h1 := MatL.allN_iff.1 (MatL.allN_iff.1 h i hi) l hl
  simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
  exact h1

private def co1BfsSeenSet (P : Nat → Nat) (t : Std.HashSet (Array Nat)) (c : Nat) : Prop :=
  ∀ y, t.contains y = true ↔ ∃ i < c, unpack 24 24 (P i) = y

private theorem co1Bfs_seenSet_mem {P : Nat → Nat} {N : Nat} (hP : ∀ i < N, P i < 2 ^ 576)
    (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) (t : Std.HashSet (Array Nat)) (c w : Nat)
    (ht : co1BfsSeenSet P t c) (hc : c ≤ N) (hw : w < N) :
    t.contains (unpack 24 24 (P w)) = decide (w < c) := by
  apply Bool.eq_iff_iff.2
  rw [ht, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    have := hinj i (by omega) w hw (co1Bfs_unpack_inj (hP i (by omega)) (hP w hw) e)
    omega
  · intro hwc
    exact ⟨w, hwc, rfl⟩

private theorem co1Bfs_seenSet_ins {P : Nat → Nat} (t : Std.HashSet (Array Nat)) (c : Nat)
    (ht : co1BfsSeenSet P t c) : co1BfsSeenSet P (t.insert (unpack 24 24 (P c))) (c + 1) := by
  intro y
  rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, ht]
  constructor
  · rintro (e | ⟨i, hi, e⟩)
    · exact ⟨c, Nat.lt_succ_self c, e⟩
    · exact ⟨i, by omega, e⟩
  · rintro ⟨i, hi, e⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact Or.inr ⟨i, hi, e⟩
    · exact Or.inl e

private theorem co1Bfs_gensArr_size (ng : Nat) (GM : Nat → Nat) : (gensArr ng GM).size = ng := by
  simp [gensArr]

theorem gtBFS_of_K {GM : Nat → Nat} {ng cap N : Nat} {P PAR LAB W S : Nat → Nat}
    (h : gtPinK GM ng cap N P PAR LAB W S = true) :
    gtBFS (gensArr ng GM) cap = bfsTree N P PAR LAB ∧
      gtOK (gensArr ng GM) (bfsTree N P PAR LAB) = true := by
  unfold gtPinK at h
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hb, hcl⟩ := h
  obtain ⟨hN, hP0, hpar0, hlab0, hd, hr⟩ := co1Bfs_bfsK_sound hb
  obtain ⟨hP, hinj⟩ := co1Bfs_bfsDistK_sound hd
  have hcl' := co1Bfs_gtClosK_sound hcl
  have hroot : idRows 24 = unpack 24 24 (P 0) := by rw [hP0, MatL.unpack_idM]; rfl
  have hσ0 : co1BfsSeenSet P ((∅ : Std.HashSet (Array Nat)).insert (unpack 24 24 (P 0))) 1 := by
    have h0 : co1BfsSeenSet P (∅ : Std.HashSet (Array Nat)) 0 := fun y => by
      simp only [Std.HashSet.contains_empty, Bool.false_eq_true, false_iff]
      rintro ⟨i, hi, -⟩
      omega
    exact co1Bfs_seenSet_ins _ 0 h0
  have hstp : ∀ x l, l < ng → mulRows 24 (unpack 24 24 x) (gensArr ng GM)[l]! =
      unpack 24 24 (gtStepK GM x l) := by
    intro x l hl
    rw [co1Bfs_gensArr_get hl]
    exact mul_unpackW x (GM l)
  obtain ⟨e1, e2, e3, ht⟩ := co1Bfs_replay (stp := fun x l => mulRows 24 x (gensArr ng GM)[l]!)
    (mem := fun t y => t.contains y) (ins := fun t y _ => t.insert y) (enc := unpack 24 24)
    (SeenOK := co1BfsSeenSet P) (W := W) (cap := cap) hstp
    (co1Bfs_seenSet_mem hP hinj) (fun t c ht _ => co1Bfs_seenSet_ins t c ht) hσ0 hpar0 hlab0 hN hr
  have hT : gtBFS (gensArr ng GM) cap = bfsTree N P PAR LAB := by
    rw [gtBFS_eq_co1BfsRun, co1Bfs_gensArr_size, hroot]
    dsimp only
    rw [e1, e2, e3]
    rfl
  refine ⟨hT, ?_⟩
  have hsz : (bfsTree N P PAR LAB).pts.size = N := by simp [bfsTree]
  simp only [gtOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hsz]
  refine ⟨⟨⟨⟨⟨hN, (by simp [bfsTree])⟩, (by simp [bfsTree])⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [co1Bfs_allIn_eq_true]
    intro i _ hi
    unfold gtPointOK
    rw [co1Bfs_bfsTree_pts hi, co1Bfs_validRows_unpack, Bool.true_and]
    by_cases hi0 : i = 0
    · subst hi0
      rw [← hroot]
      simp
    · obtain ⟨h1, h2, h3⟩ := ht i (by omega) hi
      have hne : (i == 0) = false := by simpa using hi0
      rw [hne, if_neg (by simp), co1Bfs_bfsTree_par hi, co1Bfs_bfsTree_lab hi,
        co1Bfs_bfsTree_pts (by omega), co1Bfs_gensArr_size, hstp _ _ h2, ← h3]
      simp [h1, h2]
  · exact co1Bfs_distinctKeys hP hinj
  · unfold gtClosed
    rw [co1Bfs_allIn_eq_true]
    intro i _ hi
    rw [co1Bfs_allIn_eq_true]
    intro l _ hl
    rw [hsz] at hi
    rw [co1Bfs_gensArr_size] at hl
    obtain ⟨hw, hpw⟩ := hcl' i hi l hl
    rw [Std.HashSet.contains_ofList, Array.contains_toList, co1Bfs_bfsTree_pts hi, hstp _ _ hl]
    exact contains_bfsTree hw (by rw [hpw])

private def co1BfsSeenMap (P : Nat → Nat) (t : Std.HashMap Nat Nat) (c : Nat) : Prop :=
  ∀ k, t.contains k = true ↔ ∃ i < c, P i = k

private theorem co1Bfs_seenMap_ins {P : Nat → Nat} (t : Std.HashMap Nat Nat) (c n : Nat)
    (ht : co1BfsSeenMap P t c) : co1BfsSeenMap P (t.insert (P c) n) (c + 1) := by
  intro y
  rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, ht]
  constructor
  · rintro (e | ⟨i, hi, e⟩)
    · exact ⟨c, Nat.lt_succ_self c, e⟩
    · exact ⟨i, by omega, e⟩
  · rintro ⟨i, hi, e⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact Or.inr ⟨i, hi, e⟩
    · exact Or.inl e

private theorem co1Bfs_seenMap_mem {P : Nat → Nat} {N : Nat} (hP : ∀ i < N, P i < 2 ^ 576)
    (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) (t : Std.HashMap Nat Nat) (c w : Nat)
    (ht : co1BfsSeenMap P t c) (hc : c ≤ N) (hw : w < N) :
    t.contains (rowsKey (unpack 24 24 (P w))) = decide (w < c) := by
  rw [co1Bfs_rowsKey_unpack (hP w hw)]
  apply Bool.eq_iff_iff.2
  rw [ht, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    have := hinj i (by omega) w hw e
    omega
  · intro hwc
    exact ⟨w, hwc, rfl⟩

theorem conjAtLeast_of_K {GM GIM : Nat → Nat} {ng cap N R : Nat} {P PAR LAB W S : Nat → Nat}
    (h : ctPinK GM GIM R ng cap N P PAR LAB W S = true) :
    conjAtLeast (gensArr ng GM) (gensArr ng GIM) (unpack 24 24 R) cap = true := by
  unfold ctPinK at h
  rw [MatL.bAnd_eq, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨hcap, hb⟩ := h
  obtain ⟨hN, hP0, hpar0, hlab0, hd, hr⟩ := co1Bfs_bfsK_sound hb
  obtain ⟨hP, hinj⟩ := co1Bfs_bfsDistK_sound hd
  have hroot : unpack 24 24 R = unpack 24 24 (P 0) := by rw [hP0]
  have hσ0 : co1BfsSeenMap P ((∅ : Std.HashMap Nat Nat).insert (rowsKey (unpack 24 24 (P 0))) 0)
      1 := by
    have h0 : co1BfsSeenMap P (∅ : Std.HashMap Nat Nat) 0 := fun y => by
      simp only [Std.HashMap.contains_empty, Bool.false_eq_true, false_iff]
      rintro ⟨i, hi, -⟩
      omega
    rw [co1Bfs_rowsKey_unpack (hP 0 hN)]
    exact co1Bfs_seenMap_ins _ 0 0 h0
  have hstp : ∀ x l, l < ng →
      conjRows (gensArr ng GM)[l]! (gensArr ng GIM)[l]! (unpack 24 24 x) =
        unpack 24 24 (ctStepK GM GIM x l) := by
    intro x l hl
    rw [co1Bfs_gensArr_get hl, co1Bfs_gensArr_get hl]
    unfold conjRows ctStepK
    rw [← mul_unpackW, ← mul_unpackW]
    rfl
  obtain ⟨e1, e2, e3, ht⟩ := co1Bfs_replay
    (stp := fun x l => conjRows (gensArr ng GM)[l]! (gensArr ng GIM)[l]! x)
    (mem := fun t y => t.contains (rowsKey y)) (ins := fun t y n => t.insert (rowsKey y) n)
    (enc := unpack 24 24) (SeenOK := co1BfsSeenMap P) (W := W) (cap := cap) hstp
    (co1Bfs_seenMap_mem hP hinj)
    (fun t c ht hc => by
      rw [co1Bfs_rowsKey_unpack (hP c hc)]
      exact co1Bfs_seenMap_ins t c c ht) hσ0 hpar0 hlab0 hN hr
  have hC : conjBFS (gensArr ng GM) (gensArr ng GIM) (unpack 24 24 R) cap =
      ⟨(bfsTree N P PAR LAB).pts, (bfsTree N P PAR LAB).par, (bfsTree N P PAR LAB).lab⟩ := by
    rw [conjBFS_eq_co1BfsRun, co1Bfs_gensArr_size, hroot]
    dsimp only
    rw [e1, e2, e3]
    rfl
  have hsz : (bfsTree N P PAR LAB).pts.size = N := by simp [bfsTree]
  unfold conjAtLeast
  dsimp only
  rw [hC]
  simp only [ctOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hsz]
  refine ⟨⟨⟨⟨hN, ?_⟩, ?_⟩, co1Bfs_distinctKeys hP hinj⟩, hcap⟩
  · rw [co1Bfs_bfsTree_pts hN, hroot]
  · rw [co1Bfs_allIn_eq_true]
    intro i _ hi
    unfold ctPointOK
    dsimp only
    rw [co1Bfs_bfsTree_pts hi, co1Bfs_validRows_unpack, Bool.true_and]
    by_cases hi0 : i = 0
    · subst hi0
      simp
    · obtain ⟨h1, h2, h3⟩ := ht i (by omega) hi
      have hne : (i == 0) = false := by simpa using hi0
      rw [hne, Bool.false_or, co1Bfs_bfsTree_par hi, co1Bfs_bfsTree_lab hi,
        co1Bfs_bfsTree_pts (by omega), co1Bfs_gensArr_size, hstp _ _ h2, ← h3]
      simp [h1, h2]

end Replays

end CFSG.KS.SporSch.M24

end
