module

public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Sporadic.Co1I301.Inputs

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KS.Raw CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.SmallF2.Native CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Co1Block.Native

section Gen

variable {α σ : Type} [Inhabited α]

private def ctrIStep (stp : α → Nat → α) (mem : σ → α → Bool) (ins : σ → α → σ) (h : Nat) (x : α)
    (s : Array α × σ × Array Nat × Array Nat) (l : Nat) : Array α × σ × Array Nat × Array Nat :=
  if (!mem s.2.1 (stp x l)) = true then
    (s.1.push (stp x l), ins s.2.1 (stp x l), s.2.2.1.push h, s.2.2.2.push l)
  else s

private def ctrHead (stp : α → Nat → α) (mem : σ → α → Bool) (ins : σ → α → σ) (ng : Nat)
    (s : Array α × σ × Array Nat × Array Nat) (i : Nat) : Array α × σ × Array Nat × Array Nat :=
  if hi : i < s.1.size then (List.range' 0 ng).foldl (ctrIStep stp mem ins i s.1[i]) s else s

private theorem ctr_forIn_yield {β : Type} (g : β → Nat → β) (f : Nat → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g b a)) :
    ∀ (l : List Nat) (init : β), forIn (m := Id) l init f = l.foldl g init
  | [], _ => rfl
  | a :: l, init => by
    rw [List.forIn_cons, hf]
    exact ctr_forIn_yield g f hf l (g init a)

private theorem ctr_range_forIn {β : Type} (g : β → Nat → β) (f : Nat → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g b a)) (n : Nat) (init : β) :
    forIn (m := Id) [:n] init f = (List.range' 0 n).foldl g init := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  exact ctr_forIn_yield g f hf _ init

end Gen

private theorem ctr_conjTree_eq (G Gi : Array CFSG.Sporadic.Co1Schreier.Native.Rows)
    (root : CFSG.Sporadic.Co1Schreier.Native.Rows) (cap : Nat) :
    CFSG.Sporadic.Co1I301.Native.conjTree G Gi root cap =
      (fun s : Array CFSG.Sporadic.Co1Schreier.Native.Rows × Std.HashSet (Array Nat) × Array Nat ×
          Array Nat => (s.2.2.1, s.2.2.2))
        ((List.range' 0 cap).foldl
          (ctrHead (fun x l => CFSG.Sporadic.Co1Schreier.Native.mul
            (CFSG.Sporadic.Co1Schreier.Native.mul G[l]! x) Gi[l]!) (fun t y => t.contains y)
            (fun t y => t.insert y) G.size)
          (#[root], (∅ : Std.HashSet (Array Nat)).insert root, #[0], #[0])) := by
  unfold CFSG.Sporadic.Co1I301.Native.conjTree
  dsimp only [Id.run]
  rw [ctr_range_forIn (ctrHead (fun x l => CFSG.Sporadic.Co1Schreier.Native.mul
    (CFSG.Sporadic.Co1Schreier.Native.mul G[l]! x) Gi[l]!) (fun t y => t.contains y)
    (fun t y => t.insert y) G.size)]
  · rfl
  · intro i s
    unfold ctrHead
    by_cases hi : i < s.1.size
    · rw [dif_pos hi, dif_pos hi, ctr_range_forIn (ctrIStep (fun x l =>
        CFSG.Sporadic.Co1Schreier.Native.mul (CFSG.Sporadic.Co1Schreier.Native.mul G[l]! x) Gi[l]!)
        (fun t y => t.contains y) (fun t y => t.insert y) i s.1[i])]
      · rfl
      · intro l t
        unfold ctrIStep
        dsimp only
        split <;> rfl
    · rw [dif_neg hi, dif_neg hi]
      rfl

section Kernel

variable {F : Nat → Nat → Nat} {P PAR LAB W : Nat → Nat} {ng : Nat}

private theorem ctr_bfsRowK_succ (h k l c : Nat) :
    bfsRowK F P PAR LAB W ng h (k + 1) l c =
      if W (h * ng + l) < c then
        (if P (W (h * ng + l)) = F (P h) l then bfsRowK F P PAR LAB W ng h k (l + 1) c else 0)
      else if W (h * ng + l) = c ∧ P c = F (P h) l ∧ PAR c = h ∧ LAB c = l then
        bfsRowK F P PAR LAB W ng h k (l + 1) (c + 1)
      else 0 := by
  change strictN (W (Nat.add (Nat.mul h ng) l)) (fun w => strictN (F (P h) l) fun y =>
      nIf(Nat.blt w c, nIf(Nat.beq (P w) y, bfsRowK F P PAR LAB W ng h k (Nat.succ l) c, nat_lit 0),
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (P c) y, bAnd(Nat.beq (PAR c) h, Nat.beq (LAB c) l))),
          bfsRowK F P PAR LAB W ng h k (Nat.succ l) (Nat.succ c), nat_lit 0))) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]
  rfl

private theorem ctr_bfsRowK_mono (h : Nat) :
    ∀ k l c, bfsRowK F P PAR LAB W ng h k l c ≠ 0 → c ≤ bfsRowK F P PAR LAB W ng h k l c := by
  intro k
  induction k with
  | zero => intro l c _; exact Nat.le_refl c
  | succ k ih =>
    intro l c hne
    rw [ctr_bfsRowK_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact ih _ _ hne
      · exact absurd rfl hne
    · rw [if_neg ‹_›]
      split at hne
      · rw [if_pos ‹_›]; exact Nat.le_of_succ_le (ih _ _ hne)
      · exact absurd rfl hne

private theorem ctr_bfsRunK_zero (cap h c : Nat) : bfsRunK F P PAR LAB W ng cap 0 h c = 0 := rfl

private theorem ctr_bfsRunK_succ (cap fuel h c : Nat) :
    bfsRunK F P PAR LAB W ng cap (fuel + 1) h c =
      if h < c ∧ c < cap then
        (if bfsRowK F P PAR LAB W ng h ng 0 c = 0 then 0
         else bfsRunK F P PAR LAB W ng cap fuel (h + 1) (bfsRowK F P PAR LAB W ng h ng 0 c))
      else c := by
  change nIf(bAnd(Nat.blt h c, Nat.blt c cap),
      strictN (bfsRowK F P PAR LAB W ng h ng (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, bfsRunK F P PAR LAB W ng cap fuel (Nat.succ h) c'), c) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]

private theorem ctr_bfsRunK_mono (cap : Nat) :
    ∀ fuel h c, bfsRunK F P PAR LAB W ng cap fuel h c ≠ 0 →
      c ≤ bfsRunK F P PAR LAB W ng cap fuel h c := by
  intro fuel
  induction fuel with
  | zero => intro h c hne; exact absurd rfl hne
  | succ fuel ih =>
    intro h c hne
    rw [ctr_bfsRunK_succ] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      split at hne
      · exact absurd rfl hne
      · rw [if_neg ‹_›]
        exact Nat.le_trans (ctr_bfsRowK_mono h ng 0 c ‹_›) (Nat.le_of_lt_succ
          (Nat.lt_succ_of_le (ih _ _ hne)))
    · rw [if_neg ‹_›]

end Kernel

section Replay

variable {α σ : Type} [Inhabited α]

private structure CtrMatch (enc : Nat → α) (P PAR LAB : Nat → Nat) (SeenOK : σ → Nat → Prop)
    (c : Nat) (s : Array α × σ × Array Nat × Array Nat) : Prop where
  size : s.1.size = c
  pts : ∀ i < c, s.1[i]! = enc (P i)
  seen : SeenOK s.2.1 c
  psize : s.2.2.1.size = c
  par : ∀ i < c, s.2.2.1[i]! = PAR i
  lsize : s.2.2.2.size = c
  lab : ∀ i < c, s.2.2.2[i]! = LAB i

private theorem ctr_push_lt {β : Type} [Inhabited β] (a : Array β) (x : β) {j : Nat}
    (h : j < a.size) : (a.push x)[j]! = a[j]! := by
  rw [getElem!_pos (a.push x) j (by rw [Array.size_push]; omega), getElem!_pos a j h,
    Array.getElem_push_lt h]

private theorem ctr_push_size {β : Type} [Inhabited β] (a : Array β) (x : β) :
    (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

variable {stp : α → Nat → α} {mem : σ → α → Bool} {ins : σ → α → σ} {enc : Nat → α}
  {SeenOK : σ → Nat → Prop} {F : Nat → Nat → Nat} {P PAR LAB W : Nat → Nat} {ng N : Nat}

private theorem ctr_push_match {c : Nat} {s : Array α × σ × Array Nat × Array Nat}
    (hs : CtrMatch enc P PAR LAB SeenOK c s) {h l : Nat} (hh : PAR c = h) (hl : LAB c = l)
    (hσ : SeenOK (ins s.2.1 (enc (P c))) (c + 1)) :
    CtrMatch enc P PAR LAB SeenOK (c + 1)
      (s.1.push (enc (P c)), ins s.2.1 (enc (P c)), s.2.2.1.push h, s.2.2.2.push l) := by
  obtain ⟨hsz, hpts, -, hpsz, hpar, hlsz, hlab⟩ := hs
  refine ⟨by simp [hsz], fun i hi => ?_, hσ, by simp [hpsz], fun i hi => ?_, by simp [hlsz],
    fun i hi => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [ctr_push_lt _ _ (by omega)]; exact hpts i hi
    · rw [← hsz, ctr_push_size, hsz]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [ctr_push_lt _ _ (by omega)]; exact hpar i hi
    · rw [← hpsz, ctr_push_size, hpsz, hh]
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [ctr_push_lt _ _ (by omega)]; exact hlab i hi
    · rw [← hlsz, ctr_push_size, hlsz, hl]

private theorem ctr_row (hstp : ∀ x l, l < ng → stp (enc x) l = enc (F x l))
    (hmem : ∀ t c w, SeenOK t c → c ≤ N → w < N → mem t (enc (P w)) = decide (w < c))
    (hins : ∀ t c, SeenOK t c → c < N → SeenOK (ins t (enc (P c))) (c + 1)) {h : Nat} :
    ∀ k l c (s : Array α × σ × Array Nat × Array Nat), l + k ≤ ng → h < c →
      CtrMatch enc P PAR LAB SeenOK c s →
      bfsRowK F P PAR LAB W ng h k l c ≠ 0 → bfsRowK F P PAR LAB W ng h k l c ≤ N →
      CtrMatch enc P PAR LAB SeenOK (bfsRowK F P PAR LAB W ng h k l c)
          ((List.range' l k).foldl (ctrIStep stp mem ins h (enc (P h))) s) := by
  intro k
  induction k with
  | zero =>
    intro l c s _ _ hs _ _
    exact hs
  | succ k ih =>
    intro l c s hlk hhc hs hne hle
    have hmono := ctr_bfsRowK_mono (F := F) (P := P) (PAR := PAR) (LAB := LAB) (W := W)
      (ng := ng) h (k + 1) l c hne
    rw [List.range'_succ, List.foldl_cons]
    rw [ctr_bfsRowK_succ] at hne hle hmono ⊢
    unfold ctrIStep
    rw [hstp _ _ (by omega)]
    by_cases hw : W (h * ng + l) < c
    · rw [if_pos hw] at hne hle hmono ⊢
      by_cases hp : P (W (h * ng + l)) = F (P h) l
      · rw [if_pos hp] at hne hle hmono ⊢
        have hcN : c ≤ N := Nat.le_trans hmono hle
        rw [← hp, hmem _ _ _ hs.seen hcN (by omega), decide_eq_true hw]
        exact ih (l + 1) c s (by omega) hhc hs hne hle
      · rw [if_neg hp] at hne
        exact absurd rfl hne
    · rw [if_neg hw] at hne hle hmono ⊢
      by_cases hn : W (h * ng + l) = c ∧ P c = F (P h) l ∧ PAR c = h ∧ LAB c = l
      · rw [if_pos hn] at hne hle hmono ⊢
        obtain ⟨hwc, hpc, hpar, hlab⟩ := hn
        have hcN : c < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
          (Nat.le_trans (ctr_bfsRowK_mono h k (l + 1) (c + 1) hne) hle)
        rw [← hpc, hmem _ _ _ hs.seen (by omega) hcN, decide_eq_false (Nat.lt_irrefl c)]
        simp only [Bool.not_false, ↓reduceIte]
        exact ih (l + 1) (c + 1) _ (by omega) (by omega)
          (ctr_push_match hs hpar hlab (hins _ _ hs.seen hcN)) hne hle
      · rw [if_neg hn] at hne
        exact absurd rfl hne

private theorem ctr_run (hstp : ∀ x l, l < ng → stp (enc x) l = enc (F x l))
    (hmem : ∀ t c w, SeenOK t c → c ≤ N → w < N → mem t (enc (P w)) = decide (w < c))
    (hins : ∀ t c, SeenOK t c → c < N → SeenOK (ins t (enc (P c))) (c + 1)) (hN : 0 < N) :
    ∀ fuel h c (s : Array α × σ × Array Nat × Array Nat), h ≤ c →
      CtrMatch enc P PAR LAB SeenOK c s →
      bfsRunK F P PAR LAB W ng (N + 1) fuel h c = N →
      CtrMatch enc P PAR LAB SeenOK N
        ((List.range' h (N - h)).foldl (ctrHead stp mem ins ng) s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s _ _ hr
    rw [ctr_bfsRunK_zero] at hr
    omega
  | succ fuel ih =>
    intro h c s hhc hs hr
    rw [ctr_bfsRunK_succ] at hr
    by_cases hc : h < c ∧ c < N + 1
    · rw [if_pos hc] at hr
      by_cases h0 : bfsRowK F P PAR LAB W ng h ng 0 c = 0
      · rw [if_pos h0] at hr; omega
      · rw [if_neg h0] at hr
        have hle : bfsRowK F P PAR LAB W ng h ng 0 c ≤ N :=
          hr ▸ ctr_bfsRunK_mono (N + 1) fuel (h + 1) _ (by omega)
        have hs' := ctr_row (stp := stp) (mem := mem) (ins := ins) (W := W) hstp hmem hins ng 0 c s
          (by omega) hc.1 hs h0 hle
        have hcr := ctr_bfsRowK_mono (F := F) (P := P) (PAR := PAR) (LAB := LAB) (W := W)
          (ng := ng) h ng 0 c h0
        have e : N - h = (N - (h + 1)) + 1 := by omega
        have hlt : h < s.1.size := by rw [hs.size]; exact hc.1
        have hx : ctrHead stp mem ins ng s h =
            (List.range' 0 ng).foldl (ctrIStep stp mem ins h (enc (P h))) s := by
          unfold ctrHead
          rw [dif_pos hlt, ← getElem!_pos s.1 h hlt, hs.pts h hc.1]
        rw [e, List.range'_succ, List.foldl_cons, hx]
        exact ih (h + 1) _ _ (by omega) hs' hr
    · rw [if_neg hc] at hr
      have hhN : h = N := by
        rcases Nat.lt_or_ge h c with h1 | h1
        · exact absurd ⟨h1, by omega⟩ hc
        · omega
      rw [hhN, Nat.sub_self, List.range'_zero, List.foldl_nil, ← hr]
      exact hs

private theorem ctr_eq_ofFn {β : Type} [Inhabited β] (a : Array β) (f : Nat → β) (N : Nat)
    (hs : a.size = N) (h : ∀ i < N, a[i]! = f i) : a = Array.ofFn (n := N) fun i => f i.val := by
  apply Array.ext
  · rw [hs, Array.size_ofFn]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← h i (by omega), getElem!_pos a i h1]

end Replay

private theorem ctr_foldr_rowV (X : Nat) : ∀ m j : Nat,
    ((List.range' j m).map (MatL.rowV X)).foldr (fun r acc => r + 16777216 * acc) 0 =
      X / 2 ^ (24 * j) % 2 ^ (24 * m)
  | 0, j => by simp only [List.range'_zero, List.map_nil, List.foldr_nil, Nat.mul_zero,
      Nat.pow_zero, Nat.mod_one]
  | m + 1, j => by
    rw [List.range'_succ, List.map_cons, List.foldr_cons, ctr_foldr_rowV X m (j + 1)]
    unfold MatL.rowV
    have e1 : 2 ^ (24 * (j + 1)) = 2 ^ (24 * j) * 2 ^ 24 := by
      rw [← Nat.pow_add, Nat.mul_succ]
    have e2 : 2 ^ (24 * (m + 1)) = 2 ^ 24 * 2 ^ (24 * m) := by
      rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
    rw [e1, e2, ← Nat.div_div_eq_div_mul, Nat.mod_mul]
    rfl

private theorem ctr_unpack_toList (X : Nat) :
    (unpack 24 24 X).toList = (List.range' 0 24).map (MatL.rowV X) := by
  apply List.ext_getElem
  · simp [MatL.unpack_size]
  · intro i h1 h2
    rw [Array.getElem_toList, MatL.unpack_getElem, List.getElem_map, List.getElem_range']
    simp

set_option exponentiation.threshold 576 in
private theorem ctr_rowsKey_unpack {X : Nat} (hX : X < 2 ^ 576) :
    rowsKey (unpack 24 24 X) = X := by
  unfold rowsKey
  rw [ctr_unpack_toList, ctr_foldr_rowV]
  rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt hX

private theorem ctr_unpack_inj {X Y : Nat} (hX : X < 2 ^ 576) (hY : Y < 2 ^ 576)
    (h : unpack 24 24 X = unpack 24 24 Y) : X = Y := by
  rw [← ctr_rowsKey_unpack hX, ← ctr_rowsKey_unpack hY, h]

private theorem ctr_gensArr_get {ng : Nat} {GM : Nat → Nat} {l : Nat} (hl : l < ng) :
    (gensArr ng GM)[l]! = unpack 24 24 (GM l) := by
  rw [getElem!_pos (gensArr ng GM) l (by simp [gensArr, hl])]
  simp [gensArr]

private theorem ctr_gensArr_size (ng : Nat) (GM : Nat → Nat) : (gensArr ng GM).size = ng := by
  simp [gensArr]

private theorem ctr_bfsK_sound {F : Nat → Nat → Nat} {P PAR LAB W S : Nat → Nat}
    {ng cap N R : Nat} (h : bfsK F P PAR LAB W S ng cap N R = true) :
    0 < N ∧ P 0 = R ∧ PAR 0 = 0 ∧ LAB 0 = 0 ∧ bfsDistK P S N = true ∧
      bfsRunK F P PAR LAB W ng cap (N + 1) 0 1 = N := by
  unfold bfsK at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

private theorem ctr_strict {P S : Nat → Nat} {N : Nat}
    (h : ∀ k, k + 1 < N → P (S k) < P (S (k + 1))) :
    ∀ a b, a < b → b < N → P (S a) < P (S b) := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
    · exact Nat.lt_trans (ih hab (by omega)) (h b hb)
    · exact h a hb

set_option exponentiation.threshold 576 in
private theorem ctr_bfsDistK_sound {P S : Nat → Nat} {N : Nat} (h : bfsDistK P S N = true) :
    (∀ i < N, P i < 2 ^ 576) ∧ ∀ a < N, ∀ b < N, P a = P b → a = b := by
  unfold bfsDistK at h
  rw [MatL.allN_iff] at h
  have h' : ∀ k < N, S k < N ∧ P k < 2 ^ 576 ∧ (k + 1 = N ∨ P (S k) < P (S (k + 1))) := by
    intro k hk
    have := h k hk
    simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at this
    refine ⟨this.1, ?_, ?_⟩
    · exact (Nat.one_shiftLeft 576) ▸ this.2.1
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
  have hst := ctr_strict (P := P) (S := S) (N := N) fun k hk =>
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

private def CtrSeenSet (P : Nat → Nat) (t : Std.HashSet (Array Nat)) (c : Nat) : Prop :=
  ∀ y, t.contains y = true ↔ ∃ i < c, unpack 24 24 (P i) = y

private theorem ctr_seenSet_mem {P : Nat → Nat} {N : Nat} (hP : ∀ i < N, P i < 2 ^ 576)
    (hinj : ∀ a < N, ∀ b < N, P a = P b → a = b) (t : Std.HashSet (Array Nat)) (c w : Nat)
    (ht : CtrSeenSet P t c) (hc : c ≤ N) (hw : w < N) :
    t.contains (unpack 24 24 (P w)) = decide (w < c) := by
  apply Bool.eq_iff_iff.2
  rw [ht, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    have := hinj i (by omega) w hw (ctr_unpack_inj (hP i (by omega)) (hP w hw) e)
    omega
  · intro hwc
    exact ⟨w, hwc, rfl⟩

private theorem ctr_seenSet_ins {P : Nat → Nat} (t : Std.HashSet (Array Nat)) (c : Nat)
    (ht : CtrSeenSet P t c) : CtrSeenSet P (t.insert (unpack 24 24 (P c))) (c + 1) := by
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

theorem conjTree_of_K {GM GIM : Nat → Nat} {ng N R : Nat} {P PAR LAB W S : Nat → Nat}
    (h : bfsK (ctStepK GM GIM) P PAR LAB W S ng (N + 1) N R = true) :
    CFSG.Sporadic.Co1I301.Native.conjTree (gensArr ng GM) (gensArr ng GIM) (unpack 24 24 R) N =
      (Array.ofFn (n := N) fun i => PAR i.val, Array.ofFn (n := N) fun i => LAB i.val) := by
  obtain ⟨hN, hP0, hpar0, hlab0, hd, hr⟩ := ctr_bfsK_sound h
  obtain ⟨hP, hinj⟩ := ctr_bfsDistK_sound hd
  have hσ0 : CtrSeenSet P ((∅ : Std.HashSet (Array Nat)).insert (unpack 24 24 (P 0))) 1 := by
    have h0 : CtrSeenSet P (∅ : Std.HashSet (Array Nat)) 0 := fun y => by
      simp only [Std.HashSet.contains_empty, Bool.false_eq_true, false_iff]
      rintro ⟨i, hi, -⟩
      omega
    exact ctr_seenSet_ins _ 0 h0
  have hstp : ∀ x l, l < ng →
      CFSG.Sporadic.Co1Schreier.Native.mul
        (CFSG.Sporadic.Co1Schreier.Native.mul (gensArr ng GM)[l]! (unpack 24 24 x))
          (gensArr ng GIM)[l]! = unpack 24 24 (ctStepK GM GIM x l) := by
    intro x l hl
    rw [ctr_gensArr_get hl, ctr_gensArr_get hl, mul_unpackW, mul_unpackW]
    rfl
  have hs0 : CtrMatch (unpack 24 24) P PAR LAB (CtrSeenSet P) 1
      (#[unpack 24 24 (P 0)], (∅ : Std.HashSet (Array Nat)).insert (unpack 24 24 (P 0)), #[0],
        #[0]) := by
    refine ⟨rfl, fun i hi => ?_, hσ0, rfl, fun i hi => ?_, rfl, fun i hi => ?_⟩ <;>
      obtain rfl : i = 0 := by omega
    · rfl
    · exact hpar0.symm
    · exact hlab0.symm
  have hm := ctr_run (stp := fun x l => CFSG.Sporadic.Co1Schreier.Native.mul
      (CFSG.Sporadic.Co1Schreier.Native.mul (gensArr ng GM)[l]! x) (gensArr ng GIM)[l]!)
    (mem := fun t y => t.contains y) (ins := fun t y => t.insert y) (enc := unpack 24 24)
    (SeenOK := CtrSeenSet P) (W := W) hstp (ctr_seenSet_mem hP hinj)
    (fun t c ht _ => ctr_seenSet_ins t c ht) hN (N + 1) 0 1 _ (Nat.zero_le 1) hs0 hr
  rw [Nat.sub_zero] at hm
  rw [ctr_conjTree_eq, ctr_gensArr_size, ← hP0]
  exact Prod.ext (ctr_eq_ofFn _ _ N hm.psize hm.par) (ctr_eq_ofFn _ _ N hm.lsize hm.lab)

end CFSG.KS.SporSch.M24

end
