module

public import CFSG.Certificates.Kernel.S63K.BfsSound
public import Certificates.Data.Kernel.S63K.Pick
public import CFSG.LargeExtraspecial.S63CD4Inputs
import CFSG.Monster.B.Co2.PermArr

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.S63K

open CFSG.KC.Co1F2 CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native CFSG.KS.SporSch.M24
open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] noncomputable def ElG (P : ℕ → ℕ) (N : ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := N) fun i => unpackR 24 (P i.val)

@[expose] noncomputable def DkG (P PAR LAB : ℕ → ℕ) (N : ℕ) : EnumData :=
  { El := ElG P N, P := Array.ofFn (n := N) (fun i => PAR i.val),
    K := Array.ofFn (n := N) (fun i => LAB i.val), idx := lookup (mkIdx (ElG P N)),
    inv := (ElG P N).map fun x => lookup (mkIdx (ElG P N)) (invPow x) }

@[expose] noncomputable def closOK (G P W : ℕ → ℕ) (ng N : ℕ) : Bool :=
  allN N fun h => allN ng fun l =>
    bAnd(Nat.blt (W (h * ng + l)) N, Nat.beq (P (W (h * ng + l))) (stepK G (P h) l))

@[expose] noncomputable def invOK' (P INV : ℕ → ℕ) (N : ℕ) : Bool :=
  allN N fun i => bAnd(Nat.blt (INV i) N,
    bAnd(Nat.beq (P (INV i)) (ipK (P i) 64 (P i) idP % 2 ^ 576),
      eqM (CFSG.KC.F2W.mulW 24 (P i) (P (INV i))) idP))

@[expose] def resIP (r : Option (Array ℕ) × Array ℕ × Array ℕ) : Array ℕ :=
  match r.1 with
  | some a => a
  | none => r.2.2

@[expose] def bodyIP (x : Array ℕ) (_ : ℕ) (r : Option (Array ℕ) × Array ℕ × Array ℕ) :
    Id (ForInStep (Option (Array ℕ) × Array ℕ × Array ℕ)) :=
  if (r.2.1 == oneR) = true then pure (ForInStep.done (some r.2.2, r.2.1, r.2.2))
  else pure (ForInStep.yield (none, mulR r.2.1 x, r.2.1))

theorem loopIP (X : ℕ) : ∀ n s (p q : ℕ),
    resIP (forIn (m := Id) (List.range' s n) ((none : Option (Array ℕ)), unpackR 24 p,
      unpackR 24 q) (bodyIP (unpackR 24 X))) = unpackR 24 (ipK X n p q) := by
  intro n
  induction n with
  | zero => intro s p q; rfl
  | succ n ih =>
    intro s p q
    rw [List.range'_succ, List.forIn_cons]
    unfold bodyIP
    rw [oneR_eq, beq_unpackR, Nat.mod_eq_of_lt idP_lt]
    by_cases hp : p % 2 ^ 576 = idP
    · have hb : Nat.beq (p % 2 ^ 576) idP = true := by rw [hp]; exact Nat.beq_refl _
      simp only [hb, ↓reduceIte]
      unfold ipK
      rw [if_pos hp]
      rfl
    · have hb : Nat.beq (p % 2 ^ 576) idP = false := by
        cases e : Nat.beq (p % 2 ^ 576) idP
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hp
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      unfold ipK
      rw [if_neg hp, mulR_unpackR, ← oneR_eq]
      exact ih (s + 1) _ p

theorem invPow_eq (x : Array ℕ) : invPow x =
    resIP (forIn (m := Id) (List.range' 0 64) ((none : Option (Array ℕ)), x, oneR) (bodyIP x)) := by
  have e : ∀ (init : Option (Array ℕ) × Array ℕ × Array ℕ)
      (f : ℕ → Option (Array ℕ) × Array ℕ × Array ℕ →
        Id (ForInStep (Option (Array ℕ) × Array ℕ × Array ℕ))),
      forIn (m := Id) [:64] init f = forIn (m := Id) (List.range' 0 64) init f := by
    intro init f
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  unfold invPow
  dsimp only
  rw [e]
  generalize hR : forIn (m := Id) (List.range' 0 64) ((none : Option (Array ℕ)), x, oneR) _ = R
  have h2 : forIn (m := Id) (List.range' 0 64) ((none : Option (Array ℕ)), x, oneR) (bodyIP x) = R :=
    hR
  rw [h2]
  rcases R with ⟨_ | r, a, b⟩ <;> rfl

theorem invPow_unpackR (X : ℕ) : invPow (unpackR 24 X) = unpackR 24 (ipK X 64 X idP) := by
  have h := loopIP X 64 0 X idP
  rw [← oneR_eq] at h
  exact (invPow_eq _).trans h

variable {gs : Array (Array ℕ)} {G P PAR LAB W S INV : ℕ → ℕ} {ng N : ℕ}

theorem elG_get {i : ℕ} (hi : i < N) : (ElG P N)[i]! = unpackR 24 (P i) := by
  rw [getElem!_pos (ElG P N) i (by simp [ElG, hi])]
  simp [ElG]

theorem mkEnum_of_K (hng : gs.size = ng) (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l))
    (h : bfsK (stepK G) P PAR LAB W S ng (N + 1) N idP = true) : mkEnum gs = DkG P PAR LAB N := by
  unfold mkEnum
  rw [(enumBFS_of_K (W := W) hng hg h).1]
  rfl

theorem idx_of_K (hng : gs.size = ng) (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l))
    (h : bfsK (stepK G) P PAR LAB W S ng (N + 1) N idP = true) {w : ℕ} (hw : w < N) :
    lookup (mkIdx (ElG P N)) (unpackR 24 (P w)) = w :=
  lookup_mkIdx (enumBFS_of_K (W := W) hng hg h).2.2.1 (enumBFS_of_K (W := W) hng hg h).2.2.2 hw

theorem eqM_iff {A B : ℕ} : eqM A B = true ↔ unpackR 24 A = unpackR 24 B := by
  unfold eqM
  rw [Nat.beq_eq, unpackR_inj]

theorem memR_eq (hng : gs.size = ng) (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l))
    (h : bfsK (stepK G) P PAR LAB W S ng (N + 1) N idP = true) (Y : ℕ) :
    memR (ElG P N) (lookup (mkIdx (ElG P N))) (unpackR 24 Y) =
      (List.range N).any fun w => eqM (P w) Y := by
  have hsz : (ElG P N).size = N := by simp [ElG]
  cases ha : (List.range N).any fun w => eqM (P w) Y
  · unfold memR
    cases hm : (decide (lookup (mkIdx (ElG P N)) (unpackR 24 Y) < (ElG P N).size) &&
        (ElG P N)[lookup (mkIdx (ElG P N)) (unpackR 24 Y)]! == unpackR 24 Y)
    · rfl
    · exfalso
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hsz] at hm
      obtain ⟨hk, he⟩ := hm
      rw [elG_get hk] at he
      have : ((List.range N).any fun w => eqM (P w) Y) = true :=
        List.any_eq_true.2 ⟨_, List.mem_range.2 hk, eqM_iff.2 he⟩
      rw [ha] at this
      exact Bool.false_ne_true this
  · obtain ⟨w, hw, he⟩ := List.any_eq_true.1 ha
    have hw' := List.mem_range.1 hw
    rw [← eqM_iff.1 he]
    unfold memR
    rw [idx_of_K hng hg h hw', elG_get hw', hsz]
    simp [hw']

theorem inv_of_K (hng : gs.size = ng) (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l))
    (h : bfsK (stepK G) P PAR LAB W S ng (N + 1) N idP = true) (hi : invOK' P INV N = true)
    {i : ℕ} (hiN : i < N) :
    (DkG P PAR LAB N).inv[i]! = INV i ∧ INV i < N ∧
      mulR (unpackR 24 (P i)) (unpackR 24 (P (INV i))) = oneR := by
  have hk := MatL.allN_iff.1 hi i hiN
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hk
  obtain ⟨h1, h2, h3⟩ := hk
  refine ⟨?_, h1, ?_⟩
  · have hsz : (DkG P PAR LAB N).inv.size = N := by simp [DkG, ElG]
    rw [getElem!_pos (DkG P PAR LAB N).inv i (by rw [hsz]; exact hiN)]
    simp only [DkG, Array.getElem_map]
    rw [← getElem!_pos (ElG P N) i (by simp [ElG, hiN]), elG_get hiN,
      invPow_unpackR, unpackR_mod,
      ← Nat.eq_of_beq_eq_true h2, idx_of_K hng hg h h1]
  · rw [mulR_unpackR, oneR_eq]
    exact eqM_iff.1 h3

theorem ok_of_K (hng : gs.size = ng) (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l))
    (h : bfsK (stepK G) P PAR LAB W S ng (N + 1) N idP = true) (hc : closOK G P W ng N = true) :
    (DkG P PAR LAB N).ok gs N = true := by
  have F := enumBFS_of_K (W := W) hng hg h
  unfold EnumData.ok enumOK
  have hsz : (DkG P PAR LAB N).El.size = N := by simp [DkG, ElG]
  have hroot : P 0 = idP := (bfsK_sound h).2.1
  have hN : 0 < N := (bfsK_sound h).1
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hsz]
  refine ⟨⟨⟨hN, ?_⟩, ?_⟩, trivial⟩
  · change (ElG P N)[0]! = oneR
    rw [elG_get hN, hroot, oneR_eq]
  · refine allLt_iff.2 fun i hi => ?_
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    change ((validR (ElG P N)[i]! = true ∧ lookup (mkIdx (ElG P N)) (ElG P N)[i]! = i) ∧ (i = 0 ∨
      (((DkG P PAR LAB N).P[i]! < i ∧ (DkG P PAR LAB N).K[i]! < gs.size) ∧
        (ElG P N)[i]! = mulR gs[(DkG P PAR LAB N).K[i]!]! (ElG P N)[(DkG P PAR LAB N).P[i]!]!))) ∧
      allLt gs.size (fun k => decide (lookup (mkIdx (ElG P N)) (mulR gs[k]! (ElG P N)[i]!) < N) &&
        (ElG P N)[lookup (mkIdx (ElG P N)) (mulR gs[k]! (ElG P N)[i]!)]! == mulR gs[k]! (ElG P N)[i]!) =
        true
    rw [elG_get hi, validR_unpackR, idx_of_K hng hg h hi, hng]
    refine ⟨⟨⟨rfl, rfl⟩, ?_⟩, ?_⟩
    · by_cases h0 : i = 0
      · exact Or.inl h0
      · right
        obtain ⟨h1, h2, h3⟩ := F.2.1 i (by omega) hi
        have ep : (DkG P PAR LAB N).P[i]! = PAR i := by simp [DkG, getElem!_pos, hi]
        have ek : (DkG P PAR LAB N).K[i]! = LAB i := by simp [DkG, getElem!_pos, hi]
        rw [ep, ek, elG_get (by omega), step_eq hg _ h2, ← h3]
        exact ⟨⟨h1, h2⟩, rfl⟩
    · refine allLt_iff.2 fun k hk => ?_
      have h1 := MatL.allN_iff.1 (MatL.allN_iff.1 hc i hi) k hk
      simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h1
      obtain ⟨hw, hpw⟩ := h1
      rw [step_eq hg _ hk, ← Nat.eq_of_beq_eq_true hpw, idx_of_K hng hg h hw, elG_get hw]
      simp [hw]

theorem invOK_of_K (hng : gs.size = ng) (hg : ∀ l < ng, gs[l]! = unpackR 24 (G l))
    (h : bfsK (stepK G) P PAR LAB W S ng (N + 1) N idP = true) (hi : invOK' P INV N = true) :
    (DkG P PAR LAB N).invOK N = true := by
  unfold EnumData.invOK
  refine allLt_iff.2 fun i hiN => ?_
  obtain ⟨h1, h2, h3⟩ := inv_of_K hng hg h hi hiN
  change (decide ((DkG P PAR LAB N).inv[i]! < N) &&
    mulR (ElG P N)[i]! (ElG P N)[(DkG P PAR LAB N).inv[i]!]! == oneR) = true
  rw [h1, elG_get hiN, elG_get h2, h3]
  simp [h2]

end CFSG.KC.S63K

end
