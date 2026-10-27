module

public import CFSG.Certificates.Kernel.LceSP.Walk
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.Certificates.LceP

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop

theorem sI_eq (S : ℕ) : sI S = S % 4294967296 := land32 S
theorem sN_eq (S : ℕ) : sN S = S / 4294967296 := shr_eq S 32

theorem sI_lt (S : ℕ) : sI S < 4294967296 := by
  rw [sI_eq]
  omega

theorem mkS_eq {i : ℕ} (nx : ℕ) (hi : i < 4294967296) : mkS i nx = i + nx * 4294967296 :=
  lor32 nx hi

section Facts

variable {G : Type*} [Group G] (gen : ℕ → G) (H K : Subgroup G)

@[expose] def FInv (blk : ℕ → ℕ) (INV nC i N : ℕ) : Prop :=
  (∀ h < i, recOK INV nC (fct blk h) = true) ∧ ∃ rep : ℕ → G, rep 0 = 1 ∧ (∀ k < N, rep k ∈ K) ∧
    ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) → ∀ h < i, el gen rep' (fct blk h) ∈ H

@[expose] def FGood (blk : ℕ → ℕ) (INV nC S : ℕ) : Prop :=
  S = 0 ∨ (1 ≤ sN S ∧ FInv gen H K blk INV nC (sI S) (sN S))

theorem FInv_zero (blk : ℕ → ℕ) (INV nC N : ℕ) : FInv gen H K blk INV nC 0 N :=
  ⟨fun h hh => absurd hh (Nat.not_lt_zero h), fun _ => 1, rfl, fun _ _ => K.one_mem,
    fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩

theorem FGood_mkS {blk : ℕ → ℕ} {INV nC i N : ℕ} (hi : i ≤ 4294967296) (hN : 1 ≤ N)
    (hF : i < 4294967296 → FInv gen H K blk INV nC i N) : FGood gen H K blk INV nC (mkS i N) := by
  right
  rcases Nat.lt_or_ge i 4294967296 with hlt | hge
  · rw [sN_eq, sI_eq, mkS_eq N hlt]
    have e1 : (i + N * 4294967296) / 4294967296 = N := by omega
    have e2 : (i + N * 4294967296) % 4294967296 = i := by omega
    rw [e1, e2]
    exact ⟨hN, hF hlt⟩
  · have hi' : i = 4294967296 := by omega
    subst hi'
    have e : mkS 4294967296 N = (1 ||| N) * 4294967296 := by
      change (1 <<< 32) ||| (N <<< 32) = _
      rw [← Nat.shiftLeft_or_distrib, Nat.shiftLeft_eq]
    rw [sN_eq, sI_eq, e, Nat.mul_div_cancel _ (by norm_num), Nat.mul_mod_left]
    exact ⟨le_trans (by norm_num) Nat.left_le_or, FInv_zero gen H K blk INV nC _⟩

@[expose] def WOK (w : ℕ) : Prop :=
  (wKind w = 2 → bv gen (wWord w) (wLen w) = 1) ∧ (wKind w = 3 → bv gen (wWord w) (wLen w) ∈ H)

theorem factStep_good {blk WT : ℕ → ℕ} {INV INV8 L nC : ℕ} (hinv : invOK INV INV8 L = true)
    (hWT : ∀ k < 65536, WOK gen H (WT k)) (hK : ∀ c < L, lv gen c ∈ K) {S J w : ℕ}
    (hS : FGood gen H K blk INV nC S) (hw : Nat.land J 1 = 1 → ∃ k < 65536, w = WT k) :
    FGood gen H K blk INV nC (factStep blk INV nC L J S (fct blk (sI S)) w) := by
  unfold factStep
  rw [brec_eq]
  split_ifs with hpos
  · rw [Nat.blt_eq] at hpos
    rcases hS with h0 | ⟨hN, hrec, rep, hrep0, hrepK, hfacts⟩
    · omega
    rw [brec_eq]
    split_ifs with hJ
    · rw [Nat.beq_eq] at hJ
      rw [brec_eq]
      split_ifs with hwk
      · obtain ⟨k, hk, rfl⟩ := hw hJ
        have hfs : Nat.land (Nat.shiftRight J 17) 1048575 < 1048576 := by
          rw [land20]
          omega
        have hwalk : ∀ rep' : ℕ → G, (∀ k < sN S, rep' k = rep k) →
            recOK INV nC (fct blk (sI S)) = true ∧ el gen rep' (fct blk (sI S)) ∈ H := by
          intro rep' hag
          refine walkOK_sound gen H hwk hfs (fun h hh => ⟨hfacts rep' hag h hh, ?_⟩) ?_
            (hWT k hk).1 (hWT k hk).2
          · exact (lv_fic gen blk hinv (hrec h hh)).1
          · rw [hag 0 (by omega), hrep0]
        apply FGood_mkS gen H K (Nat.succ_le_of_lt (sI_lt S)) hN
        intro _
        refine ⟨fun h hh => ?_, rep, hrep0, hrepK, fun rep' hag h hh => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
          · exact hrec h hh
          · exact (hwalk rep (fun _ _ => rfl)).1
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
          · exact hfacts rep' hag h hh
          · exact (hwalk rep' hag).2
      · exact Or.inl rfl
    · rw [brec_eq]
      split_ifs with htree
      · unfold fTree at htree
        simp only [andB_iff, Nat.beq_eq, Nat.blt_eq] at htree
        obtain ⟨hrR, hfy, hfx, hfc⟩ := htree
        apply FGood_mkS gen H K (Nat.succ_le_of_lt (sI_lt S)) (by omega)
        intro _
        refine ⟨fun h hh => ?_, Function.update rep (sN S) (rep (fx (fct blk (sI S))) *
          lv gen (fc (fct blk (sI S)))), ?_, fun k hk => ?_, fun rep' hag h hh => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
          · exact hrec h hh
          · exact hrR
        · rw [Function.update_of_ne (show (0 : ℕ) ≠ sN S by omega)]
          exact hrep0
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · rw [Function.update_of_ne (show k ≠ sN S by omega)]
            exact hrepK k hk
          · rw [Function.update_self]
            exact K.mul_mem (hrepK _ hfx) (hK _ hfc)
        · have hag' : ∀ k < sN S, rep' k = rep k := by
            intro k hk
            rw [hag k (by omega), Function.update_of_ne (show k ≠ sN S by omega)]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
          · exact hfacts rep' hag' h hh
          · unfold el
            rw [hfy, hag (sN S) (by omega), Function.update_self, hag' _ hfx, mul_inv_cancel]
            exact H.one_mem
      · exact Or.inl rfl
  · exact Or.inl rfl

@[expose] noncomputable def chunkRec (blk WT : ℕ → ℕ) (INV nC L : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight J (nat_lit 1)) (factStep blk INV nC L J S (fct blk (sI S)) (nat_lit 0)))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        ih (Nat.shiftRight J (jLen J w)) (factStep blk INV nC L J S (fct blk (sI S)) w)))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

theorem chunk_good {blk WT : ℕ → ℕ} {INV INV8 L nC : ℕ} (hinv : invOK INV INV8 L = true)
    (hWT : ∀ k < 65536, WOK gen H (WT k)) (hK : ∀ c < L, lv gen c ∈ K) :
    ∀ k J S, FGood gen H K blk INV nC S → FGood gen H K blk INV nC (chunkRec blk WT INV nC L k J S)
  | 0, _, _, hS => hS
  | k + 1, J, S, hS => by
    change FGood gen H K blk INV nC (Bool.rec (motive := fun _ => Nat)
      (chunkRec blk WT INV nC L k (Nat.shiftRight J 1) (factStep blk INV nC L J S (fct blk (sI S)) 0))
      (strictN (strictN (Nat.land (Nat.shiftRight J 1) 65535) WT) (fun w =>
        chunkRec blk WT INV nC L k (Nat.shiftRight J (jLen J w))
          (factStep blk INV nC L J S (fct blk (sI S)) w)))
      (Nat.beq (Nat.land J 1) 1))
    rw [brec_eq]
    split_ifs with hJ
    · simp only [strictN_eq]
      apply chunk_good hinv hWT hK k
      apply factStep_good gen H K hinv hWT hK hS
      intro _
      refine ⟨_, ?_, rfl⟩
      rw [land_lit _ 16 65535 (by norm_num)]
      omega
    · apply chunk_good hinv hWT hK k
      apply factStep_good gen H K hinv hWT hK hS
      intro h1
      rw [Nat.beq_eq] at hJ
      exact absurd h1 hJ

theorem runFacts_good {blk WT : ℕ → ℕ} {INV INV8 L nC : ℕ} (hinv : invOK INV INV8 L = true)
    (hWT : ∀ k < 65536, WOK gen H (WT k)) (hK : ∀ c < L, lv gen c ∈ K) :
    ∀ (Cs : List ℕ) S, FGood gen H K blk INV nC S →
      FGood gen H K blk INV nC (runFacts blk WT INV nC L Cs S)
  | [], _, hS => hS
  | C :: Cs, S, hS => by
    change FGood gen H K blk INV nC (strictN (runChunk blk WT INV nC L C S)
      (runFacts blk WT INV nC L Cs))
    rw [strictN_eq]
    apply runFacts_good hinv hWT hK Cs
    exact chunk_good gen H K hinv hWT hK _ _ _ hS

end Facts

@[expose] def CGood (blk LVs : ℕ → ℕ) (nf L X : ℕ) : Prop :=
  X = 0 ∨ (1 ≤ X ∧ ∀ x < X - 1, alive LVs x = true → ∀ c < L,
    ∃ e, slotOK blk LVs nf (Nat.lor x (Nat.shiftLeft c 20)) e = true)

theorem slots_spec (blk LVs : ℕ → ℕ) (nf L x : ℕ) : ∀ k ≤ L, ∀ J,
    Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun k ih J => andB
        (slotOK blk LVs nf (Nat.lor x (Nat.shiftLeft (Nat.sub L (Nat.succ k)) (nat_lit 20)))
          (Nat.land J (nat_lit 4294967295)))
        (letB (Nat.shiftRight J (nat_lit 32)) ih)) k J = true →
    ∀ t < k, ∃ e, slotOK blk LVs nf (Nat.lor x (Nat.shiftLeft (L - k + t) 20)) e = true
  | 0, _, _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | k + 1, hk, J, h, t, ht => by
    change andB (slotOK blk LVs nf (Nat.lor x (Nat.shiftLeft (Nat.sub L (Nat.succ k)) 20))
      (Nat.land J 4294967295)) (letB (Nat.shiftRight J 32) (Nat.rec (motive := fun _ => ℕ → Bool)
        (fun _ => true) (fun k ih J => andB
          (slotOK blk LVs nf (Nat.lor x (Nat.shiftLeft (Nat.sub L (Nat.succ k)) (nat_lit 20)))
            (Nat.land J (nat_lit 4294967295)))
          (letB (Nat.shiftRight J (nat_lit 32)) ih)) k)) = true at h
    rw [andB_iff, letB_eq] at h
    obtain ⟨h1, h2⟩ := h
    rcases t with _ | t
    · refine ⟨Nat.land J 4294967295, ?_⟩
      simpa using h1
    · obtain ⟨e, he⟩ := slots_spec blk LVs nf L x k (by omega) _ h2 t (by omega)
      have e1 : L - k + t = L - (k + 1) + (t + 1) := by omega
      rw [e1] at he
      exact ⟨e, he⟩

theorem slotsOK_spec {blk LVs : ℕ → ℕ} {nf L x J : ℕ} (h : slotsOK blk LVs nf L x J = true) :
    ∀ c < L, ∃ e, slotOK blk LVs nf (Nat.lor x (Nat.shiftLeft c 20)) e = true := by
  intro c hc
  have := slots_spec blk LVs nf L x L le_rfl J h c hc
  rwa [Nat.sub_self, Nat.zero_add] at this

theorem covStep_good {blk LVs : ℕ → ℕ} {nf L J X : ℕ} {a : Bool} (hX : CGood blk LVs nf L X)
    (ha : alive LVs (X - 1) = a) : CGood blk LVs nf L (covStep blk LVs nf L J X a) := by
  unfold covStep
  rw [brec_eq]
  split_ifs with hpos
  · rw [Nat.blt_eq] at hpos
    rcases hX with h0 | ⟨-, hX⟩
    · omega
    have e : Nat.succ X - 1 = X := rfl
    rw [brec_eq]
    split_ifs with ha'
    · rw [brec_eq]
      split_ifs with hsl
      · right
        refine ⟨by omega, fun x hx hal => ?_⟩
        rw [e] at hx
        rcases Nat.lt_or_ge x (X - 1) with h1 | h1
        · exact hX x h1 hal
        · have : x = X - 1 := by omega
          subst this
          exact slotsOK_spec hsl
      · exact Or.inl rfl
    · right
      refine ⟨by omega, fun x hx hal => ?_⟩
      rw [e] at hx
      rcases Nat.lt_or_ge x (X - 1) with h1 | h1
      · exact hX x h1 hal
      · have : x = X - 1 := by omega
        subst this
        rw [ha] at hal
        exact absurd hal ha'
  · exact Or.inl rfl

@[expose] noncomputable def covRec (blk LVs : ℕ → ℕ) (nf L : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ X => X)
    (fun _ ih J X =>
      Bool.rec (motive := fun _ => Nat)
        (strictN (covStep blk LVs nf L J X false) (ih J))
        (strictN (covStep blk LVs nf L J X true) (fun X' =>
          strictN (Nat.shiftRight J (Nat.mul (nat_lit 32) L)) (fun J' => ih J' X')))
        (alive LVs (Nat.sub X (nat_lit 1)))) k

theorem cov_good {blk LVs : ℕ → ℕ} {nf L : ℕ} :
    ∀ k J X, CGood blk LVs nf L X → CGood blk LVs nf L (covRec blk LVs nf L k J X)
  | 0, _, _, hX => hX
  | k + 1, J, X, hX => by
    change CGood blk LVs nf L (Bool.rec (motive := fun _ => Nat)
        (strictN (covStep blk LVs nf L J X false) (covRec blk LVs nf L k J))
        (strictN (covStep blk LVs nf L J X true) (fun X' =>
          strictN (Nat.shiftRight J (Nat.mul 32 L)) (fun J' => covRec blk LVs nf L k J' X')))
        (alive LVs (Nat.sub X 1)))
    rw [brec_eq]
    split_ifs with ha
    · simp only [strictN_eq]
      exact cov_good k _ _ (covStep_good hX ha)
    · simp only [strictN_eq]
      exact cov_good k _ _ (covStep_good hX (by simpa using ha))

theorem runCover_good {blk LVs : ℕ → ℕ} {nf L : ℕ} :
    ∀ (Cs : List ℕ) X, CGood blk LVs nf L X → CGood blk LVs nf L (runCover blk LVs nf L Cs X)
  | [], _, hX => hX
  | C :: Cs, X, hX => by
    change CGood blk LVs nf L (strictN (covChunk blk LVs nf L C X) (runCover blk LVs nf L Cs))
    rw [strictN_eq]
    exact runCover_good Cs _ (cov_good _ _ _ hX)

end CFSG.Certificates.LceP

end
