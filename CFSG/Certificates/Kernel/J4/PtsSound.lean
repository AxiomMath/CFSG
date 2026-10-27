module

public import CFSG.Certificates.Kernel.J4.TStructSound
public import Certificates.Data.Kernel.J4Pts

public section

namespace CFSG.KJ4.TStruct

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models CFSG.KC.Loop
open CFSG.Certificates.DceWord (lvE wv)
open CFSG.Certificates.J4Words (jv)
open CFSG.Certificates.J4KShape (rv)

@[expose] def PInv (k : KD) (BM : ℕ) : Prop :=
  ∀ q < k.NOM, BM.testBit q = true → ∃ g ∈ Khat k.LET, actS.act (thV k) g = ptVecs (k.PT q)

theorem brec_cases {P : ℕ → Prop} {a x : ℕ} {b : Bool} (h0 : P a) (h1 : b = true → P x) :
    P (Bool.rec (motive := fun _ => ℕ) a x b) := by
  cases b
  · exact h0
  · exact h1 rfl

theorem testBit_lor_one (BM i q : ℕ) :
    (Nat.lor BM (Nat.shiftLeft 1 i)).testBit q = (BM.testBit q || decide (i = q)) := by
  change (BM ||| 1 <<< i).testBit q = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_of_land {BM p : ℕ} (h : 0 < Nat.land BM (Nat.shiftLeft 1 p)) : BM.testBit p = true := by
  by_contra hn
  have h0 : Nat.land BM (Nat.shiftLeft 1 p) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    change (BM &&& 1 <<< p).testBit j = (0 : ℕ).testBit j
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hj : p = j
    · subst hj
      simpa using hn
    · simp [hj]
  rw [h0] at h
  exact Nat.lt_irrefl 0 h

theorem pts_letter {k : KD} (hS : kSetup k = true) {c : ℕ} (hc : ptsLet c = true) :
    ∃ u ∈ Khat k.LET, ((u : GLm) : Mat12) = toMat (letMat k.LET c) := by
  obtain ⟨-, h01, h23, h56, -⟩ := kSetup_parts hS
  rcases orB_eq_true.1 hc with h | h
  · rw [Nat.eq_of_beq_eq_true h]
    exact ⟨xh k.LET, Subgroup.subset_closure (by simp), val_lu h01⟩
  rcases orB_eq_true.1 h with h | h
  · rw [Nat.eq_of_beq_eq_true h]
    exact ⟨yh k.LET, Subgroup.subset_closure (by simp), val_lu h23⟩
  · rw [Nat.eq_of_beq_eq_true h]
    exact ⟨zh k.LET, Subgroup.subset_closure (by simp), val_lu h56⟩

theorem pts_step {k : KD} (o : Ok k) (e : ℕ) {BM : ℕ} (hI : PInv k BM) :
    PInv k (ptsStep k.PT k.LET k.NOM e BM) := by
  simp only [ptsStep, R.strictN_eq]
  refine brec_cases (P := PInv k) hI (fun hb => ?_)
  obtain ⟨hi, hb⟩ := andB_eq_true.1 hb
  obtain ⟨hp, hb⟩ := andB_eq_true.1 hb
  obtain ⟨hset, hb⟩ := andB_eq_true.1 hb
  obtain ⟨hc, hpt⟩ := andB_eq_true.1 hb
  rw [chkPtF_eq] at hpt
  have hi' := blt_eq_true.1 hi
  have hp' := blt_eq_true.1 hp
  intro q hq hbit
  rw [testBit_lor_one] at hbit
  rcases Bool.or_eq_true_iff.1 hbit with hbit | hbit
  · exact hI q hq hbit
  have hqi := (decide_eq_true_iff.1 hbit).symm
  subst hqi
  obtain ⟨g, hg, hgP⟩ := hI _ hp' (testBit_of_land (blt_eq_true.1 hset))
  obtain ⟨u, hu, huM⟩ := pts_letter o.hS hc
  have hP := (kPts_parts o.hP).1
  refine ⟨g * u, mul_mem hg hu, ?_⟩
  rw [actS.act_mul, hgP, act_eq, huM]
  exact chkPt_image (andB_eq_true.1 (hP _ hp')).1 (andB_eq_true.1 (hP _ hi')).1 hpt

theorem pts_run {k : KD} (o : Ok k) : ∀ (m C BM : ℕ), PInv k BM →
    PInv k (ptsRun k.PT k.LET k.NOM C m BM)
  | 0, _, _, h => h
  | m + 1, C, BM, h => by
    have key : ptsRun k.PT k.LET k.NOM C (m + 1) BM = strictN C (fun C' =>
        strictN (Nat.land C' 18446744073709551615) (fun e => strictN (ptsStep k.PT k.LET k.NOM e BM)
          (fun B => ptsRun k.PT k.LET k.NOM (Nat.shiftRight C' 64) m B))) := rfl
    rw [key, R.strictN_eq, R.strictN_eq, R.strictN_eq]
    exact pts_run o m _ _ (pts_step o _ h)

theorem pts_list {k : KD} (o : Ok k) : ∀ (l : List ℕ) (BM : ℕ), PInv k BM →
    PInv k (ptsL k.PT k.LET k.NOM l BM)
  | [], _, h => h
  | C :: l, BM, h => by
    have key : ptsL k.PT k.LET k.NOM (C :: l) BM =
        strictN (ptsRun k.PT k.LET k.NOM (Nat.shiftRight C 12) (Nat.land C 4095) BM)
          (ptsL k.PT k.LET k.NOM l) := rfl
    rw [key, R.strictN_eq]
    exact pts_list o l _ (pts_run o _ _ _ h)

theorem kSetup_root {k : KD} (h : kSetup k = true) : k.PT k.i0 = k.TH := by
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  obtain ⟨-, h⟩ := andB_eq_true.1 h
  exact beq_eq_true.1 (andB_eq_true.1 h).1

theorem pts_root {k : KD} (o : Ok k) : PInv k (Nat.shiftLeft 1 k.i0) := by
  intro q _ hq
  have e : Nat.shiftLeft 1 k.i0 = 2 ^ k.i0 := by
    rw [← Nat.one_shiftLeft]
    rfl
  rw [e, Nat.testBit_two_pow] at hq
  have hqi := (decide_eq_true_iff.1 hq).symm
  subst hqi
  refine ⟨1, one_mem _, ?_⟩
  rw [actS.act_one, thV, kSetup_root o.hS]

theorem allIn_spec' {a b : ℕ} {f : ℕ → Bool} (h : allIn a b f = true) {i : ℕ} (hai : a ≤ i)
    (hi : i < b) : f i = true := by
  refine CFSG.Certificates.J4KShape.rngAll_spec _ h i hai hi ?_
  change i < a + 64 * ((b - a) >>> 6 + 1)
  rw [Nat.shiftRight_eq_div_pow]
  have h64 : (2 : ℕ) ^ 6 = 64 := rfl
  rw [h64]
  omega

theorem j4Pts_parts {k : KD} {PL : List ℕ} (h : j4Pts k PL = true) :
    chkInv k.PS1 k.PS1 = true ∧ row11 (letMat k.LET 2) = true ∧ row11 (letMat k.LET 5) = true ∧
    (∀ a, k.nH ≤ a → a < 2 ^ 16 → k.HT a = 0) ∧ (∀ w < 2 ^ 16, ptsWord k.RT k.WT k.INV w = true) ∧
    ptsL k.PT k.LET k.NOM PL (Nat.shiftLeft 1 k.i0) = fullOf k := by
  obtain ⟨h1, h⟩ := andB_eq_true.1 h
  obtain ⟨h2, h⟩ := andB_eq_true.1 h
  obtain ⟨h3, h⟩ := andB_eq_true.1 h
  obtain ⟨h4, h⟩ := andB_eq_true.1 h
  obtain ⟨h5, h6⟩ := andB_eq_true.1 h
  exact ⟨h1, h2, h3, fun a ha hb => beq_eq_true.1 (allIn_spec' h4 ha hb),
    fun w hw => allIn_spec' h5 (Nat.zero_le w) hw, beq_eq_true.1 h6⟩

theorem orb_of_pts {k : KD} (o : Ok k) {PL : List ℕ} (h : j4Pts k PL = true) : Orb k := by
  have hB := (j4Pts_parts h).2.2.2.2.2
  have hI := pts_list o PL _ (pts_root o)
  rw [hB] at hI
  intro j hj
  refine hI j hj ?_
  have e : fullOf k = 2 ^ k.NOM - 1 := by
    unfold fullOf
    rw [← Nat.one_shiftLeft]
    rfl
  rw [e, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

theorem ps1_mem {k : KD} (hS : kSetup k = true) {PL : List ℕ} (h : j4Pts k PL = true) :
    ∃ ps : Khat k.LET, ((ps : GLm) : Mat12) = toMat k.PS1 := by
  have hv : ((lu k.PS1 k.PS1 : GLm) : Mat12) = toMat k.PS1 := val_lu (j4Pts_parts h).1
  exact ⟨⟨_, unit_mem hS (kSetup_more hS).2.2.2.1 hv⟩, hv⟩

theorem khat_le_Rsub {k : KD} (o : Ok k) {PL : List ℕ} (h : j4Pts k PL = true) : Khat k.LET ≤ Rsub := by
  obtain ⟨-, h01, h23, h56, -⟩ := kSetup_parts o.hS
  obtain ⟨-, hy, hz, -⟩ := j4Pts_parts h
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl)
  · exact mem_Rsub_of_row11 (val_lu h01) o.x11
  · exact mem_Rsub_of_row11 (val_lu h23) hy
  · exact mem_Rsub_of_row11 (val_lu h56) hz

theorem hz_of_pts {k : KD} {PL : List ℕ} (h : j4Pts k PL = true) :
    ∀ a, k.nH ≤ a → a < 2 ^ 16 → k.HT a = 0 :=
  (j4Pts_parts h).2.2.2.1

theorem wFits_lt' {W n : ℕ} (h : wFits W n = true) : W < 256 ^ n := by
  have h' : W < 1 <<< (8 * n) := blt_eq_true.1 h
  rw [Nat.one_shiftLeft, pow_mul] at h'
  exact h'

theorem lvE_lvE {G : Type*} [Group G] (f : ℕ → G) : lvE (lvE f) = lvE f := by
  funext c
  unfold lvE
  split_ifs <;> rfl

theorem words_of_pts {k : KD} (hS : kSetup k = true) (hR : kRange k = true) {PL : List ℕ}
    (h : j4Pts k PL = true) {G : Type*} [Group G] (x y t : G) (ht : t * t = 1)
    (hRv : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1) :
    ∀ w < 2 ^ 16, wFits (wW (k.WT w)) (wN (k.WT w)) = true ∧ rv (jv x y t 1) (k.WT w) = 1 := by
  intro w hw
  have hp := (j4Pts_parts h).2.2.2.2.1 w hw
  simp only [ptsWord, wordOK, CFSG.Certificates.J4Chain.letB_eq] at hp
  obtain ⟨hlt, hp⟩ := andB_eq_true.1 hp
  obtain ⟨hfit, hc⟩ := andB_eq_true.1 hp
  have hlt' := blt_eq_true.1 hlt
  have hrel : relOK k.LET (k.RT (wR (k.WT w))) = true := (kSetup_more hS).2.1 _ hlt'
  have hr := wFits_lt' (andB_eq_true.1 hrel).1
  rw [(kRange_parts hR).1] at hc
  refine ⟨hfit, ?_⟩
  have e := CFSG.Certificates.J4Words.chkWord_val (lvE (jv x y t 1)) hr (hRv _ hlt') (fun q _ hne => by
    obtain ⟨hl, hj⟩ := CFSG.Certificates.J4Words.jv_inv x y t 1 ht (wLet (wW (k.WT w)) q)
    simp only [lvE, hne, Nat.ne_of_lt hl, ↓reduceIte]
    exact hj) hc
  rw [lvE_lvE] at e
  exact e

end CFSG.KJ4.TStruct

end
