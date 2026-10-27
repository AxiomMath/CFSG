module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bits
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeModel

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bmulVec)
open CFSG.EvenSmallLie.OmegaEight.Stage2 (urRows)

theorem one_le_deg (ε : Eps) : 1 ≤ deg ε := by cases ε <;> decide

@[expose] noncomputable def Lm : (ε : Eps) → Subgroup (Equiv.Perm (Fin (deg ε)))
  | .plus => OmegaEight.omega1T
  | .minus => OmegaEightMinus.omegaT

theorem memL_iff {ε : Eps} {g : Array ℕ} {G : Equiv.Perm (Fin (deg ε))} (hG : Rep (deg ε) g G) :
    memL ε g = true ↔ G ∈ Lm ε := by
  cases ε
  · exact ofArrays_mem_iff (by norm_num) OmegaEight.omega1Chain_ok.1 hG
  · exact ofArrays_mem_iff (by norm_num) OmegaEightMinus.omegaChain_ok.1 hG

@[expose] def lOdd : Eps → ℕ
  | .plus => 42525
  | .minus => 48195

theorem card_Lm (ε : Eps) : Nat.card (Lm ε) = 4096 * lOdd ε := by
  cases ε
  · exact OmegaEight.card_omega1T
  · exact OmegaEightMinus.card_omegaT

theorem odd_lOdd (ε : Eps) : Odd (lOdd ε) := by
  cases ε <;> decide

theorem card_Lm_eq (ε : Eps) : 4096 * lOdd ε = nOrb ε * (64 * (oBound ε / 2)) := by
  cases ε <;> rfl

theorem pS_size (ε : Eps) : (pS ε).size = 12 + (pWords ε).length := by
  cases ε <;> simp [pS, pSPlus, pSMinus, OmegaEight.size_pushWords, pOrig]

theorem uS_size (ε : Eps) : (uS ε).size = 12 := by
  cases ε <;> simp [uS, uSPlus, uSMinus, uOrig]

@[expose] noncomputable def pQ (ε : Eps) : RawSchreierDatum (deg ε) :=
  RawSchreierDatum.ofArrays (deg ε) (one_le_deg ε) (pS ε) 12 (by rw [pS_size]; omega) (pBase ε)
    (by cases ε <;> decide) (OmegaEight.wordsOf 12 (pWords ε))

@[expose] noncomputable def uQ (ε : Eps) : RawSchreierDatum (deg ε) :=
  RawSchreierDatum.ofArrays (deg ε) (one_le_deg ε) (uS ε) 12 (by rw [uS_size]) (uBase ε)
    (by cases ε <;> decide) (OmegaEight.wordsOf 12 [])

@[expose] noncomputable def PQm (ε : Eps) : Subgroup (Equiv.Perm (Fin (deg ε))) := (pQ ε).originalSubgroup

@[expose] noncomputable def UQm (ε : Eps) : Subgroup (Equiv.Perm (Fin (deg ε))) := (uQ ε).originalSubgroup

theorem pChain_ok (ε : Eps) :
    rawChainOK (deg ε) ((pS ε).extract 0 12) (pS ε) (((pBase ε).map Fin.val).toArray)
      (OmegaEight.wordsOf 12 (pWords ε)) 4 = true ∧
    rawOrbitSizes (deg ε) (pS ε) (((pBase ε).map Fin.val).toArray) = pSizes ε := by
  have h := (modelChecks ε).1
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem uChain_ok (ε : Eps) :
    rawChainOK (deg ε) ((uS ε).extract 0 12) (uS ε) (((uBase ε).map Fin.val).toArray)
      (OmegaEight.wordsOf 12 []) 4 = true ∧
    rawOrbitSizes (deg ε) (uS ε) (((uBase ε).map Fin.val).toArray) = uSizes ε := by
  have h := (modelChecks ε).1
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem card_PQm (ε : Eps) : Nat.card (PQm ε) = 64 * (oBound ε / 2) := by
  rw [PQm, pQ, ofArrays_card (by norm_num) (pChain_ok ε).1, (pChain_ok ε).2]
  cases ε <;> rfl

theorem card_UQm (ε : Eps) : Nat.card (UQm ε) = 4096 := by
  rw [UQm, uQ, ofArrays_card (by norm_num) (uChain_ok ε).1, (uChain_ok ε).2]
  cases ε <;> rfl

theorem memP_iff {ε : Eps} {g : Array ℕ} {G : Equiv.Perm (Fin (deg ε))} (hG : Rep (deg ε) g G) :
    memP ε g = true ↔ G ∈ PQm ε := by
  have := ofArrays_mem_iff (hn := one_le_deg ε) (hk := by rw [pS_size]; omega)
    (hb := by cases ε <;> decide) (by norm_num) (pChain_ok ε).1 hG
  cases ε <;> exact this

theorem memU_iff {ε : Eps} {g : Array ℕ} {G : Equiv.Perm (Fin (deg ε))} (hG : Rep (deg ε) g G) :
    memU ε g = true ↔ G ∈ UQm ε := by
  have := ofArrays_mem_iff (hn := one_le_deg ε) (hk := by rw [uS_size])
    (hb := by cases ε <;> decide) (by norm_num) (uChain_ok ε).1 hG
  cases ε <;> exact this


theorem psiT_eq (ε : Eps) {y : ℕ} (hy : y < 64) : psiT ε y = psiArr ε y := by
  cases ε <;> simp [psiT, psiTab, psiTabPlus, psiTabMinus, Array.getD, hy]

theorem basic_parts (ε : Eps) :
    (∀ y < 64, isInvA (deg ε) (psiArr ε y) (invCand (deg ε) (psiArr ε y)) = true ∧
      memL ε (psiArr ε y) = true ∧ memP ε (psiArr ε y) = true ∧ memU ε (psiArr ε y) = true) ∧
    (∀ y < 64, ∀ y' < 64,
      eqA (deg ε) (psiArr ε (y ^^^ y')) (compA (deg ε) (psiArr ε y) (psiArr ε y')) = true ∧
        (y = y' ∨ eqA (deg ε) (psiArr ε y) (psiArr ε y') = false)) ∧
    (∀ i < 6, isInvA (deg ε) (pArr ε i) (invCand (deg ε) (pArr ε i)) = true ∧
      memL ε (pArr ε i) = true ∧ ∀ y < 64, eqA (deg ε) (conjA (deg ε) (pArr ε i) (psiArr ε y))
        (psiArr ε (bmulVec 6 6 (genRows ε i) y)) = true) ∧
    (∀ k < 6, isInvA (deg ε) (uArr ε k) (invCand (deg ε) (uArr ε k)) = true ∧
      memL ε (uArr ε k) = true ∧ ∀ y < 64, eqA (deg ε) (conjA (deg ε) (uArr ε k) (psiArr ε y))
        (psiArr ε (bmulVec 6 6 (urRows ε k) y)) = true) ∧
    (∀ y < 64, (∀ k < 6, bmulVec 6 6 (urRows ε k) y = y) → y = 0 ∨ y = 1) := by
  have h := (modelChecks ε).2.1
  simp only [basicCheck, Bool.and_eq_true, allLt_iff, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hb : ∀ A y, bmulVec 6 6 A y < 64 := bmulVec_lt
  refine ⟨fun y hy => ?_, fun y hy y' hy' => ?_, fun i hi => ?_, fun k hk => ?_, fun y hy hk => ?_⟩
  · have := h1 y hy
    rw [psiT_eq ε hy] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · have := h2 y hy y' hy'
    rw [psiT_eq ε hy, psiT_eq ε hy', psiT_eq ε (Nat.xor_lt_two_pow (n := 6) hy hy')] at this
    exact this
  · obtain ⟨⟨hi1, hi2⟩, hi3⟩ := h3 i hi
    refine ⟨hi1, hi2, fun y hy => ?_⟩
    have := hi3 y hy
    rwa [psiT_eq ε hy, psiT_eq ε (hb _ _)] at this
  · obtain ⟨⟨hk1, hk2⟩, hk3⟩ := h4 k hk
    refine ⟨hk1, hk2, fun y hy => ?_⟩
    have := hk3 y hy
    rwa [psiT_eq ε hy, psiT_eq ε (hb _ _)] at this
  · rcases h5 y hy with (h | h) | h
    · have h' : (allLt 6 fun k => bmulVec 6 6 (urRows ε k) y == y) = true :=
        allLt_iff.2 fun k hk' => by simp [hk k hk']
      rw [h] at h'
      exact absurd h' (by decide)
    · exact Or.inl h
    · exact Or.inr h

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
