module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9E1
public import Certificates.Certificate26824

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.LieType.Multipliers CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic

@[expose] def mzR : HSCover := wordVal hsGens mzRW

@[expose] def mzA : HSCover := wordVal hsGens mzAW

@[expose] def mzP : HSCover := wordVal hsGens mzPW

theorem wordVal_append_mz (u v : List ℕ) :
    wordVal hsGens (u ++ v) = wordVal hsGens u * wordVal hsGens v := by
  simp [wordVal, List.map_append, List.prod_append]

theorem wordVal_nil_mz : wordVal hsGens ([] : List ℕ) = 1 := by simp [wordVal]

theorem wordVal_rptW (w : List ℕ) (k : ℕ) : wordVal hsGens (rptW w k) = wordVal hsGens w ^ k := by
  induction k with
  | zero => simp [rptW, wordVal_nil_mz]
  | succ k ih =>
    have : rptW w (k + 1) = w ++ rptW w k := by simp [rptW, List.replicate_succ]
    rw [this, wordVal_append_mz, ih, pow_succ']

theorem wordVal_kapW (c : List ℕ) : wordVal hsGens (kapW c) = kapL c := by
  simp only [kapW, kapL, wordVal_append_mz, wordVal_rptW, bet, tL, betaW]

theorem rptW_letters {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) (k : ℕ) :
    ∀ l ∈ rptW w k, 1 ≤ l ∧ l ≤ 6 := by
  intro l hl
  simp only [rptW, List.mem_flatten, List.mem_replicate] at hl
  obtain ⟨w', ⟨-, rfl⟩, hl⟩ := hl
  exact hw l hl

theorem append_letters {u v : List ℕ} (hu : ∀ l ∈ u, 1 ≤ l ∧ l ≤ 6) (hv : ∀ l ∈ v, 1 ≤ l ∧ l ≤ 6) :
    ∀ l ∈ u ++ v, 1 ≤ l ∧ l ≤ 6 := by
  intro l hl
  rcases List.mem_append.1 hl with h | h
  · exact hu l h
  · exact hv l h

theorem betaW_letters (j : ℕ) : ∀ l ∈ betaW j, 1 ≤ l ∧ l ≤ 6 := betaWords_getD_letters j

theorem kapW_letters (c : List ℕ) : ∀ l ∈ kapW c, 1 ≤ l ∧ l ≤ 6 :=
  append_letters (append_letters (append_letters (rptW_letters (betaW_letters 0) _)
    (rptW_letters (betaW_letters 1) _)) (rptW_letters tWord_letters _))
    (rptW_letters (betaW_letters 2) _)

theorem mzRW_letters : ∀ l ∈ mzRW, 1 ≤ l ∧ l ≤ 6 := by decide

theorem mzAW_letters : ∀ l ∈ mzAW, 1 ≤ l ∧ l ≤ 6 := by decide

theorem mzPW_letters : ∀ l ∈ mzPW, 1 ≤ l ∧ l ≤ 6 := by decide

section Facts


theorem HSCtx.mz_eq (hΛ : HSCtx) {u v : List ℕ} (hu : ∀ l ∈ u, 1 ≤ l ∧ l ≤ 6)
    (hv : ∀ l ∈ v, 1 ≤ l ∧ l ≤ 6) (h : mzEq u v = true) :
    wordVal hsGens u = wordVal hsGens v :=
  hΛ.rho_injective ((tblEq_iff_eq (rep_rho_wordVal u hu) (rep_rho_wordVal v hv)).1 h)

theorem HSCtx.mz_ne (_hΛ : HSCtx) {u v : List ℕ} (hu : ∀ l ∈ u, 1 ≤ l ∧ l ≤ 6)
    (hv : ∀ l ∈ v, 1 ≤ l ∧ l ≤ 6) (h : mzEq u v = false) :
    wordVal hsGens u ≠ wordVal hsGens v := by
  intro e
  have := (tblEq_iff_eq (rep_rho_wordVal u hu) (rep_rho_wordVal v hv)).2
    (congrArg harRhoHom e)
  rw [mzEq] at h
  rw [h] at this
  exact Bool.false_ne_true this


theorem HSCtx.mz_facts (hΛ : HSCtx) :
    mzR ^ 3 = 1 ∧ mzR ≠ 1 ∧
    (∀ j < 3, mzR * bet j = kapL (colOf mzRData ([0, 1, 3].getD j 0)) * mzR) ∧
    mzA * hΛ.sigma mzA = 1 ∧
    (∀ j < 3, mzA * hΛ.sigma (bet j) = bet j ^ 3 * mzA) ∧
    mzR * mzA = mzA * hΛ.sigma mzR ∧
    mzP ^ 3 = 1 ∧ mzP ≠ 1 ∧ mzP ≠ mzR ∧ mzP ≠ mzR * mzR ∧ mzP * mzR = mzR * mzP ∧
    mzP * mzA = mzA * hΛ.sigma mzP ∧
    gamma1L * mzA = kapL mzEps * mzA * hΛ.sigma gamma1L ∧
    gamma2L * hΛ.sigma mzA = kapL mzEps * mzA * hΛ.sigma gamma2L := by
  have h := (Certificates.certificate26824 : mzOK = true)
  simp only [mzOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩ := h
  have hs : ∀ {w : List ℕ}, (∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) → hΛ.sigma (wordVal hsGens w) =
      wordVal hsGens (sigWord w) := fun _ => hΛ.sigma_wordVal _
  have hsl : ∀ {w : List ℕ}, (∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) → ∀ l ∈ sigWord w, 1 ≤ l ∧ l ≤ 6 :=
    fun hw => sigWord_letters hw
  have hnil : ∀ l ∈ ([] : List ℕ), 1 ≤ l ∧ l ≤ 6 := by simp
  have hR := mzRW_letters
  have hA := mzAW_letters
  have hP := mzPW_letters
  have hg1 := gamma1Word_letters
  have hg2 := gamma2Word_letters
  have happ := @append_letters
  have hmz : ∀ {u v : List ℕ}, (∀ l ∈ u, 1 ≤ l ∧ l ≤ 6) → (∀ l ∈ v, 1 ≤ l ∧ l ≤ 6) →
      mzEq u v = true → wordVal hsGens u = wordVal hsGens v := fun hu hv h => hΛ.mz_eq hu hv h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hmz (happ (happ hR hR) hR) hnil h1
    simp only [wordVal_append_mz, wordVal_nil_mz] at this
    show wordVal hsGens mzRW ^ 3 = 1
    rw [pow_succ, pow_two]
    exact this
  · intro e
    have := hΛ.mz_ne hR hnil (by simpa using h2)
    exact this e
  · intro j hj
    have := hmz (happ hR (betaW_letters j)) (happ (kapW_letters _) hR) (h3 j hj)
    simpa only [wordVal_append_mz, wordVal_kapW, mzR, bet, betaW] using this
  · have := hmz (happ hA (hsl hA)) hnil h4
    simp only [wordVal_append_mz, wordVal_nil_mz] at this
    rw [← hs hA] at this
    exact this
  · intro j hj
    have := hmz (happ hA (hsl (betaW_letters j))) (happ (rptW_letters (betaW_letters j) 3) hA)
      (h5 j hj)
    simp only [wordVal_append_mz, wordVal_rptW] at this
    rw [← hs (betaW_letters j)] at this
    simpa only [mzA, bet, betaW] using this
  · have := hmz (happ hR hA) (happ hA (hsl hR)) h6
    simp only [wordVal_append_mz] at this
    rw [← hs hR] at this
    exact this
  · have := hmz (happ (happ hP hP) hP) hnil h7
    simp only [wordVal_append_mz, wordVal_nil_mz] at this
    show wordVal hsGens mzPW ^ 3 = 1
    rw [pow_succ, pow_two]
    exact this
  · intro e
    have := hΛ.mz_ne hP hnil (by simpa using h8)
    exact this e
  · exact hΛ.mz_ne hP hR (by simpa using h9)
  · have := hΛ.mz_ne hP (happ hR hR) (by simpa using h10)
    simpa [wordVal_append_mz, mzR, mzP] using this
  · have := hmz (happ hP hR) (happ hR hP) h11
    simpa [wordVal_append_mz, mzR, mzP] using this
  · have := hmz (happ hP hA) (happ hA (hsl hP)) h12
    simp only [wordVal_append_mz] at this
    rw [← hs hP] at this
    exact this
  · have := hmz (happ hg1 hA) (happ (happ (kapW_letters _) hA) (hsl hg1)) h13
    simp only [wordVal_append_mz, wordVal_kapW] at this
    rw [← hs hg1] at this
    exact this
  · have := hmz (happ hg2 (hsl hA)) (happ (happ (kapW_letters _) hA) (hsl hg2)) h14
    simp only [wordVal_append_mz, wordVal_kapW] at this
    rw [← hs hg2, ← hs hA] at this
    exact this

end Facts

end CFSG.EvenSporadicStandard.TwoHS
