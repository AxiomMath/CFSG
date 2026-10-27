module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9E1
public import Certificates.Certificate26791

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.LieType.Multipliers CFSG.Blueprint
  CFSG.Blueprint.NativeSporadic

@[expose] def fyRe : HSCover := wordVal hsGens fyRWord

@[expose] def fyCe (i : ℕ) : HSCover := wordVal hsGens (fyC i)

@[expose] def fyAe : HSCover := wordVal hsGens fyAWord

@[expose] def fyLe : HSCover := wordVal hsGens fyLWord

theorem wordVal_append' (u v : List ℕ) :
    wordVal hsGens (u ++ v) = wordVal hsGens u * wordVal hsGens v := by
  simp [wordVal, List.map_append, List.prod_append]

theorem wordVal_nil' : wordVal hsGens ([] : List ℕ) = 1 := by simp [wordVal]

theorem fyRWord_letters : ∀ l ∈ fyRWord, 1 ≤ l ∧ l ≤ 6 := by decide

theorem fyAWord_letters : ∀ l ∈ fyAWord, 1 ≤ l ∧ l ≤ 6 := by decide

theorem fyLWord_letters : ∀ l ∈ fyLWord, 1 ≤ l ∧ l ≤ 6 := by decide

theorem fyCWords_letters : ∀ w ∈ fyCWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 6 := by decide

theorem fyC_letters (i : ℕ) : ∀ l ∈ fyC i, 1 ≤ l ∧ l ≤ 6 := by
  by_cases hi : i < fyCWords.length
  · unfold fyC
    rw [List.getD_eq_getElem _ _ hi]
    exact fyCWords_letters _ (List.getElem_mem _)
  · unfold fyC
    rw [List.getD_eq_default _ _ (by omega)]
    intro l hl
    simp at hl

section Facts


theorem HSCtx.fy_eq (hΛ : HSCtx) {u v : List ℕ} (hu : ∀ l ∈ u, 1 ≤ l ∧ l ≤ 6)
    (hv : ∀ l ∈ v, 1 ≤ l ∧ l ≤ 6) (h : fyEq u v = true) :
    wordVal hsGens u = wordVal hsGens v :=
  hΛ.rho_injective ((tblEq_iff_eq (rep_rho_wordVal u hu) (rep_rho_wordVal v hv)).1 h)

theorem HSCtx.fy_ne (_hΛ : HSCtx) {u v : List ℕ} (hu : ∀ l ∈ u, 1 ≤ l ∧ l ≤ 6)
    (hv : ∀ l ∈ v, 1 ≤ l ∧ l ≤ 6) (h : fyEq u v = false) :
    wordVal hsGens u ≠ wordVal hsGens v := by
  intro e
  have := (tblEq_iff_eq (rep_rho_wordVal u hu) (rep_rho_wordVal v hv)).2
    (congrArg harRhoHom e)
  rw [fyEq] at h
  rw [h] at this
  exact Bool.false_ne_true this

theorem HSCtx.fy_facts (hΛ : HSCtx) :
    fyRe ^ 3 = 1 ∧ fyRe ≠ 1 ∧
    (∀ i < 4, fyCe i * fyCe i = tL ∧ fyCe i * fyRe = fyRe * fyCe i ∧
      fyCe i * fyAe = tL * fyAe * hΛ.sigma (fyCe i)) ∧
    (∀ i < 3, fyCe i * fyCe (i + 1) * fyCe i = fyCe (i + 1) * fyCe i * fyCe (i + 1)) ∧
    fyCe 0 * fyCe 2 = fyCe 2 * fyCe 0 ∧ fyCe 0 * fyCe 3 = fyCe 3 * fyCe 0 ∧
    fyCe 1 * fyCe 3 = fyCe 3 * fyCe 1 ∧
    fyAe * hΛ.sigma fyAe = 1 ∧ fyAe * hΛ.sigma fyRe = fyRe * fyAe ∧
    fyCe 0 ≠ fyCe 1 ∧ fyCe 2 ≠ fyCe 0 ∧ fyCe 2 ≠ fyCe 0 * tL ∧
    fyLe * fyAe = fyAe * hΛ.sigma (fyCe 0) * tL * hΛ.sigma fyLe := by
  have h := (Certificates.certificate26791 : fyOK = true)
  simp only [fyOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  have hs : ∀ {w : List ℕ}, (∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) → hΛ.sigma (wordVal hsGens w) =
      wordVal hsGens (sigWord w) := fun _ => hΛ.sigma_wordVal _
  have hsl : ∀ {w : List ℕ}, (∀ l ∈ w, 1 ≤ l ∧ l ≤ 6) → ∀ l ∈ sigWord w, 1 ≤ l ∧ l ≤ 6 :=
    fun hw => sigWord_letters hw
  have htW : ∀ l ∈ tWord, 1 ≤ l ∧ l ≤ 6 := tWord_letters
  have hnil : ∀ l ∈ ([] : List ℕ), 1 ≤ l ∧ l ≤ 6 := by simp
  have happ : ∀ {u v : List ℕ}, (∀ l ∈ u, 1 ≤ l ∧ l ≤ 6) → (∀ l ∈ v, 1 ≤ l ∧ l ≤ 6) →
      ∀ l ∈ u ++ v, 1 ≤ l ∧ l ≤ 6 := by
    intro u v hu hv l hl
    rcases List.mem_append.1 hl with h | h
    · exact hu l h
    · exact hv l h
  have hR := fyRWord_letters
  have hA := fyAWord_letters
  have hL := fyLWord_letters
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hΛ.fy_eq (happ (happ hR hR) hR) hnil h1
    simp only [wordVal_append', wordVal_nil'] at this
    show wordVal hsGens fyRWord ^ 3 = 1
    rw [pow_succ, pow_two]
    exact this
  · intro e
    have := hΛ.fy_ne hR hnil (by simpa using h2)
    exact this e
  · intro i hi
    have hi' : i ∈ List.range 4 := List.mem_range.2 hi
    obtain ⟨⟨e1, e2⟩, e3⟩ := h3 i hi
    have hc := fyC_letters i
    refine ⟨?_, ?_, ?_⟩
    · have := hΛ.fy_eq (happ hc hc) htW e1
      simpa [wordVal_append', fyCe, tL] using this
    · have := hΛ.fy_eq (happ hc hR) (happ hR hc) e2
      simpa [wordVal_append', fyCe, fyRe] using this
    · have := hΛ.fy_eq (happ hc hA) (happ (happ htW hA) (hsl hc)) e3
      simp only [wordVal_append'] at this
      rw [← hs hc] at this
      exact this
  · intro i hi
    have hc := fyC_letters i
    have hc' := fyC_letters (i + 1)
    have := hΛ.fy_eq (happ (happ hc hc') hc) (happ (happ hc' hc) hc') (h4 i hi)
    simpa [wordVal_append', fyCe, mul_assoc] using this
  · have := hΛ.fy_eq (happ (fyC_letters 0) (fyC_letters 2))
      (happ (fyC_letters 2) (fyC_letters 0)) h5
    simpa [wordVal_append', fyCe] using this
  · have := hΛ.fy_eq (happ (fyC_letters 0) (fyC_letters 3))
      (happ (fyC_letters 3) (fyC_letters 0)) h6
    simpa [wordVal_append', fyCe] using this
  · have := hΛ.fy_eq (happ (fyC_letters 1) (fyC_letters 3))
      (happ (fyC_letters 3) (fyC_letters 1)) h7
    simpa [wordVal_append', fyCe] using this
  · have := hΛ.fy_eq (happ hA (hsl hA)) hnil h8
    simp only [wordVal_append', wordVal_nil'] at this
    rw [← hs hA] at this
    exact this
  · have := hΛ.fy_eq (happ hA (hsl hR)) (happ hR hA) h9
    simp only [wordVal_append'] at this
    rw [← hs hR] at this
    exact this
  · exact hΛ.fy_ne (fyC_letters 0) (fyC_letters 1) (by simpa using h10)
  · exact hΛ.fy_ne (fyC_letters 2) (fyC_letters 0) (by simpa using h11)
  · have := hΛ.fy_ne (fyC_letters 2) (happ (fyC_letters 0) htW) (by simpa using h12)
    simpa [wordVal_append', fyCe, tL] using this
  · have := hΛ.fy_eq (happ hL hA) (happ (happ (happ hA (hsl (fyC_letters 0))) htW) (hsl hL)) h13
    simp only [wordVal_append'] at this
    rw [← hs (fyC_letters 0), ← hs hL] at this
    exact this

end Facts

end CFSG.EvenSporadicStandard.TwoHS
