module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.NQFacts
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.ONSchreier.Native

@[expose] def relab (μ : ℕ → ℕ) (l : ℤ) : ℤ :=
  if 0 < l then ((μ (l.natAbs - 1) + 1 : ℕ) : ℤ) else -((μ (l.natAbs - 1) + 1 : ℕ) : ℤ)

theorem evalWord_append {G S : Type*} [Group G] (ι : S → G) :
    ∀ u v : List (S × Bool), Quiver.SchreierGraph.evalWord ι (u ++ v) =
      Quiver.SchreierGraph.evalWord ι u * Quiver.SchreierGraph.evalWord ι v
  | [], v => by simp [Quiver.SchreierGraph.evalWord_nil]
  | (s, b) :: u, v => by
    cases b
    · rw [List.cons_append, Quiver.SchreierGraph.evalWord_cons_false,
        Quiver.SchreierGraph.evalWord_cons_false, evalWord_append ι u v, mul_assoc]
    · rw [List.cons_append, Quiver.SchreierGraph.evalWord_cons_true,
        Quiver.SchreierGraph.evalWord_cons_true, evalWord_append ι u v, mul_assoc]

theorem ptoLetters_append (j : ℕ) (u v : List ℤ) :
    ptoLetters j (u ++ v) = ptoLetters j u ++ ptoLetters j v :=
  List.filterMap_append

theorem ptoLetters_cons' {j : ℕ} {l : ℤ} (hl0 : l ≠ 0) (hlj : l.natAbs ≤ j) (w : List ℤ) :
    ptoLetters j (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) :: ptoLetters j w := by
  simp [ptoLetters, hl0, hlj]

theorem plettersOK_cons {j : ℕ} {l : ℤ} {w : List ℤ} (h : plettersOK j (l :: w) = true) :
    (l ≠ 0 ∧ l.natAbs ≤ j) ∧ plettersOK j w = true := by
  simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  exact ⟨h.1, by simpa [plettersOK, List.all_eq_true] using h.2⟩

theorem plettersOK_relab {j k : ℕ} {μ : ℕ → ℕ} (hμ : ∀ h < k, μ h < j) :
    ∀ w : List ℤ, plettersOK k w = true → plettersOK j (w.map (relab μ)) = true
  | [], _ => rfl
  | l :: w, hw => by
    obtain ⟨⟨hl0, hlk⟩, hw⟩ := plettersOK_cons hw
    have ih := plettersOK_relab hμ w hw
    have hm := hμ (l.natAbs - 1) (by omega)
    simp only [List.map_cons, plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    refine ⟨⟨?_, ?_⟩, by simpa [plettersOK, List.all_eq_true] using ih⟩
    · unfold relab
      split_ifs <;> omega
    · unfold relab
      split_ifs <;> omega

theorem plettersOK_mono {j k : ℕ} (hjk : j ≤ k) :
    ∀ w : List ℤ, plettersOK j w = true → plettersOK k w = true
  | [], _ => rfl
  | l :: w, hw => by
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := plettersOK_cons hw
    have ih := plettersOK_mono hjk w hw
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    exact ⟨⟨hl0, by omega⟩, by simpa [plettersOK, List.all_eq_true] using ih⟩

theorem relab_id {k : ℕ} : ∀ w : List ℤ, plettersOK k w = true → w.map (relab id) = w
  | [], _ => rfl
  | l :: w, hw => by
    obtain ⟨⟨hl0, -⟩, hw⟩ := plettersOK_cons hw
    rw [List.map_cons, relab_id w hw]
    congr 1
    unfold relab
    split_ifs <;> simp only [id] <;> omega

theorem evalWord_relab {G : Type*} [Group G] {j k : ℕ} (f : ℕ → G) {μ : ℕ → ℕ}
    (hμ : ∀ h < k, μ h < j) :
    ∀ w : List ℤ, plettersOK k w = true →
      Quiver.SchreierGraph.evalWord (fun h : Fin j => f h) (ptoLetters j (w.map (relab μ))) =
        Quiver.SchreierGraph.evalWord (fun h : Fin k => f (μ h)) (ptoLetters k w)
  | [], _ => rfl
  | l :: w, hw => by
    obtain ⟨⟨hl0, hlk⟩, hw'⟩ := plettersOK_cons hw
    have ih := evalWord_relab f hμ w hw'
    have hm := hμ (l.natAbs - 1) (by omega)
    have hr0 : relab μ l ≠ 0 := by
      unfold relab
      split_ifs <;> omega
    have hrj : (relab μ l).natAbs ≤ j := by
      unfold relab
      split_ifs <;> omega
    have hra : (relab μ l).natAbs - 1 = μ (l.natAbs - 1) := by
      unfold relab
      split_ifs <;> omega
    have hrs : decide (0 < relab μ l) = decide (0 < l) := by
      unfold relab
      split_ifs with h
      · simp only [h, decide_true, decide_eq_true_eq]
        omega
      · simp only [h, decide_false, decide_eq_false_iff_not, not_lt]
        omega
    rw [List.map_cons, ptoLetters_cons' hr0 hrj, ptoLetters_cons' hl0 hlk, hrs]
    cases decide (0 < l)
    · rw [Quiver.SchreierGraph.evalWord_cons_false, Quiver.SchreierGraph.evalWord_cons_false, ih]
      simp only [hra]
    · rw [Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_cons_true, ih]
      simp only [hra]

theorem nqEv2_append {G : Type*} [Group G] (a b : G) (u v : List ℤ) :
    nqEv2 a b (u ++ v) = nqEv2 a b u * nqEv2 a b v := by
  unfold nqEv2
  rw [ptoLetters_append, evalWord_append]

theorem nqEv2_one {G : Type*} [Group G] (a b : G) : nqEv2 a b [1] = a := by
  simp [nqEv2, ptoLetters, Quiver.SchreierGraph.evalWord_cons_true,
    Quiver.SchreierGraph.evalWord_nil]

theorem evalWord_relab_two {G : Type*} [Group G] {j : ℕ} (f : ℕ → G) {μ : ℕ → ℕ}
    (h0 : μ 0 < j) (h1 : μ 1 < j) {w : List ℤ} (hw : plettersOK 2 w = true) :
    Quiver.SchreierGraph.evalWord (fun h : Fin j => f h) (ptoLetters j (w.map (relab μ))) =
      nqEv2 (f (μ 0)) (f (μ 1)) w := by
  rw [evalWord_relab f (μ := μ) (fun h hh => by interval_cases h <;> assumption) w hw]
  unfold nqEv2
  congr 1
  funext h
  fin_cases h <;> rfl

theorem evalWord_le_two {G : Type*} [Group G] {j : ℕ} (hj : 2 ≤ j) (f : ℕ → G) {w : List ℤ}
    (hw : plettersOK 2 w = true) :
    Quiver.SchreierGraph.evalWord (fun h : Fin j => f h) (ptoLetters j w) = nqEv2 (f 0) (f 1) w := by
  have e := evalWord_relab_two (j := j) f (μ := id) (by simp only [id]; omega)
    (by simp only [id]; omega) hw
  rw [relab_id w hw] at e
  exact e

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
