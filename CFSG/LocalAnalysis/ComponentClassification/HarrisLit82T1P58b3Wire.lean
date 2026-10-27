module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BRow
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LAt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LSL
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LSp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOdd
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

namespace P58b3

theorem harris82Lemma58bThreeRow_of_not_admissible {τ : StatedLieTag} {n : ℕ}
    (h : ∀ f : ℕ, ¬ StatedLieAdmissible τ n 3 f) : Harris82Lemma58bThreeRow τ n := by
  intro G _ _ z₁ z₂ _ _ _ _ L₁ _ K _ _ _ _ _ _ _ _ _ _ _ f hm
  exact (h f (P58b.admissible_of_lieModel hm)).elim

theorem harris82Lemma58bThreeRow_of_one (h51E4 : Harris82Lemma51E4) {τ : StatedLieTag} {n : ℕ}
    (h : Harris82Lemma58bThreeRowAt τ n 1) : Harris82Lemma58bThreeRow τ n :=
  harris82Lemma58bThreeRow_of_at fun f hf => by
    rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | h2
    · exact h
    · exact harris82Lemma58bThreeRowAt_of_two_le h51E4 h2

end P58b3

open P58b3 in
theorem harris82Lemma58bThree_of_rowsAt
    (h51E4 : Harris82Lemma51E4) (hPSL4 : Harris82Lemma58bThreeRowAt .PSL 4 1)
    (hPSU4 : Harris82Lemma58bThreeRowAt .PSU 4 1) (hPSp2 : Harris82Lemma58bThreeRowAt .PSp 2 1)
    (hPSU : ∀ n : ℕ, Even n → 6 ≤ n → Harris82Lemma58bThreeRowAt .PSU n 1)
    (hPlus : ∀ n : ℕ, 4 ≤ n → Harris82Lemma58bThreeRowAt .POmegaPlus n 1)
    (hMinus : ∀ n : ℕ, 4 ≤ n → Harris82Lemma58bThreeRowAt .POmegaMinus n 1)
    (hE7 : Harris82Lemma58bThreeRowAt .E7 0 1) : Harris82Lemma58bThree := by
  have hGA : TBLit.GriessMultipliersAllModels := TBLit.griessMultipliersAllModels_holds
  have hTB : CFSG.TauCetiBridge.TypewiseBridges := CFSG.TauCetiBridge.typewiseBridges
  refine harris82Lemma58bThree_of_rows harris82Lemma51eOdd_holds hGA fun τ n => ?_
  have hexc : ∀ τ ∈ ({.G2, .F4, .E6, .E8, .twistedE6, .trialityD4, .twistedG2} :
      Finset StatedLieTag), Harris82Lemma58bThreeRow τ n :=
    fun τ hτ => harris82Lemma58bThreeRow_exc hGA hTB hτ n
  cases τ with
  | PSL =>
    rcases Nat.even_or_odd n with he | ho
    · rcases (show n = 0 ∨ n = 2 ∨ n = 4 ∨ 6 ≤ n by obtain ⟨k, hk⟩ := he; omega) with
        h0 | h2 | h4 | h6
      · subst h0
        exact harris82Lemma58bThreeRow_of_not_admissible fun f h => by
          obtain ⟨-, -, h⟩ := h
          exact absurd h.1 (by norm_num)
      · subst h2
        exact harris82Lemma58bThreeRow_PSL_two
      · subst h4
        exact harris82Lemma58bThreeRow_of_one h51E4 hPSL4
      · exact harris82Lemma58bThreeRow_PSL_of_six_le h51E4 h6
    · exact harris82Lemma58bThreeRow_PSL_odd hGA hTB ho
  | PSU =>
    rcases Nat.even_or_odd n with he | ho
    · rcases (show n ≤ 2 ∨ n = 4 ∨ 6 ≤ n by obtain ⟨k, hk⟩ := he; omega) with h2 | h4 | h6
      · exact harris82Lemma58bThreeRow_of_not_admissible fun f h => by
          obtain ⟨-, -, h⟩ := h
          exact absurd h.1 (by omega)
      · subst h4
        exact harris82Lemma58bThreeRow_of_one h51E4 hPSU4
      · exact harris82Lemma58bThreeRow_of_one h51E4 (hPSU n he h6)
    · exact harris82Lemma58bThreeRow_PSU_odd hGA hTB ho
  | PSp =>
    rcases (show n ≤ 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
    · exact harris82Lemma58bThreeRow_of_not_admissible fun f h => by
        obtain ⟨-, -, h⟩ := h
        exact absurd h.1 (by omega)
    · subst h2
      exact harris82Lemma58bThreeRow_of_one h51E4 hPSp2
    · exact harris82Lemma58bThreeRow_PSp_of_three_le h51E4 h3
  | POmegaOdd =>
    exact harris82Lemma58bThreeRow_POmegaOdd_of hGA fun f hf =>
      harris82Lemma58bThreeRowAt_of_two_le h51E4 hf
  | POmegaPlus =>
    rcases (show n < 4 ∨ 4 ≤ n by omega) with h3 | h4
    · exact harris82Lemma58bThreeRow_of_not_admissible fun f h => by
        obtain ⟨-, -, h⟩ := h
        exact absurd (show 4 ≤ n from h) (by omega)
    · exact harris82Lemma58bThreeRow_of_one h51E4 (hPlus n h4)
  | POmegaMinus =>
    rcases (show n < 4 ∨ 4 ≤ n by omega) with h3 | h4
    · exact harris82Lemma58bThreeRow_of_not_admissible fun f h => by
        obtain ⟨-, -, h⟩ := h
        exact absurd (show 4 ≤ n from h) (by omega)
    · exact harris82Lemma58bThreeRow_of_one h51E4 (hMinus n h4)
  | G2 => exact hexc _ (by simp)
  | F4 => exact hexc _ (by simp)
  | E6 => exact hexc _ (by simp)
  | E7 =>
    rcases eq_or_ne n 0 with h0 | h0
    · subst h0
      exact harris82Lemma58bThreeRow_of_one h51E4 hE7
    · exact harris82Lemma58bThreeRow_of_not_admissible fun f h => by
        obtain ⟨-, -, h⟩ := h
        exact h0 h
  | E8 => exact hexc _ (by simp)
  | twistedE6 => exact hexc _ (by simp)
  | trialityD4 => exact hexc _ (by simp)
  | twistedB2 => exact harris82Lemma58bThreeRow_char_two (Or.inl rfl) n
  | twistedG2 => exact hexc _ (by simp)
  | twistedF4 => exact harris82Lemma58bThreeRow_char_two (Or.inr (Or.inl rfl)) n
  | Tits => exact harris82Lemma58bThreeRow_char_two (Or.inr (Or.inr rfl)) n

end CFSG.ComponentClassification.HarrisLit.T1
