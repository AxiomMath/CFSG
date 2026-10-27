module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenClassical
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPSLSix
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPSpThree
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPSUThree
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPSUEven
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPOmegaPlus
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPSUFour
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPOmegaPlusEight

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem isExcRow_PSL {n f₀ : ℕ} (h : IsExcRow .PSL n f₀) : n = 6 ∧ f₀ = 1 := by
  obtain ⟨hf, h | h | h | h⟩ := h
  · exact ⟨h.2, hf⟩
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)

theorem isExcRow_PSp {n f₀ : ℕ} (h : IsExcRow .PSp n f₀) : n = 3 ∧ f₀ = 1 := by
  obtain ⟨hf, h | h | h | h⟩ := h
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact ⟨h.2, hf⟩
  · exact absurd h.1 (by decide)

theorem isExcRow_POmegaPlus {n f₀ : ℕ} (h : IsExcRow .POmegaPlus n f₀) : n = 4 ∧ f₀ = 1 := by
  obtain ⟨hf, h | h | h | h⟩ := h
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact ⟨h.2, hf⟩

theorem psu_rows_cover {n f₀ : ℕ} (h : ¬ (Odd n ∧ ¬ IsExcRow .PSU n f₀)) :
    ((Even n ∧ ¬ IsExcRow .PSU n f₀) ∨ (n = 3 ∧ f₀ = 1)) ∨ (n = 4 ∧ f₀ = 1) := by
  by_cases hexc : IsExcRow .PSU n f₀
  · obtain ⟨hf, h1 | h1 | h1 | h1⟩ := hexc
    · exact absurd h1.1 (by decide)
    · rcases h1.2 with h3 | h4
      · exact Or.inl (Or.inr ⟨h3, hf⟩)
      · exact Or.inr ⟨h4, hf⟩
    · exact absurd h1.1 (by decide)
    · exact absurd h1.1 (by decide)
  · by_cases hodd : Odd n
    · exact absurd ⟨hodd, hexc⟩ h
    · exact Or.inl (Or.inl ⟨Nat.not_odd_iff_even.mp hodd, hexc⟩)

theorem overgroupLocalAt_PSL_final (hOver : CFSG.Quasithin.AsLieTwoOvergroups) :
    OvergroupLocalAt .PSL :=
  overgroupLocalAt_PSL hOver
    ((overgroupLocalWhen_PSL_six hOver).mono fun _ _ h => isExcRow_PSL h)

theorem overgroupLocalAt_PSp_final (hOver : CFSG.Quasithin.AsLieTwoOvergroups)
    (hLie : LieOrderFormulasInput) : OvergroupLocalAt .PSp :=
  overgroupLocalAt_PSp hOver hLie
    ((overgroupLocalWhen_PSp_three hOver).mono fun _ _ h => isExcRow_PSp h)

theorem overgroupLocalAt_PSU_final
    (hOver : CFSG.Quasithin.AsLieTwoOvergroups) (hLie : LieOrderFormulasInput) :
    OvergroupLocalAt .PSU := by
  have hEven : OvergroupLocalWhen .PSU (fun n f₀ => Even n ∧ ¬ IsExcRow .PSU n f₀) :=
    overgroupLocalWhen_of_twoLocalWhen hOver (twoLocalWhen_PSU_even hLie)
  have hThree : OvergroupLocalWhen .PSU (fun n f₀ => n = 3 ∧ f₀ = 1) :=
    overgroupLocalWhen_PSU_three hLie
  have hAB : OvergroupLocalWhen .PSU
      (fun n f₀ => (Even n ∧ ¬ IsExcRow .PSU n f₀) ∨ (n = 3 ∧ f₀ = 1)) :=
    OvergroupLocalWhen.of_or hEven hThree fun _ _ h => h
  exact overgroupLocalAt_PSU hOver hLie
    (OvergroupLocalWhen.of_or hAB (overgroupLocalWhen_PSU_four hOver)
      fun _ _ h => psu_rows_cover h)

theorem overgroupLocalAt_POmegaPlus_final (hOver : CFSG.Quasithin.AsLieTwoOvergroups)
    (hLie : LieOrderFormulasInput) : OvergroupLocalAt .POmegaPlus :=
  overgroupLocalAt_of_when (IsExcRow .POmegaPlus)
    ((overgroupLocalWhen_POmegaPlus_eight hOver).mono fun _ _ h => isExcRow_POmegaPlus h)
    (overgroupLocalWhen_of_twoLocalWhen hOver (twoLocalWhen_POmegaPlus hLie))

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
