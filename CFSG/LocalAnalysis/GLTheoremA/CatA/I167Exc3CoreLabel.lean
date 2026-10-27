module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167FieldDict
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SLOrder
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


theorem exc3core_t167_label {G : Type} [Group G] {f : ℕ} (h : catalogIs G (T167Idx f)) :
    (f = 1 ∧ ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ CFSG.Blueprint.LieModel G .PSL n 2 1) ∨
    (f = 1 ∧ ∃ n : ℕ, Even n ∧ 6 ≤ n ∧ CFSG.Blueprint.LieModel G .POmegaMinus n 2 1) ∨
    (1 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧ ∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ (f = 1 → 5 ≤ n) ∧
      ((4 ≤ n ∧ CFSG.Blueprint.LieModel G .POmegaPlus n 2 f) ∨
        (n = 3 ∧ 2 ≤ f ∧ CFSG.Blueprint.LieModel G .PSL 4 2 f))) := by
  obtain ⟨i, hi, e⟩ := h
  unfold T167Idx at hi
  rcases hi with ⟨hf, n, hn, hn5, his⟩ | ⟨hf, n, hn, hn6, his⟩ | ⟨n, hn, hn3, hnk, hf, hdiv, his⟩
  · exact Or.inl ⟨hf, n, hn, hn5, fld_lieModel_of_isLnA hn5 ⟨i, his, e⟩⟩
  · exact Or.inr (Or.inl ⟨hf, n, hn, hn6, fld_lieModel_of_isOmMA (by omega) ⟨i, his, e⟩⟩)
  · exact Or.inr (Or.inr ⟨hf, hdiv, n, hn, hn3, hnk, fld_lieModel_of_isOmPA hf hn3 hnk ⟨i, his, e⟩⟩)

theorem exc3core_type_det {G : Type} [Group G] {f : ℕ} (h : catalogIs G (T167Idx f))
    {t : StatedLieTag} {ν g : ℕ} (hm : CFSG.Blueprint.LieModel G t ν 2 g) :
    (t = .PSL ∧ Odd ν ∧ 5 ≤ ν ∧ g = 1 ∧ f = 1) ∨
    (t = .POmegaMinus ∧ Even ν ∧ 6 ≤ ν ∧ g = 1 ∧ f = 1) ∨
    (1 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧ g = f ∧
      ((t = .POmegaPlus ∧ Odd ν ∧ 5 ≤ ν) ∨ (t = .PSL ∧ ν = 4 ∧ 2 ≤ f))) := by
  rcases exc3core_t167_label h with ⟨hf, n, hn, hn5, hm'⟩ | ⟨hf, n, hn, hn6, hm'⟩ |
    ⟨hf, hdiv, n, hn, hn3, hnk, hm'⟩
  · obtain ⟨ht, hν, hg⟩ :=
      CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (m := n) (f := 1) (by omega) hm' hm
    exact Or.inl ⟨ht, hν ▸ hn, by omega, hg, hf⟩
  · obtain ⟨ht, hν, hg⟩ :=
      CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique (s := .POmegaMinus) (m := n) (f := 1) (Or.inr rfl) hm' hm
    exact Or.inr (Or.inl ⟨ht, hν ▸ hn, by omega, hg, hf⟩)
  · rcases hm' with ⟨hn4, hm'⟩ | ⟨rfl, hf2, hm'⟩
    · obtain ⟨ht, hν, hg⟩ :=
        CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique (s := .POmegaPlus) (m := n) (f := f) (Or.inl rfl) hm' hm
      obtain ⟨k, hk⟩ := hn
      exact Or.inr (Or.inr ⟨hf, hdiv, hg, Or.inl ⟨ht, hν ▸ ⟨k, hk⟩, by omega⟩⟩)
    · obtain ⟨ht, hν, hg⟩ :=
        CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (m := 4) (f := f) (by omega) hm' hm
      exact Or.inr (Or.inr ⟨hf, hdiv, hg, Or.inr ⟨ht, hν, hf2⟩⟩)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
