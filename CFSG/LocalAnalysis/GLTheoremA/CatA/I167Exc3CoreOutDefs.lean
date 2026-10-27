module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreLabel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


@[expose] def exc3core_Out (G : Type) [Group G] : Prop :=
  ∃ (t : StatedLieTag) (ν g : ℕ), CFSG.Blueprint.LieModel G t ν 2 g ∧
    ¬ ((t = .PSL ∧ Odd ν ∧ 5 ≤ ν) ∨ (t = .POmegaMinus ∧ Even ν ∧ 6 ≤ ν) ∨
      (t = .POmegaPlus ∧ Odd ν ∧ 5 ≤ ν) ∨ (t = .PSL ∧ ν = 4))


theorem exc3core_false_of_out {G : Type} [Group G] {f : ℕ} (h : catalogIs G (T167Idx f))
    (ho : exc3core_Out G) : False := by
  obtain ⟨t, ν, g, hm, hn⟩ := ho
  rcases exc3core_type_det h hm with ⟨h1, h2, h3, -, -⟩ | ⟨h1, h2, h3, -, -⟩ |
    ⟨-, -, -, ⟨h1, h2, h3⟩ | ⟨h1, h2, -⟩⟩
  · exact hn (Or.inl ⟨h1, h2, h3⟩)
  · exact hn (Or.inr (Or.inl ⟨h1, h2, h3⟩))
  · exact hn (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))
  · exact hn (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))


end CFSG.LocalAnalysis.GLTheoremA.I167

end
