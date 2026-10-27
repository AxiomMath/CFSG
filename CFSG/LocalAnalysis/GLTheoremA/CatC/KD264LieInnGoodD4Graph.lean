module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodD4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295e
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectSolv

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.LieType.SeitzGeneration.ExcWideThree

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem d4GraphPerfect_holds : D4GraphPerfect := by
  intro F _ _ hF3 hF2 g a ε hε hα3
  have hK4 := four_le_card_of_ringChar_ne_three hF3 hF2
  have : Finite (ModGL Tag.D4 F) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 F) := Subtype.finite
  have hT : D4ElemType (MulAut.conj g * (exactNormalAut Tag.D4 F a 1 0 * d4Graph F ε))
      (fun ε σ => ε ≠ 0 ∧ σ = 1) :=
    ⟨g, a, 1, ε, by omega, one_pow 3, ⟨by omega, rfl⟩, rfl⟩
  by_contra hcon
  exact GLTheoremB.MovingAround.Inputs295e.not_isPSolvable_fixedSubgroup_graphType hF3 hK4 hα3 hT
    (AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isPSolvable_three_of_no_perfect _
      fun J hJ hJJ h3 => hcon ⟨J, fun x hx => hJ hx, hJJ, h3⟩)

theorem lieInnGood_D4 :
    LieInnGood fun d => ∃ q, d = .D 4 q :=
  lieInnGood_D4_of_graph d4GraphPerfect_holds

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
