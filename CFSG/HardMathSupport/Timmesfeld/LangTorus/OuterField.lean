module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

set_option linter.unusedSectionVars false


section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem noFrobeniusInner_of_big_any (S : LangSetup τ L p) (hτ : τ ≠ .G2)
    (hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E)
    (h : HasBigAnyComponent S D₁) : NoFrobeniusInner S D₁ := by
  intro r f j _ hr hqf hj0 hjf z hz
  obtain ⟨a, haD, ha1, i, hbig, -⟩ := h
  exact outer_false_of_component_fixed_by_twist_of_E S hτ (hD₁E haD) i hr hqf hq4 hj0 hjf z
    (fun x hx => hz x (Or.inl ⟨a, haD, ha1, i, hbig, hx⟩))

end Main

end CFSG.HardMathSupport.Timmesfeld.LangTorus
