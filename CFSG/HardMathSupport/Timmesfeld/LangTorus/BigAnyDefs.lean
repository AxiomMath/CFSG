module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.RankThree.Chevalley.SteinbergCFSmallReeCentralCover

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Defs

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def bigAnyRoots (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L)) :
    Set (Fin τ.rank → ℤ) :=
  {γ | ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ ∧ rootDiagUnit τ a ≠ 1 ∧
    ∃ i : KernelComponent (rootCharHom a),
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∧
      4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      γ ∈ componentRoots (rootCharHom a) i}

@[expose] def HasBigAnyComponent (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L)) : Prop :=
  ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ ∧ rootDiagUnit τ a ≠ 1 ∧
    ∃ i : KernelComponent (rootCharHom a),
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∧
      4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)

@[expose] def BigAnyComponentsGenerate (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L)) : Prop :=
  adjointGroup τ L ≤ rootSpan τ L (bigAnyRoots S D₁)

end Defs

end CFSG.HardMathSupport.Timmesfeld.LangTorus
