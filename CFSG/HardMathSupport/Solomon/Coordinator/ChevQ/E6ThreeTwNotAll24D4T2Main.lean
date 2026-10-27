module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Plumb

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

section Main

set_option linter.unusedSectionVars false

theorem d4t2OuterThm_holds : D4T2OuterThm := by
  intro L _ _ p₀ S hS l f hl hf hq hl3 h3 h3q a hT hap i hall hr hc hρ hnin
  exact twE6ComponentType_rational_of_outer_d4 S hS hl hf hq hl3 h3 h3q hT hap i hall hr hc hρ
    hnin

theorem twE6LineStructureAt_of_d4 (hM : D4T2ModelGen)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hd : TwE6LineDim K σ f 30) : TwE6LineStructureAt K σ E f :=
  ⟨twE6LineComponentsAt_of_d4 d4t2OuterThm_holds hE hf hf1 hd,
    twE6LineGenAt_of_model hM hE hf hf1 hd⟩

theorem twE6LineStructureD4In_of_model (hM : D4T2ModelGen) : TwE6LineStructureD4In := by
  intro K _ _ σ q E hE f hf hf1 _ hd
  exact twE6LineStructureAt_of_d4 hM hE hf hf1 hd

theorem twE6LineStructureD4Out_of_model (hM : D4T2ModelGen) : TwE6LineStructureD4Out := by
  intro K _ _ σ q E hE f hf hf1 _ hd
  exact twE6LineStructureAt_of_d4 hM hE hf hf1 hd

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
