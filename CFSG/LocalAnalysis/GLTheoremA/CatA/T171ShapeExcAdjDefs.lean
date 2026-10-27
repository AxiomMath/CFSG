module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
open scoped Pointwise

@[expose] def ExcKernelCompAction :
    Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀), p₀.Prime → p₀ ≠ 2 →
    ∀ {p : ℕ}, p.Prime → p ≠ 2 →
    (τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ {a : Fin τ.rank → Lˣ}, rootDiagUnit τ a ∈ S.D.torus →
    (∀ j, a j ^ p = 1) → rootDiagUnit τ a ^ p = 1 → rootDiagUnit τ a ≠ 1 →
    (τ = .G2 → 4 ≤ S.D.q) →
    (i : KernelComponent (rootCharHom a)) →
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 360 →
    ∀ {y : ModGL τ L}
      (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
      (hyF : S.D.step y = y)
      (hyStab : MulAut.conj y ∈ subgroupStabAut
        (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
      centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
            ⟨MulAut.conj y, hyStab⟩) ∈
        innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
