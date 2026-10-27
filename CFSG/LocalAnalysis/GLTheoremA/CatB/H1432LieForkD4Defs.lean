module

public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def D4ThreeOuterCases :
    Prop :=
  ∀ {K : Type} [Field K] {f : ℕ}, Nat.card K = 3 ^ f → 1 ≤ f →
    ∀ α : MulAut (adjointGroup Tag.D4 K), α ^ 3 = 1 → α ∉ inner (adjointGroup Tag.D4 K) →
      (∃ (d : ℕ) (T : K ≃+* K) (ψ : MulAut (adjointGroup Tag.D4 K)), d * 3 = f ∧
          (∀ c, T c = c ^ 3 ^ d) ∧ (ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T ∨
            ψ * α ^ 2 * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T)) ∨
        ∀ A : Subgroup (adjointGroup Tag.D4 K), GLAPComponent 3 (fixSubgroup α) A →
          CFSG.Blueprint.LieModel (PSimple 3 A) .G2 0 3 f ∨
            ∃ f', 3 * f' = f ∧ CFSG.Blueprint.LieModel (PSimple 3 A) .trialityD4 0 3 f'

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
