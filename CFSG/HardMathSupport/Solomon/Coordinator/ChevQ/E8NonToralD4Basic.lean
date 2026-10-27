module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def KernelPosStable {τ : Tag} {K : Type} [Field K] {ι : Type}
    (a : ι → Fin τ.rank → Kˣ) (w : WeylGroup τ) : Prop :=
  ∀ γ ∈ familyKernel a, 0 < height γ → w • γ ∈ familyKernel a ∧ 0 < height (w • γ)

@[expose] def IsOrthTriple {τ : Tag} (w : WeylGroup τ) (d : Fin τ.rank → ℤ) : Prop :=
  iform d (w • d) = 0 ∧ iform d (w ^ 2 • d) = 0 ∧ iform (w • d) (w ^ 2 • d) = 0

@[expose] def tripleRefl {τ : Tag} (w : WeylGroup τ) (d : Fin τ.rank → ℤ) : WeylGroup τ :=
  rootReflection d * rootReflection (w • d) * rootReflection (w ^ 2 • d)

@[expose] def orbitNorm {G : Type*} [Group G] (z y : G) : G :=
  y * (z * y * z⁻¹) * (z ^ 2 * y * (z ^ 2)⁻¹)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
