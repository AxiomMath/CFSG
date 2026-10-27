module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution

@[expose] def Asc82FactZetaInv6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
      {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate} (φ : ↥L →* omegaGroup hQ),
      IsCoverMap L φ → ∀ (w : G) (o : OGroup Q), CoverAct L φ w (orthToSim Q o) →
        (detSpinorNorm hQ o).1 = 1 → (detSpinorNorm hQ o).2 ≠ 1 →
          ∀ x ∈ oddCoreIn L, w * x * w⁻¹ = x⁻¹

end CFSG.OddStandard.SmallF3.Omega
