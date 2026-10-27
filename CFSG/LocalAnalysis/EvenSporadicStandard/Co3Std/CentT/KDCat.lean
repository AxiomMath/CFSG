module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Defs

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def KDCo3Cat : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Catalog (K ⧸ center K) →
    IsPGroup 2 (center K) → ∀ ζ : MulAut K, orderOf ζ = 2 →
    ∀ D : Subgroup K, D ≤ fixedSubgroup ζ → D.relIndex (fixedSubgroup ζ) ≤ 2 →
      IsTwoSp62 ↥D → (∀ d : ↥D, d ∈ center ↥D → (d : K) ∈ center K) →
        (LieModel (K ⧸ center K) .POmegaPlus 4 2 1 ∨ LieModel (K ⧸ center K) .PSU 6 2 1 ∨
            NativeSporadic.IsSporadic (K ⧸ center K) .Fi22) ∧
          ∀ g : K, ζ ≠ MulAut.conj g

end CFSG.EvenSporadicStandard.Co3Std.CentT
