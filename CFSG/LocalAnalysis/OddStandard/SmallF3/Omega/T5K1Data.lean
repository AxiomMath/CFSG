module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem t5_k1_data (hS : Asc82SchurU43) (hL : IsOm6Z2 L) {s : G} (hk : Kind5 L s 1) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (φ : ↥L →* omegaGroup hQ)
      (τ : OGroup Q), IsCoverMap L φ ∧ τ * τ = 1 ∧ invType τ = (4, -1) ∧
        CoverAct L φ s (orthToSim Q τ) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, e, x, hdim, hsgn, hx, hxt⟩ := hk
  obtain ⟨τ, hτ2, hτty, hτx⟩ := t5_simHasType_elim hxt
  obtain ⟨φ, hφ, -, hact⟩ := t5_cover_data hS hL hdim hsgn hx hτx
  exact ⟨V, i1, i2, i3, Q, hQ, φ, τ, hφ, hτ2, hτty, hact⟩

end CFSG.OddStandard.SmallF3.Omega
