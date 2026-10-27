module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

section Dim

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def SimHasDim (x : ProjSim Q) (r : ℕ) : Prop :=
  ∃ t : OGroup Q, t * t = 1 ∧ invDim t = r ∧ projOrthToProjSim Q (toProj Q t) = x

theorem SimHasType.simHasDim {x : ProjSim Q} {r : ℕ} {α : ℤˣ} (h : SimHasType x r α) :
    SimHasDim x r := by
  obtain ⟨y, hy, -, t, htt, hty, rfl⟩ := h
  exact ⟨t, htt, congrArg Prod.fst hty, hy⟩

end Dim

@[expose] def Asc82E16Model : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate),
    Module.finrank (ZMod 3) V = 6 → quadSign Q = -1 →
      ∀ F : Subgroup (ProjSim Q), IsElemAb2 F 4 →
        (∀ f ∈ F, f ≠ 1 → (SimInOmegaStar hQ f ∧ SimHasDim f 4) ∨ SimHasDim f 3) →
          ∀ f ∈ F, SimInOmegaStar hQ f

end CFSG.OddStandard.SmallF3.Omega
