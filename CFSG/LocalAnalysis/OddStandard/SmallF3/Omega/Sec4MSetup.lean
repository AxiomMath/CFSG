module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4MPts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4NotConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Statements
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G} {u : G}

theorem conj_iff_mem_conjClassIn_top {x : G} :
    (∃ h : G, x = h⁻¹ * t * h) ↔ x ∈ conjClassIn ⊤ t := by
  simp only [conjClassIn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h⁻¹, Subgroup.mem_top _, by rw [inv_inv]⟩
  · rintro ⟨h, -, rfl⟩
    exact ⟨h⁻¹, by rw [inv_inv]⟩

end CFSG.OddStandard.SmallF3.Omega
