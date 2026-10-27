module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Basic
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.LocalComponent.Layer
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentTransport
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open
open scoped commutatorElement

namespace CentConfig

variable {X : Type} [Group X] [Finite X] {a b : X} {E : Subgroup X} {Fus : X → Prop}

private theorem le_centralizer_a (h : CentConfig X a b E Fus) :
    E ≤ Subgroup.centralizer ({a} : Set X) := fun e he =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.a_comm he)

theorem isComponent_E (h : CentConfig X a b E Fus) :
    IsComponentOf (E.subgroupOf (centralizer ({a} : Set X))) ⊤ := by
  have hEC := le_centralizer_a h
  exact (CFSG.ComponentClassification.OrdinaryComponentTransport.subgroupOf_iff
    E (Subgroup.centralizer ({a} : Set X)) hEC).mpr
    ⟨h.normal_subgroupOf.isSubnormal, h.isQuasisimple_E⟩

theorem le_layer (h : CentConfig X a b E Fus) :
    E ≤ CFSG.ComponentClassification.Layer.subgroup X := by
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  have hEC : E ≤ C := le_centralizer_a h
  have hcomp : IsComponentOf (E.subgroupOf C) ⊤ := isComponent_E h
  have hnative : CFSG.IsComponent (E.subgroupOf C) :=
    (CFSG.isComponent_iff_open (E.subgroupOf C)).mpr hcomp
  have hp : CFSG.IsPComponent 2 (E.subgroupOf C) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hnative
  have h2 : CFSG.ComponentClassification.TwoComponents.IsTwoComponent (E.subgroupOf C) :=
    (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).1 hp
  have hmain := CFSG.ClassicalInvolution.twoComponent_le_layer_of_l2PrimeBalance
    (G := X) (C := C) CFSG.ClassicalInvolution.l2PrimeBalance
    (show CFSG.Open.componentClassificationOddCore X = ⊥ from h.oddCore)
    h.a_sq rfl h2
  simpa only [Subgroup.map_subgroupOf_eq_of_le hEC] using hmain

theorem exists_component_not_commuting (h : CentConfig X a b E Fus) :
    ∃ L : Subgroup X, IsComponentOf L ⊤ ∧ ⁅E, L⁆ ≠ ⊥ := by
  by_contra hcontra
  push_neg at hcontra
  have hlayer : CFSG.ComponentClassification.Layer.subgroup X ≤
      Subgroup.centralizer (E : Set X) := by
    rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup X]
    exact sSup_le fun L hL =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
        rw [Subgroup.commutator_comm]
        exact hcontra L hL)
  have hEcent : E ≤ Subgroup.centralizer (E : Set X) := (le_layer h).trans hlayer
  have hcomm : commutator ↥E = ⊥ := by
    change ⁅(⊤ : Subgroup ↥E), ⊤⁆ = ⊥
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _ y _
    exact (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEcent y.2) x x.2)).symm
  have htopbot : (⊤ : Subgroup ↥E) = ⊥ := by
    rw [← h.isQuasisimple_E.1, hcomm]
  have hbE : (⟨b, h.b_mem⟩ : ↥E) = 1 := by
    have hmem : (⟨b, h.b_mem⟩ : ↥E) ∈ (⊥ : Subgroup ↥E) := by
      rw [← htopbot]
      exact Subgroup.mem_top _
    simpa using hmem
  exact h.b_ne (by simpa using congrArg (fun z : ↥E => (z : X)) hbE)

end CentConfig

end CFSG.EvenSporadicStandard.Co3Std.CentT
