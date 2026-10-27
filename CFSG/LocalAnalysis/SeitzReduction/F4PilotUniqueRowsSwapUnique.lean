module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.ChevalleyBinomial
public import CFSG.LieType.Chevalley.RootWeightFiltration
public import CFSG.LocalAnalysis.EvenSmallLie.Setup

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

section General

variable {G : Type*} [Group G]

theorem conjugate_sup_eq_sup_conjugate (A B : Subgroup G) (h : G) :
    CFSG.conjugate (A ⊔ B) h = CFSG.conjugate A h ⊔ CFSG.conjugate B h :=
  Subgroup.map_sup _ _ _

theorem conjugate_le_centralizer_conjugate_of_le {A B : Subgroup G}
    (hAB : B ≤ centralizer (A : Set G)) (h : G) :
    CFSG.conjugate B h ≤ centralizer (CFSG.conjugate A h : Set G) := by
  intro y hy
  rw [mem_centralizer_iff]
  intro x hx
  have hx' : x ∈ CFSG.conjugate A h := hx
  rw [mem_conjugate_iff_of_mul] at hx' hy
  have hc := (mem_centralizer_iff.1 (hAB hy)) _ hx'
  calc x * y = h⁻¹ * ((h * x * h⁻¹) * (h * y * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * y * h⁻¹) * (h * x * h⁻¹)) * h := by rw [hc]
    _ = y * x := by group

@[expose] noncomputable def conjugateSymmEquiv (A : Subgroup G) (h : G) : CFSG.conjugate A h ≃* A :=
  (A.equivMapOfInjective _ (MulAut.conj h⁻¹).injective).symm

end General

end CFSG.SeitzReduction.F4Pilot
