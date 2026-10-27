module

public import CFSG.GH74.GLS.Prop27.LocBal
public import CFSG.GH74.KGroups.L33
public meta import CFSG.GH74.GLS.Prop27.LocBal
public meta import CFSG.GH74.KGroups.L33
public import Certificates.Certificate5096
public import Certificates.Certificate5120
public meta import CFSG.Assembly.BalancedOddCoreCompletion
public import CFSG.Assembly.BalancedOddCoreCompletion
public meta import CFSG.Assembly.CompletedOddCoreElimination
public import CFSG.Assembly.CompletedOddCoreElimination
public meta import CFSG.Fischer.Uniq.CompTau
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.E2.ComponentsShape
public meta import CFSG.GH74.E2.ComponentsShape
public import CFSG.GH74.GLS.Statements
public meta import CFSG.GH74.GLS.Statements
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public meta import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public meta import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.SignalizerFunctor
public meta import CFSG.Walter.J1
public import CFSG.Walter.J1
public meta import Certificates.Certificate5007
public import Certificates.Certificate5007

public section

namespace CFSG.GH74.GLS.Prop27

open CFSG.GH74.KGroups CFSG.GH74.E2 CFSG.Certificates CFSG.Sporadic.Schreier

theorem l33_QP_le_QA : L33.QP.originalSubgroup ≤ L33.QA.originalSubgroup := by
  have hA : L33.QA.originalSubgroup =
      Subgroup.closure {g | g ∈ [L33.PA, L33.PB, L33.sg0]} := by
    rw [L33.QA, certificate_originalSubgroup]
  rw [L33.QP_closure, Subgroup.closure_le, hA]
  intro g hg
  apply Subgroup.subset_closure
  rcases hg with rfl | hg
  · simp
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    simp

theorem l33_oddCore :
    ∀ τ ∈ L33.QA.originalSubgroup, τ ^ 2 = 1 → τ ≠ 1 → ∀ x ∈ L33.QA.originalSubgroup,
      x * τ = τ * x → x ≠ 1 → Odd (orderOf x) →
      ∃ c ∈ L33.QP.originalSubgroup, c * τ = τ * c ∧ Even (orderOf (x * c * x⁻¹ * c⁻¹)) :=
  Certificates.certificate5096

theorem locBal2_L33 :
    LocBal2 ShapeL33 :=
  locBal2_of_autModel ShapeL33 L33.QP.originalSubgroup L33.QA.originalSubgroup l33_QP_le_QA
    (fun _ _ h => by
      obtain ⟨e⟩ := L33.equiv_of_lieModel h
      exact L33.autModel e)
    l33_oddCore

end CFSG.GH74.GLS.Prop27
