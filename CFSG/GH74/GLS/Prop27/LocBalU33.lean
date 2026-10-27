module

public import CFSG.GH74.GLS.Prop27.LocBal
public import CFSG.GH74.KGroups.U33
public meta import CFSG.GH74.GLS.Prop27.LocBal
public meta import CFSG.GH74.KGroups.U33
public import Certificates.Certificate5098
public import Certificates.Certificate5133
public import Certificates.Certificate8080
public import Certificates.Certificate8081
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

theorem u33_QP_le_QA : U33.QP.originalSubgroup ≤ U33.QA.originalSubgroup := by
  have hA : U33.QA.originalSubgroup =
      Subgroup.closure {g | g ∈ [U33.pa, U33.pb, U33.sg0]} := by
    rw [U33.QA, certificate_originalSubgroup]
  rw [U33.QP_closure, Subgroup.closure_le, hA]
  intro g hg
  apply Subgroup.subset_closure
  rcases hg with rfl | hg
  · simp
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    simp

theorem u33_oddCore_check :
    oddCoreCheck 189 (elemsT U33.QA) (elemsT U33.QP) = true :=
  Certificates.certificate5098

theorem locBal2_U33 :
    LocBal2 ShapeU33 :=
  locBal2_of_chains ShapeU33 U33.QA U33.QP U33.QA_ok U33.QP_ok u33_QP_le_QA (a := 6) (m := 189)
    (by decide) (by rw [card_group U33.QA U33.QA_ok, U33.QA_valid.2]; norm_num)
    (fun _ _ h => by
      obtain ⟨e⟩ := U33.equiv_of_lieModel h
      exact U33.autModel e)
    u33_oddCore_check

end CFSG.GH74.GLS.Prop27
