module

public import CFSG.GH74.GLS.Prop27.LocBal
public import CFSG.GH74.KGroups.L28
public meta import CFSG.GH74.GLS.Prop27.LocBal
public meta import CFSG.GH74.KGroups.L28
public import Certificates.Certificate5095
public import Certificates.Certificate5118
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

theorem l28_QP_le_QA : L28.QP.originalSubgroup ≤ L28.QA.originalSubgroup := by
  have hA : L28.QA.originalSubgroup =
      Subgroup.closure {g | g ∈ [L28.pa, L28.pb, L28.sg]} := by
    rw [L28.QA, certificate_originalSubgroup]
  rw [L28.QP_closure, Subgroup.closure_le, hA]
  intro g hg
  apply Subgroup.subset_closure
  rcases hg with rfl | hg
  · simp
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    simp

theorem l28_oddCore_check :
    oddCoreCheck 189 (elemsT L28.QA) (elemsT L28.QP) = true :=
  Certificates.certificate5095

theorem locBal2_L28 :
    LocBal2 ShapeL28 :=
  locBal2_of_chains ShapeL28 L28.QA L28.QP L28.QA_ok L28.QP_ok l28_QP_le_QA (a := 3) (m := 189)
    (by decide) (by rw [card_group L28.QA L28.QA_ok, L28.QA_valid.2]; norm_num)
    (fun _ _ h => L28.autModel h) l28_oddCore_check

end CFSG.GH74.GLS.Prop27
