module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallTransport
public import CFSG.GH74.KGroups.A6
public meta import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public meta import CFSG.GH74.KGroups.A6
public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA6Inputs
public import Certificates.Certificate2016
public import Certificates.Certificate5108

public section

namespace CFSG.ComponentClassification.FooteSmall.A6

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A6

theorem Q0_closed : closedCheck Q0list = true :=
  Certificates.certificate2016.1

theorem Q0_nodup : Q0list.Nodup :=
  Certificates.certificate2016.2.1

theorem Q0_length : Q0list.length = 2 ^ 5 :=
  Certificates.certificate2016.2.2.1

theorem Q0_le : Q0list.all (fun g => QA.sift g 0) = true :=
  Certificates.certificate2016.2.2.2.1

theorem ab_ok : (a0 ∈ Q0list ∧ b0 ∈ Q0list) ∧ (QP.sift a0 0 = true ∧ QP.sift b0 0 = true) ∧
    dihB a0 b0 = true :=
  Certificates.certificate2016.2.2.2.2.1

theorem pair_ok : pairCheck 3 4 Q0list (elemsT QP) [pa, pb] = true :=
  Certificates.certificate2016.2.2.2.2.2

theorem iSup_fix_eq_top {K : Type} [Group K] [Finite K] (e : K ≃* QP.originalSubgroup)
    (T : Subgroup (MulAut K)) (hT : IsPGroup 2 T)
    (hTP : ∃ P : Sylow 2 K, Nonempty ((P : Subgroup K) ≃* T)) :
    ⨆ (τ : MulAut K) (_ : τ ∈ T) (_ : orderOf τ = 2),
      MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id K) = ⊤ := by
  obtain ⟨M, hMP, hMA⟩ := autModel e
  have hcard : Q0list.length = 2 ^ QA.orderCertificate.factorization 2 := by
    rw [QA_valid.2, factorization_two_of_eq (k := 5) (r := 45) (by norm_num) (by norm_num)]
    exact Q0_length
  exact iSup_fix_eq_top_of_checks QP QA QP_ok QA_ok QP_closure M hMP hMA Q0list Q0_closed
    Q0_nodup hcard Q0_le pair_ok ab_ok.1.1 ab_ok.1.2 ab_ok.2.1.1 ab_ok.2.1.2 ab_ok.2.2 T hT hTP

end CFSG.ComponentClassification.FooteSmall.A6
