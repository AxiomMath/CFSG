module

public import Certificates.Certificate5168
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier

theorem l34_outer3
    (σ : Equiv.Perm (Fin 42)) (hσ : σ ∈ L34.QA.originalSubgroup)
    (h27 : σ ^ 27 = 1) (h9 : 9 ∣ Nat.card ↥(L34.QP.originalSubgroup ⊓
      Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 42))))) :
    σ ∈ L34.QP.originalSubgroup := by
  have h := List.all_eq_true.1 Certificates.certificate5168 σ
    ((mem_elemsT L34.QA L34.QA_ok σ).2 hσ)
  rw [card_inf_centralizer L34.QP L34.QP_ok σ] at h9
  rw [mem_iff_sift L34.QP L34.QP_ok]
  have h0 : ((elemsT L34.QP).filter (fun g => decide (g * σ = σ * g))).length % 9 = 0 :=
    Nat.mod_eq_zero_of_dvd h9
  rw [decide_eq_true h27, h0] at h
  simpa using h

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
