module

public import CFSG.RankThree.PartTwo.KFacts.K426J3
public import Certificates.Certificate5170
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup CFSG.Sporadic.Schreier CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.RankThree.Native CFSG.RankThree.PartOne

theorem j3_line4 :
    permOfArr 6156 j3tTrans[4]! ∈ j3P ∧
      permOfArr 6156 j3tTrans[4]! * j3tXB * (permOfArr 6156 j3tTrans[4]!)⁻¹ =
        permOfArr 6156 j3tLines[4]! ∧
      permOfArr 6156 j3tLines[4]! * j3tXB = j3tXB * permOfArr 6156 j3tLines[4]! ∧
      permOfArr 6156 j3tLines[4]! ≠ j3tXB ∧ permOfArr 6156 j3tLines[4]! ≠ j3tXB ^ 2 := by
  have hrec : ∀ j < 13, j3tRec.getD j 0 < 2 := fun j hj =>
    of_decide_eq_true (allLt_spec j3t_lines_check.2.2.2 hj)
  have ht := transOK2_spec mem_j3P_of_sift (fun j hj => (j3tReps_spec (hrec j hj)).1)
    (fun j hj => (linesOK3_line j3t_lines_check.1 hj).1) j3t_lines_check.2.2.1
    (j := 4) (by norm_num)
  have hr4 : j3tRec.getD 4 0 = 1 := rfl
  rw [hr4] at ht
  have hvL := rep_of_validA (linesOK3_line j3t_lines_check.1 (by norm_num : 4 < 13)).1
  have hvX := rep_of_validA (j3tReps_spec (by norm_num : 1 < 2)).1
  obtain ⟨hc, he1, he2⟩ := Certificates.certificate5170
  refine ⟨ht.1, ht.2, (commA_iff hvL hvX).1 hc, fun h => ?_, fun h => ?_⟩
  · change permOfArr 6156 j3tLines[4]! = permOfArr 6156 j3tReps[1]! at h
    rw [← (eqA_iff hvL hvX)] at h
    rw [h] at he1
    exact Bool.false_ne_true he1.symm
  · change permOfArr 6156 j3tLines[4]! = permOfArr 6156 j3tReps[1]! ^ 2 at h
    rw [← (eqA_iff hvL (rep_powArr hvX 2))] at h
    rw [h] at he2
    exact Bool.false_ne_true he2.symm

theorem j3_card_three : 3 ^ (Nat.card j3P).factorization 3 = 243 := by
  rw [factorization_card_j3P_three]
  norm_num

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
