module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Kit
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model
public import Certificates.Certificate13512
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3

theorem rep_m24A : CFSG.Monster.B.Co2.Rep 24 m24S3A (List.formPerm [0, 3] * List.formPerm [1, 6] *
    List.formPerm [2, 16] * List.formPerm [4, 12] * List.formPerm [5, 8] * List.formPerm [7, 14] *
    List.formPerm [9, 18] * List.formPerm [10, 17] * List.formPerm [11, 20] *
    List.formPerm [13, 15] * List.formPerm [19, 23] * List.formPerm [21, 22]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m24B : CFSG.Monster.B.Co2.Rep 24 m24S3B (List.formPerm [0, 3, 5] *
    List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] * List.formPerm [4, 17, 9] *
    List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem b3Phi_m24 :
    ∀ x : ↥NativeSporadic.M24, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set _)) :=
  b3Phi_centralizer_of_perm _
    (check_sound m24S3Data rep_m24A rep_m24B Certificates.certificate13512)

theorem b3SporPair_M24_three (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .M24 3 :=
  b3SporPair_of_model hOut ↥NativeSporadic.M24 (hbr .M24) b3Phi_m24

end CFSG.HardMathSupport.Solomon.Coordinator
