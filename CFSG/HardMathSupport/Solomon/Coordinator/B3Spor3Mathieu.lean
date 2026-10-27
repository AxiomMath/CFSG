module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Kit
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Model
public import Certificates.Certificate13511
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3

theorem rep_m11A : CFSG.Monster.B.Co2.Rep 11 m11S3A (List.formPerm [1, 9] * List.formPerm [3, 10] *
    List.formPerm [4, 6] * List.formPerm [7, 8]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m11B : CFSG.Monster.B.Co2.Rep 11 m11S3B (List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m12A : CFSG.Monster.B.Co2.Rep 12 m12S3A (List.formPerm [0, 3] * List.formPerm [2, 9] *
    List.formPerm [4, 10] * List.formPerm [5, 11]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m12B : CFSG.Monster.B.Co2.Rep 12 m12S3B (List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] *
    List.formPerm [4, 11, 10] * List.formPerm [5, 9, 6]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m22A : CFSG.Monster.B.Co2.Rep 22 m22S3A (List.formPerm [0, 12] * List.formPerm [1, 7] *
    List.formPerm [2, 15] * List.formPerm [3, 11] * List.formPerm [5, 21] *
    List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m22B : CFSG.Monster.B.Co2.Rep 22 m22S3B (List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] *
    List.formPerm [4, 11] * List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] *
    List.formPerm [16, 18]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m23A : CFSG.Monster.B.Co2.Rep 23 m23S3A (List.formPerm [0, 1] * List.formPerm [2, 3] *
    List.formPerm [6, 7] * List.formPerm [8, 9] * List.formPerm [12, 13] *
    List.formPerm [14, 15] * List.formPerm [18, 19] * List.formPerm [20, 21]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_m23B : CFSG.Monster.B.Co2.Rep 23 m23S3B (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] *
    List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] *
    List.formPerm [14, 16]) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem b3Phi_m11 :
    ∀ x : ↥NativeSporadic.M11, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set _)) :=
  b3Phi_centralizer_of_perm _
    (check_sound m11S3Data rep_m11A rep_m11B Certificates.certificate13511.1)

theorem b3Phi_m12 :
    ∀ x : ↥NativeSporadic.M12, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set _)) :=
  b3Phi_centralizer_of_perm _
    (check_sound m12S3Data rep_m12A rep_m12B Certificates.certificate13511.2.1)

theorem b3Phi_m22 :
    ∀ x : ↥NativeSporadic.M22, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set _)) :=
  b3Phi_centralizer_of_perm _
    (check_sound m22S3Data rep_m22A rep_m22B Certificates.certificate13511.2.2.1)

theorem b3Phi_m23 :
    ∀ x : ↥NativeSporadic.M23, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set _)) :=
  b3Phi_centralizer_of_perm _
    (check_sound m23S3Data rep_m23A rep_m23B Certificates.certificate13511.2.2.2)

theorem b3SporPair_M11_three (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .M11 3 :=
  b3SporPair_of_model hOut ↥NativeSporadic.M11 (hbr .M11) b3Phi_m11

theorem b3SporPair_M12_three (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .M12 3 :=
  b3SporPair_of_model hOut ↥NativeSporadic.M12 (hbr .M12) b3Phi_m12

theorem b3SporPair_M22_three (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .M22 3 :=
  b3SporPair_of_model hOut ↥NativeSporadic.M22 (hbr .M22) b3Phi_m22

theorem b3SporPair_M23_three (hbr : SporadicBridges)
    (hOut : SporadicOuterLeTwo) : B3SporPair .M23 3 :=
  b3SporPair_of_model hOut ↥NativeSporadic.M23 (hbr .M23) b3Phi_m23

end CFSG.HardMathSupport.Solomon.Coordinator
