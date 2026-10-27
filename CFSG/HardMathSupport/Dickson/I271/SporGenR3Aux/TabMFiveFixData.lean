module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveFixRank
public import Certificates.Data.TabCo1Reps

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.HardMathSupport.Dickson.I271.TabCo1

@[expose] def fivePA : Array ℕ :=
  #[
    1, 2, 5, 12, 16, 53,
    65, 219, 363, 546, 1482, 3864,
    4847, 8511, 18355, 62029, 127295, 131156,
    289981, 843776, 1318121, 3401524, 4757696, 15645780]

@[expose] def fiveQA : Array ℕ :=
  #[
    7539581, 10329856, 14424026, 15156696, 13498832, 12627648,
    5516320, 4761092, 12465792, 8243200, 10677248, 5664768,
    16761344, 8552448, 1949696, 3088384, 11075584, 15204352,
    9437184, 262144, 4325376, 6291456, 4194304, 8388608]

@[expose] def fivePB : Array ℕ :=
  #[
    1, 2, 7, 13, 17, 54,
    81, 230, 415, 1013, 1988, 2671,
    4157, 13218, 30603, 38598, 89964, 155096,
    323351, 564004, 1049111, 2149307, 4253874, 8429117]

@[expose] def fiveQB : Array ℕ :=
  #[
    2496447, 1886464, 10026258, 461148, 3510272, 5524768,
    15638672, 11992960, 7080008, 15393280, 10875904, 10829888,
    3540992, 3284992, 5537792, 131072, 65536, 12337152,
    262144, 524288, 1048576, 2097152, 4194304, 8388608]

@[expose] def fivePC : Array ℕ :=
  #[
    1, 2, 6, 10, 28, 49,
    82, 236, 432, 567, 1176, 3398,
    4631, 11610, 24751, 46181, 87635, 163154,
    549238, 1274626, 447538, 2850287, 4276137, 8610876]

@[expose] def fiveQC : Array ℕ :=
  #[
    395776, 7337407, 6956246, 6463988, 8732800, 11244712,
    4740288, 6136224, 9663760, 9633024, 7336960, 15138816,
    2097152, 10749952, 9183232, 9867264, 12599296, 4587520,
    12320768, 9961472, 1048576, 8421376, 4194304, 8388608]

theorem fixCheck_fiveA : fixCheck repD0 fivePA fiveQA 24 = true := by decide +kernel

theorem fixCheck_fiveB : fixCheck repD1 fivePB fiveQB 16 = true := by decide +kernel

theorem fixCheck_fiveC : fixCheck repZ fivePC fiveQC 20 = true := by decide +kernel

theorem fixCount_fiveA_le {M : Matrix (Fin 24) (Fin 24) (ZMod 2)} (h : rowsMatrix 24 repD0 = M) :
    fixCount M ≤ 1 := by
  subst h
  simpa using card_fixed_le_of_fixCheck (by norm_num) fixCheck_fiveA

theorem fixCount_fiveB_le {M : Matrix (Fin 24) (Fin 24) (ZMod 2)} (h : rowsMatrix 24 repD1 = M) :
    fixCount M ≤ 2 ^ 8 := by
  subst h
  simpa using card_fixed_le_of_fixCheck (by norm_num) fixCheck_fiveB

theorem fixCount_fiveC_le {M : Matrix (Fin 24) (Fin 24) (ZMod 2)} (h : rowsMatrix 24 repZ = M) :
    fixCount M ≤ 2 ^ 4 := by
  subst h
  simpa using card_fixed_le_of_fixCheck (by norm_num) fixCheck_fiveC

end CFSG.HardMathSupport.Dickson.I271.TabMFive
