module

public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bGen4Lift

public section

namespace CFSG.OddStandard.Solomon75

open AhatData

theorem sylowGen4_eleven (hcard : Nat.card (P0 11) = 128) (hgood : SylowGood 11 (P0 11))
    (hg4 : Gen4Good 11 (P0 11)) : SylowGen4 11 :=
  sylowGen4_of_good (by norm_num) (by norm_num) (by simpa using hcard) hgood hg4

end CFSG.OddStandard.Solomon75
