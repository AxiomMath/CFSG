module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecShape3Count
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowModel

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem false_of_shape_three (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    {u : G} (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = z) :
    False :=
  false_of_shape_three_of_count (oddRootCount_of_le n h.hn) h d hQ2 hu huL hu2

end CFSG.OddStandard.AltStdSec
