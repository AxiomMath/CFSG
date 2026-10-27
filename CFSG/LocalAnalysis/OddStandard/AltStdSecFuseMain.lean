module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseConj
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseNear
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseNearCount
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGModel

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal

theorem farCount_of_le (n : ℕ) (hn : 12 ≤ n) : FarCount n := by
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h
  · exact farCount_mod01 n hn (Or.inl h)
  · exact farCount_mod01 n hn (Or.inr h)
  · exact farCount_mod23 n (by omega) (Or.inl h)
  · exact farCount_mod23 n (by omega) (Or.inr h)

theorem farOnlyFalse : FarOnlyFalse := farOnlyFalse_of_farCount farClass farCount_of_le

theorem nearOnlyFalse12 : NearOnlyFalse12 := nearOnlyFalse12_of_nearCount nearCount12

theorem fusionAll_of_shape_one {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}
    {Q : Subgroup G} {z : G} (hN4 : NearGivesRoot 4 (13 ≤ ·)) (hN3 : NearGivesRoot 3 (· = 12))
    (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (hn : 12 ≤ n) : FusionAll L z :=
  fusionAll_of_shape_one_of_props hN4 hN3 farOnlyFalse rootCover (nearCover 3) farClass
    nearOnlyFalse12 h d hQ2 hE hn

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

end CFSG.OddStandard.AltStdSec
