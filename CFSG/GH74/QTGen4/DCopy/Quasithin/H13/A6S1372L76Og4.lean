module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Of5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Og3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

@[expose] def Lem1376FiveSp4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H → S.L1 ≤ K →
      ∀ n, BinaryNaturalSp4 (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n → n = 1

@[expose] def Lem1376FiveG2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H → S.L1 ≤ K →
      ∀ n, G2Natural (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n → n = 1

theorem lem1376Five_of_F4 (h139 : Stmt13_3_9_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (h1337 : Stmt13_3_7_F4)
    (hSp : Lem1376FiveSp4_F4) (hG2 : Lem1376FiveG2_F4) : Lem1376Five_F4 := by
  intro G _ _ T L V S hNS hNU H hH hab _ K hK hL1K
  refine ⟨fun n hSL => ?_, hSp G T L V S hNS hNU H hH hab K hK hL1K,
    hG2 G T L V S hNS hNU H hH hab K hK hL1K⟩
  obtain ⟨F, _, _, hF, -⟩ := id hSL
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := F)
    rw [hF, pow_zero] at h1
    exact lt_irrefl 1 h1
  by_contra hn1
  exact S.false_of_natSL3_ge_two_F4 h139 h37 h38 h13315 h1356two h1337 hNS hH hab hK (by omega) hSL

theorem lem1376Full_of_atoms'_F4
    (hL : Lem1376OddNCL32_F4) (h3 : Lem1376NThree_F4) (hSp : Lem1376FiveSp4_F4) (hG2 : Lem1376FiveG2_F4)
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9_F4) (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (h1337 : Stmt13_3_7_F4) : Lem1376Full_F4 :=
  lem1376Full_of_atoms_F4 hL h3 (lem1376Five_of_F4 h139 h37 h38 h13315 h1356two h1337 hSp hG2) hF h36
    h37 h38 h139 h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
