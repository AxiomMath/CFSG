module

public import CFSG.Quasithin.H13.A6S1372L76Oh3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Og4

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open scoped Pointwise IsMulCommutative Matrix

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem false_of_natSp4_ge_two_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (h1337 : Stmt13_3_7_F4) (hNS : ¬ LieModel G .PSp 3 2 1) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) {n : ℕ} (hn2 : 2 ≤ n)
    (hSp : BinaryNaturalSp4 (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := id hSp
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨g₀, hgX, hg⟩ := S.exists_X1375_c012
  obtain ⟨a, P, v₂, rfl, -, rfl, haY, -, hP2, hPodd, hPv, hPa, -, hv⟩ :=
    S.exists_odd_config_of_F4 hH hK rfl h139 h37 h38 h13315 hgX hg
  obtain ⟨ι, hιinj, hιfix⟩ := A6L76Oh.exists_levi_sp (S.isPerfect_tilde hH hK) hn2 hF hπ haY
    hP2 hPodd hPv hPa hv
  exact S.false_of_levi_F4 h13315 h1356two h1337 hNS hH hab hK hgX hg h4 hιinj hιfix

end Setting4

theorem lem1376FiveSp4_of_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    (h1337 : Stmt13_3_7_F4) : Lem1376FiveSp4_F4 := by
  intro G _ _ T L V S hNS _ H hH hab _ K hK _ n hSp
  obtain ⟨F, _, _, hF, -⟩ := id hSp
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := F)
    rw [hF, pow_zero] at h1
    exact lt_irrefl 1 h1
  by_contra hn1
  exact S.false_of_natSp4_ge_two_F4 h139 h37 h38 h13315 h1356two h1337 hNS hH hab hK (by omega) hSp

theorem lem1376Full_of_atoms''_F4
    (hL : Lem1376OddNCL32_F4) (h3 : Lem1376NThree_F4) (hG2 : Lem1376FiveG2_F4)
    (hF : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9_F4) (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (h1337 : Stmt13_3_7_F4) : Lem1376Full_F4 :=
  lem1376Full_of_atoms'_F4 hL h3 (lem1376FiveSp4_of_F4 h139 h37 h38 h13315 h1356two h1337) hG2 hF h36
    h37 h38 h139 h13314 h13315 h1356two h1337

end CFSG.Quasithin.H13.A6
