module

public import CFSG.Quasithin.H13.A6S1372FifteenB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372Fifteen

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem b51Hyp_J_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
    {K : Subgroup G}
    (hB : IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B)
    (hKcomp : CFSG.Open.IsComponentOf (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
      (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
    (hBN : B ≤ Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
      Subgroup _) : Set _))
    (hBnot : ¬ B ≤ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
      Subgroup _) : Set _))
    (hFJ : quasithinGenFitting (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) =
      autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) :
    B51Hyp (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
      (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
  have hHU : H ≤ Subgroup.normalizer ((conjClosure S.V3 H : Subgroup G) : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  set ρ := A6Mod.secAct hHU hHC with hρ
  set X := autSec (autOn H (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hX
  set Kp := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) with hKp
  set J := ffJ X with hJ
  have hrange : ρ.range = X := S.range_secAct_plus
  have hKq : CFSG.IsQuasisimple ↥Kp := B1Red.isQuasisimple_of_open hKcomp.2.2
  have hKB : ⁅Kp, B⁆ = Kp := FFJImage.commutator_eq_of_not_le_centralizer hKq hBN hBnot
  have hKX : Kp ≤ X := hKcomp.1
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple
    S.h13.nonabelian hH.1.2
  have hSQX : SQTKGroup ↥X := by
    have h1 := InternalSec.sqtkGroup_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      (by
        rw [MonoidHom.ker_rangeRestrict, S.ker_secAct_plus_F4 hNS h13315 h1356two hH hab hNU hhat
          hLem]
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)) hSQ
    exact hrange ▸ h1
  have hSQK : SQTKGroup ↥Kp :=
    A6Fifteen.sqtkGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX)
      (InternalSec.sqtkGroup_subgroup hSQX (Kp.subgroupOf X))
  have hO2 := S.pCoreOf_plus_eq_bot_F4 hNS h13315 h1356two hH hab hNU hhat hLem
  have hb53 : B53Hyp J := by
    rw [hJ, ← hrange]
    exact FFJImage.b53Hyp_ffJ_range hSQ ρ (by rw [hrange]; exact hO2)
  have hKJ : Kp ≤ J := B1Red.K_le_ffJ hKX hB.1 hKB
  have hZ : centerOf J ≤ Kp := hFJ ▸ InternalSec.centerOf_le_quasithinGenFitting J
  exact ⟨by rw [hFJ, sup_eq_left.2 hZ], hKq, hSQK, hKJ, hb53.1, hb53.2.1⟩

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem card_commV_le_four_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4)
    [IsMulCommutative ↥(conjClosure S.V3 H)]
    {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
    (hBA : B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) :
    Nat.card (commV B) ≤ 4 := by
  have hAH := C.A_le_H_F4 hNS h13315 h1356two hH hab hhat
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hUH : conjClosure S.V3 H ≤ H := hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hBW := (B19.commV_mono hBA).trans (C.commV_A_plus_le hUH hAH fun u hu a ha =>
    C.comm_UH_A_mem_F4 hNS h13315 h1356two hH hab hhat hna h13314 hu ha)
  exact (Subgroup.card_le_of_le hBW).trans (S.card_V3_plus_F4 hNS h13315 h1356two hH h13314).le

theorem exists_K_b42_F4
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) (h56 : AsB56) (h51 : AsB51) (h42 : AsB42)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ B, IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B ∧
      B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
      ∃ K ∈ cComp H, CFSG.Open.IsComponentOf (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
          (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
        B ≤ Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) ∧
        ¬ B ≤ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) ∧
        autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ≤
          Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
              Subgroup _) : Set _) ∧
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) = ⊤ ∧
        quasithinGenFitting (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) =
          autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
        Nat.card (commV B) ≤ 4 ∧
        A6FifteenB.K15 (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
          (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B := by
  obtain ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ, hcases⟩ :=
    C.exists_K_b51_F4 hNS h13315 h1356two hH hab hhat hNU hna h13314 hLem h56 h51
  have hb51 := S.b51Hyp_J_F4 hNS h13315 h1356two hH hab hhat hNU hLem hB hKcomp hBN hBnot hFJ
  have hB4 := C.card_commV_le_four_F4 hNS h13315 h1356two hH hab hhat hna h13314 hBA
  have hBJ : IsFFStarOffender (ffJ (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) B :=
    ⟨B6.le_ffJ hB.1, hB.1.2.1, hB.1.2.2.1, hB.1.2.2.2⟩
  have hV' : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hV := Bridge.sec_sq_eq_one hV' (⊤ : Subgroup ↥(conjClosure S.V3 H))
    ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))
  refine ⟨B, hB, hBA, K, hKc, hKcomp, hBN, hBnot, hXN, hcomm, hFJ, hB4, ?_⟩
  rcases hcases with h1 | h2
  · exact Or.inl ⟨h1, A6FifteenB.b42Restricted_section h42 hV hb51 h1.1 hBJ hB4⟩
  · exact Or.inr h2

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
