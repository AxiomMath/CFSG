module

public import CFSG.Quasithin.H13.A6S1372Mod
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372Twelve

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

@[expose] def Lem1374One_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L →
    ∀ H : Subgroup G, H ∈ S.Hz → IsElemAbelian 2 (conjClosure S.V3 H) →
      ∀ h ∈ H, (∀ u ∈ conjClosure S.V3 H,
        h * u * h⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G)) → h ∈ pCoreOf 2 H

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem mem_QH_iff_plus_F4 (hNU : ¬ LieModel G .PSU 4 3 1)
    (hhat : ¬ IsHatA6 L) (hLem : Lem1374One_F4) {h : G} (hh : h ∈ H) :
    h ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure S.V3 H,
      h * u * h⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  constructor
  · intro hq u hu
    exact S.V1_le_centralizer_QH_F4 hNS h13315 h1356two hH (hF.commutator_mem_V₁ hq hu)
  · exact hLem G T L V S hNS hNU hhat H hH hab h hh

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem A_le_H_F4 : C.A ≤ H :=
  (C.A_le_T_F4 hNS h13315 h1356two hH hab hhat).trans (S.hypF91_F4 hNS h13315 h1356two hH).T_le_H

theorem card_A_plus_F4 (hNU : ¬ LieModel G .PSU 4 3 1)
    (hLem : Lem1374One_F4) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    Nat.card (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) =
      (C.A ⊓ pCoreOf 2 H).relIndex C.A :=
  A6Mod.card_autSec_eq (le_normalizer_conjClosure _ _) S.le_normalizer_U0
    (C.A_le_H_F4 hNS h13315 h1356two hH hab hhat) fun _ ha =>
      S.mem_QH_iff_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem
        (C.A_le_H_F4 hNS h13315 h1356two hH hab hhat ha)

theorem card_sec_le_A_plus_F4 (hNU : ¬ LieModel G .PSU 4 3 1)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (hLem : Lem1374One_F4)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    Nat.card (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ≤
      Nat.card (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) *
        Nat.card (fixV (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))) :=
  A6Mod.card_sec_le (le_normalizer_conjClosure _ _) S.le_normalizer_U0
    (C.A_le_H_F4 hNS h13315 h1356two hH hab hhat)
    (fun _ ha => S.mem_QH_iff_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem
      (C.A_le_H_F4 hNS h13315 h1356two hH hab hhat ha))
    (C.relIndex_centralizer_A_le_F4 hNS h13315 h1356two hH hab hhat hna)

theorem isA2_A_plus_F4 (hNU : ¬ LieModel G .PSU 4 3 1)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    IsA2 (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
      (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
  have hAH := C.A_le_H_F4 hNS h13315 h1356two hH hab hhat
  have hVC : V ≤ Subgroup.centralizer (conjClosure S.V3 H : Set G) :=
    (le_conjClosure V H).trans (S.VH_le_centralizer_UH_F4 hNS h13315 h1356two hH hab)
  refine ⟨autSec_mono (InternalSec.autOn_le_autOn_of_le hAH) _ _, ?_, ?_⟩
  ·
    intro hbot
    have h1 := C.card_A_plus_F4 hNS h13315 h1356two hH hab hhat hNU hLem
    rw [hbot, Subgroup.card_bot, eq_comm, Subgroup.relIndex_eq_one] at h1
    apply C.not_UHg_le_QH_F4 hNS h13315 h1356two hH hab hhat hna h13314
    exact fun x hx => (h1 (C.UHg_le_A_F4 hNS h13315 h1356two hH hab hx)).2
  · refine Bridge.isElemAbelian2_autSec (A6Mod.isElemAbelian2_autOn
      ((hAH.trans (le_normalizer_conjClosure _ _))) (fun a ha b hb => hVC
        (C.comm_VHg_mem_V_F4 hNS h13315 h1356two hH hab ha.1 hb.1)) (fun a ha => hVC ?_))
      (A6Mod.autOn_le_stab (hAH.trans S.le_normalizer_U0))
    have h := S.sq_VH_mem_V1_F4 hNS h13315 h1356two hH hab ((C.mem_VHg).1 ha.1)
    have hV := ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V) h
    have e : (C.g : G) * a * (C.g : G)⁻¹ * ((C.g : G) * a * (C.g : G)⁻¹) =
        (C.g : G) * (a * a) * (C.g : G)⁻¹ := by group
    rw [e] at hV
    exact (Subgroup.mem_normalizer_iff.mp C.g.2 _).mpr hV

theorem exists_isFFStarMin_A_plus_F4
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ B, IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B ∧
      B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) := by
  have hV : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hA := C.isA2_A_plus_F4 hNS h13315 h1356two hH hab hhat hNU hna h13314 hLem
  have hr := (rAV_le_one_iff (Bridge.sec_sq_eq_one hV _ _) hA).2
    (C.card_sec_le_A_plus_F4 hNS h13315 h1356two hH hab hhat hNU hna hLem)
  obtain ⟨B, hBA, hB, -⟩ := B1_4_4_le (Bridge.sec_sq_eq_one hV _ _) hA hr
  obtain ⟨B', hB', hB'B⟩ := B1Red.exists_isFFStarMin_below hB
  exact ⟨B', hB', hB'B.trans hBA⟩

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
