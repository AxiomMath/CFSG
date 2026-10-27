module

public import CFSG.Quasithin.H13.A6S1372Fourteen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372Mod

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.B19 CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem ker_secAct_plus_F4 (hNU : ¬ LieModel G .PSU 4 3 1)
    (hhat : ¬ IsHatA6 L) (hLem : Lem1374One_F4) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_U0 (H := H))).ker =
      CFSG.Open.pCore 2 ↥H := by
  ext h
  rw [MonoidHom.mem_ker, A6Mod.secAct_eq_one_iff,
    ← S.mem_QH_iff_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem h.2]
  constructor
  · rintro ⟨x, hx, hxh⟩
    rwa [Subtype.ext hxh] at hx
  · intro hh
    exact ⟨h, hh, rfl⟩

theorem pCoreOf_plus_eq_bot_F4 (hNU : ¬ LieModel G .PSU 4 3 1)
    (hhat : ¬ IsHatA6 L) (hLem : Lem1374One_F4) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    pCoreOf 2 (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) = ⊥ := by
  rw [← S.range_secAct_plus]
  exact A6Fourteen.pCoreOf_range_eq_bot _
    (S.ker_secAct_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem)

omit hab in

theorem Q_le_H_F4 (hhat : ¬ IsHatA6 L) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ H :=
  (S.cLT_le_T hhat).trans (S.hypF91_F4 hNS h13315 h1356two hH).T_le_H

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

include C in

theorem exists_c_plus_F4 [IsMulCommutative ↥(conjClosure S.V3 H)]
    (h13314 : Stmt13_3_14_F4) :
    ∃ c ∈ autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)),
      c ^ 3 = 1 ∧
      (∀ p ∈ autSec (autOn ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)),
        c * p * c⁻¹ ∈ autSec (autOn ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
          (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
      (∀ p ∈ autSec (autOn ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)),
        c⁻¹ * p * c ∈ autSec (autOn ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
          (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
      (∀ w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
          (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
            (conjClosure S.V3 H))),
        c w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
          (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
            (conjClosure S.V3 H)))) ∧
      (∀ w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
          (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
            (conjClosure S.V3 H))), c w = w → w = 1) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hQH := S.Q_le_H_F4 hNS h13315 h1356two hH hhat
  obtain ⟨c₁, hc₁L, hc₁3, hρ, -⟩ := C.exists_c1_F4 hNS h13315 h1356two hH hab hhat
  have hc₁H : (c₁ : G) ∈ H := S.L1_le_of_mem_Hz_F4 hNS h13315 h1356two hH hc₁L
  have hc₁LT : (c₁ : G) ∈ L ⊔ T := le_sup_left (a := L) (S.L1_le_L hc₁L)
  have hcN := S.le_normalizer_cLT hc₁LT
  set c₀ : ↥H := ⟨c₁, hc₁H⟩ with hc₀
  refine ⟨A6Mod.secAct hHU hHC c₀, (A6Mod.mem_autSec_iff hHU hHC le_rfl).2 ⟨c₀, hc₁H, rfl⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · have : c₀ ^ 3 = 1 := Subtype.ext (by simpa using hc₁3)
    rw [← map_pow, this, map_one]
  · intro p hp
    obtain ⟨q, hqQ, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hQH).1 hp
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (A6Mod.mem_autSec_iff hHU hHC hQH).2 ⟨_,
      (Subgroup.mem_normalizer_iff.mp hcN _).mp hqQ, rfl⟩
  · intro p hp
    obtain ⟨q, hqQ, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hQH).1 hp
    rw [← map_inv, ← map_mul, ← map_mul]
    have hcN' := Subgroup.inv_mem _ hcN
    refine (A6Mod.mem_autSec_iff hHU hHC hQH).2 ⟨_, ?_, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp hcN' (q : G)).mp hqQ
    simpa using this
  · rintro _ ⟨u, hu, rfl⟩
    rw [A6Mod.secAct_secMk]
    refine ⟨_, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Setup.rho_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (S.L1T_le_NV3 (le_sup_left (a := S.L1) hc₁L))
      (u : G)).mp hu
  · rintro _ ⟨u, hu, rfl⟩ hfix
    rw [A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      A6Mod.secMk_eq_one_iff] at hfix
    rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] at hfix
    have hu' : (u : G) ∈ S.V3 := hu
    have hcu : (c₁ : G) * u * (c₁ : G)⁻¹ ∈ S.V3 :=
      (Subgroup.mem_normalizer_iff.mp (S.L1T_le_NV3 (le_sup_left (a := S.L1) hc₁L))
        (u : G)).mp hu'
    have h1 : (c₁ : G) * u * (c₁ : G)⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
      rw [← S.V3_inf_U0_F4 hNS h13315 h1356two hH h13314]
      refine ⟨S.V3.mul_mem hcu (S.V3.inv_mem hu'), ?_, hfix⟩
      exact (conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (hHU hc₁H) (u : G)).mp u.2) ((conjClosure S.V3 H).inv_mem u.2)
    have h2 := S.mem_V1_of_c012 hρ hu' h1
    exact (A6Mod.secMk_eq_one_iff _).2 (S.V1_le_centralizer_QH_F4 hNS h13315 h1356two hH h2)

theorem le_centralizer_nilpotent_F4
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {B N : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
    (hB : IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B)
    (hBA : B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
    (hNX : N ≤ autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
    (hN : (N.subgroupOf (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))).Normal)
    (hnil : Group.IsNilpotent N) : B ≤ Subgroup.centralizer (N : Set _) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hV : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hS := A6Fourteen.setting_of_nilpotent hNX hN hnil
    (S.pCoreOf_plus_eq_bot_F4 hNS h13315 h1356two hH hab hNU hhat hLem)
  obtain ⟨c, hcX, hc3, hcP, hcP', hcW, hfix⟩ :=
    exists_c_plus_F4 hNS h13315 h1356two hH hab C hhat h13314
  have hAH := C.A_le_H_F4 hNS h13315 h1356two hH hab hhat
  have hQH := S.Q_le_H_F4 hNS h13315 h1356two hH hhat
  have hAQ : C.A ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := fun a ha =>
    ⟨C.VHg_le_LT_F4 hNS h13315 h1356two hH hab ha.1, ha.2⟩
  have hBP := hBA.trans (autSec_mono (InternalSec.autOn_le_autOn_of_le hAQ) _ _)
  have hUH : conjClosure S.V3 H ≤ H := hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hmono : commV B ≤ commV (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
    unfold commV
    refine Subgroup.closure_mono fun w hw => ?_
    obtain ⟨x, hx, v, hv⟩ := hw
    exact ⟨x, hBA hx, v, hv⟩
  have hBW := hmono.trans (C.commV_A_plus_le hUH hAH fun u hu a ha =>
    C.comm_UH_A_mem_F4 hNS h13315 h1356two hH hab hhat hna h13314 hu ha)
  have h := A6Fourteen.comm_eq_bot (Bridge.sec_sq_eq_one hV _ _) hS hB hBP
    (isPGroup_Q_plus hhat hQH) hBW hcX hcP hcP' hc3 hcW hfix
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact Subgroup.le_centralizer_iff.mp h

theorem exists_K_F4 (hNU : ¬ LieModel G .PSU 4 3 1)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4)
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
            Subgroup _) : Set _) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hV : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  obtain ⟨B, hB, hBA⟩ := C.exists_isFFStarMin_A_plus_F4 hNS h13315 h1356two hH hab hhat hNU hna
    h13314 hLem
  refine ⟨B, hB, hBA, ?_⟩
  have hO2 := S.pCoreOf_plus_eq_bot_F4 hNS h13315 h1356two hH hab hNU hhat hLem
  obtain ⟨K', hK', hnot⟩ := A6Fourteen.exists_component_not_le hB.1.1 hB.1.2.1 hB.1.2.2.1.2 hO2
    fun N hNX hN hnil => C.le_centralizer_nilpotent_F4 hNS h13315 h1356two hH hab hhat hNU hna
      h13314 hLem hB hBA hNX hN hnil
  have hBN := B15P4.asB15Part4 _ (Bridge.sec_sq_eq_one hV _ _) _ B hB.1 K' hK'

  have hK'c := A6Fourteen.mem_cComp_of_isComponentOf hK'
  rw [← S.range_secAct_plus] at hK'c
  have hsolv : Group.IsSolvable (A6Mod.secAct hHU hHC).ker := by
    rw [S.ker_secAct_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)).isNilpotent
    infer_instance
  obtain ⟨K₀, hK₀, hK₀map⟩ := A6Fourteen.exists_cComp_of_range _ hsolv hK'c
  have hK₀H := LocDbl.map_mem_cComp_of_ker H.subtype
    (LocDbl.isSolvable_ker_of_injective _ H.subtype_injective) hK₀
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hK₀H
  have hKeq : autSec (autOn (K₀.map H.subtype) (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) = K' := by
    rw [← hK₀map]
    ext ψ
    rw [A6Mod.mem_autSec_iff hHU hHC (Subgroup.map_subtype_le K₀), Subgroup.mem_map]
    constructor
    · rintro ⟨h, ⟨k, hk, hkh⟩, rfl⟩
      have : k = h := Subtype.ext hkh
      exact ⟨k, hk, by rw [this]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, ⟨k, hk, rfl⟩, rfl⟩
  exact ⟨K₀.map H.subtype, hK₀H, hKeq ▸ hK', hKeq ▸ hBN, hKeq ▸ hnot⟩

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
