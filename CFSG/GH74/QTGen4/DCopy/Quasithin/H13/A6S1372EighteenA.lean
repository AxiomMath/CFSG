module

public import CFSG.Quasithin.H13.A6S1372EighteenA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372SixteenC1

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section KTilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable [IsMulCommutative ↥(conjClosure S.V3 H)] {C : S.Conf H}
  {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
  {K : Subgroup G}

omit hab in

theorem KData.realizes_tilde_of_plus_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) (h1352 : Stmt13_5_2_F4) (h51 : AsB51)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K) {D : FFModel}
    (hD : D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))) :
    D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hHV := S.le_normalizer_UV1 hH
  have hKU := hK.le_centralizer_U0_F4 hNS h13315 h1356two hH hhat hNU hna h13314 hLem h1352 h51 hab
  have hV1C : (fsuV1 T V).subgroupOf (conjClosure S.V3 H) ≤
      (Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H) :=
    fun x hx => S.V1_le_centralizer_QH_F4 hNS h13315 h1356two hH hx

  set p := QuotientGroup.map
    (((fsuV1 T V).subgroupOf (conjClosure S.V3 H)).subgroupOf ⊤)
    (((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)).subgroupOf ⊤)
    (MonoidHom.id _) (fun x hx => hV1C hx) with hp
  have hpmk : ∀ u : ↥(conjClosure S.V3 H),
      p (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
        InternalSec.secMk
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))
            u := fun _ => rfl
  have hpeq : ∀ (h : ↥H)
      (x : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      p (A6Mod.secAct hHU hHV h x) = A6Mod.secAct hHU hHC h (p x) := by
    intro h x
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ x
    rfl
  have hpsurj : Function.Surjective p := by
    intro y
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ y
    exact ⟨_, hpmk u⟩
  have hperf : Group.IsPerfect ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    (hK.isQuasisimple_tilde_F4 hNS h13315 h1356two hH hab hhat hNU hLem).1
  refine A6Real.realizes_of_map hpsurj ?_ ?_ ?_ ?_ hD
  · intro x hx
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
    exact ⟨_, (A6Mod.mem_autSec_iff hHU hHC hKH).2 ⟨k, hkK, rfl⟩, hpeq k⟩
  · intro y hy
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hKH).1 hy
    exact ⟨_, (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨k, hkK, rfl⟩, hpeq k⟩
  ·
    intro x hx v hv
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ v
    rw [hpmk, A6Mod.secMk_eq_one_iff] at hv
    rw [A6Mod.secAct_secMk]
    congr 1
    apply Subtype.ext
    rw [Setup.rho_apply_coe]
    have hc := Subgroup.mem_centralizer_iff.mp (hKU hkK) (u : G) ⟨u.2, hv⟩
    rw [← hc, mul_inv_cancel_right]
  ·
    intro x hx hfix
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
    have h1 : A6Mod.secAct hHU hHC k = 1 := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := hpsurj y
      rw [← hpeq, hfix]
      rfl
    rw [← MonoidHom.mem_ker, S.ker_secAct_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem] at h1
    rw [← MonoidHom.mem_ker, S.ker_secAct_tilde_F4 hNS h13315 h1356two hH]
    exact h1

end Conf

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6
