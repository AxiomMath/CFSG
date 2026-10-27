module

public import CFSG.Quasithin.H13.A6S1372SixteenTilde
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372SixteenLf

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

omit hab in

theorem mem_QH_iff_tilde_F4 {h : G} (hh : h ∈ H) :
    h ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure S.V3 H, h * u * h⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  rw [hF.pCoreOf_eq_centralizerMod]
  exact ⟨fun h1 => h1.2.2, fun h1 => ⟨hh, hF.H_normalizes_V₁ hh, h1⟩⟩

omit hab in

theorem ker_secAct_tilde_F4 [IsMulCommutative ↥(conjClosure S.V3 H)] :
    (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)).ker =
      CFSG.Open.pCore 2 ↥H := by
  ext h
  rw [MonoidHom.mem_ker, A6Mod.secAct_eq_one_iff,
    ← S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH h.2]
  constructor
  · rintro ⟨x, hx, hxh⟩
    rwa [Subtype.ext hxh] at hx
  · intro hh
    exact ⟨h, hh, rfl⟩

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem UHg_le_H_F4 : conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ H :=
  (C.UHg_le_A_F4 hNS h13315 h1356two hH hab).trans (C.A_le_H_F4 hNS h13315 h1356two hH hab hhat)

theorem card_UHg_tilde_F4 [IsMulCommutative ↥(conjClosure S.V3 H)] :
    Nat.card (autSec (autOn (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) =
      (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓ pCoreOf 2 H).relIndex
        (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) :=
  A6Mod.card_autSec_eq (le_normalizer_conjClosure _ _) (S.le_normalizer_UV1 hH)
    (C.UHg_le_H_F4 hNS h13315 h1356two hH hab hhat) fun _ hx =>
      S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH (C.UHg_le_H_F4 hNS h13315 h1356two hH hab hhat hx)

theorem card_sec_le_UHg_tilde_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    Nat.card (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ≤
      Nat.card (autSec (autOn (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) *
        Nat.card (fixV (autSec
          (autOn (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :=
  A6Mod.card_sec_le (le_normalizer_conjClosure _ _) (S.le_normalizer_UV1 hH)
    (C.UHg_le_H_F4 hNS h13315 h1356two hH hab hhat)
    (fun _ hx => S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH
      (C.UHg_le_H_F4 hNS h13315 h1356two hH hab hhat hx))
    (C.relIndex_centralizer_UHg_le_F4 hNS h13315 h1356two hH hab hhat hna)

theorem isA2_UHg_tilde_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    IsA2 (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (autSec (autOn (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
  have hUgH := C.UHg_le_H_F4 hNS h13315 h1356two hH hab hhat
  have hmem : ∀ x ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H),
      (C.g : G) * x * (C.g : G)⁻¹ ∈ conjClosure S.V3 H := by
    intro x hx
    have := A1b.mem_conjSub_iff.1 hx
    simpa using this
  refine ⟨autSec_mono (InternalSec.autOn_le_autOn_of_le hUgH) _ _, ?_, ?_⟩
  · intro hbot
    have h1 := C.card_UHg_tilde_F4 hNS h13315 h1356two hH hab hhat
    rw [hbot, Subgroup.card_bot, eq_comm, Subgroup.relIndex_eq_one] at h1
    exact C.not_UHg_le_QH_F4 hNS h13315 h1356two hH hab hhat hna h13314 fun x hx => (h1 hx).2
  · refine Bridge.isElemAbelian2_autSec (A6Mod.isElemAbelian2_autOn
      (hUgH.trans (le_normalizer_conjClosure _ _)) (fun a ha b hb => ?_) (fun a ha => ?_))
      (A6Mod.autOn_le_stab (hUgH.trans (S.le_normalizer_UV1 hH)))
    · have hab' := congrArg Subtype.val (hab.1.is_comm.comm ⟨_, hmem a ha⟩ ⟨_, hmem b hb⟩)
      have e : a * b * a⁻¹ * b⁻¹ = (C.g : G)⁻¹ * (((C.g : G) * a * (C.g : G)⁻¹) *
          ((C.g : G) * b * (C.g : G)⁻¹) * ((C.g : G) * a * (C.g : G)⁻¹)⁻¹ *
          ((C.g : G) * b * (C.g : G)⁻¹)⁻¹) * (C.g : G) := by group
      have h1 : ((C.g : G) * a * (C.g : G)⁻¹) * ((C.g : G) * b * (C.g : G)⁻¹) *
          ((C.g : G) * a * (C.g : G)⁻¹)⁻¹ * ((C.g : G) * b * (C.g : G)⁻¹)⁻¹ = 1 := by
        simp only [Subgroup.coe_mul] at hab'
        rw [hab']
        group
      rw [e, h1, mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    · have h2 := hab.2 _ (hmem a ha)
      rw [pow_two] at h2
      have e : a * a = (C.g : G)⁻¹ * (((C.g : G) * a * (C.g : G)⁻¹) *
          ((C.g : G) * a * (C.g : G)⁻¹)) * (C.g : G) := by group
      rw [e, h2, mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _

theorem exists_isFFStarMin_UHg_tilde_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ D, IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) D ∧
      D ≤ autSec (autOn (conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
  have hV : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hA := C.isA2_UHg_tilde_F4 hNS h13315 h1356two hH hab hhat hna h13314
  have hr := (rAV_le_one_iff (Bridge.sec_sq_eq_one hV _ _) hA).2
    (C.card_sec_le_UHg_tilde_F4 hNS h13315 h1356two hH hab hhat hna)
  obtain ⟨D, hDA, hD, -⟩ := B1_4_4_le (Bridge.sec_sq_eq_one hV _ _) hA hr
  obtain ⟨D', hD', hD'D⟩ := B1Red.exists_isFFStarMin_below hD
  exact ⟨D', hD', hD'D.trans hDA⟩

end Hat

end Conf

end NonAb

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

theorem KData.le_normalizer_tilde_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    (hK : C.KData B K) :
    autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) ≤
      Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :
          Subgroup _) : Set _) := by
  have hHN := hK.le_normalizer_F4 hNS h13315 h1356two hH hab hhat hNU hLem
  rw [← S.range_secAct_tilde hH]
  rintro _ ⟨h, rfl⟩
  refine B19.mem_normalizer_of_map_conj_eq ?_
  rw [← A6Mod.autSec_map_conj (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
    (le_of_mem_cComp hK.2.2.1) h, B19.map_conj_eq_of_mem_normalizer (hHN h.2)]

theorem KData.nonempty_mulEquiv_tilde_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4) (hK : C.KData B K) :
    Nonempty (↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ≃*
      ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hHV := S.le_normalizer_UV1 hH
  set κ := (A6Mod.secAct hHU hHC).comp (Subgroup.inclusion hKH) with hκ
  set κ' := (A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH) with hκ'
  have hr : κ.range = autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) := by
    ext ψ
    rw [MonoidHom.mem_range, A6Mod.mem_autSec_iff hHU hHC hKH]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, k.2, rfl⟩
    · rintro ⟨h, hk, rfl⟩
      exact ⟨⟨h, hk⟩, rfl⟩
  have hr' : κ'.range = autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    ext ψ
    rw [MonoidHom.mem_range, A6Mod.mem_autSec_iff hHU hHV hKH]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, k.2, rfl⟩
    · rintro ⟨h, hk, rfl⟩
      exact ⟨⟨h, hk⟩, rfl⟩
  have hker : κ.ker = κ'.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hκ, hκ', MonoidHom.comp_apply,
      MonoidHom.comp_apply, ← MonoidHom.mem_ker, ← MonoidHom.mem_ker,
      S.ker_secAct_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem,
      S.ker_secAct_tilde_F4 hNS h13315 h1356two hH]
  exact ⟨(MulEquiv.subgroupCongr hr).symm.trans ((QuotientGroup.quotientKerEquivRange κ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans ((QuotientGroup.quotientKerEquivRange κ').trans
      (MulEquiv.subgroupCongr hr'))))⟩

theorem KData.isQuasisimple_tilde_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4) (hK : C.KData B K) :
    CFSG.IsQuasisimple ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) := by
  obtain ⟨e⟩ := hK.nonempty_mulEquiv_tilde_F4 hNS h13315 h1356two hH hab hhat hNU hLem
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e (B1Red.isQuasisimple_of_open hK.2.2.2.1.2.2)

theorem KData.inf_centralizer_tilde_eq_bot_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4) (hK : C.KData B K)
    {Y : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))}
    (hYX : Y ≤ autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) (hY : IsPGroup 2 ↥Y) :
    Y ⊓ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :
        Subgroup _) : Set _) = ⊥ := by
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hHV := S.le_normalizer_UV1 hH
  have hodd := hK.odd_card_eqvAut hab
  have hker : ∀ x : ↥H, A6Mod.secAct hHU hHC x = 1 ↔ A6Mod.secAct hHU hHV x = 1 := by
    intro x
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker,
      S.ker_secAct_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem,
      S.ker_secAct_tilde_F4 hNS h13315 h1356two hH]
  have heq : ∀ x y : ↥H, A6Mod.secAct hHU hHC x = A6Mod.secAct hHU hHC y ↔
      A6Mod.secAct hHU hHV x = A6Mod.secAct hHU hHV y := by
    intro x y
    rw [MonoidHom.eq_iff, MonoidHom.eq_iff, MonoidHom.mem_ker, MonoidHom.mem_ker, hker]
  rw [eq_bot_iff]
  rintro d ⟨hdY, hdC⟩
  have hdX := hYX hdY
  rw [← S.range_secAct_tilde hH] at hdX
  obtain ⟨h, rfl⟩ := hdX
  obtain ⟨k, hk⟩ := hY ⟨_, hdY⟩
  have hk' : A6Mod.secAct hHU hHV (h ^ 2 ^ k) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val hk
  have hρk : A6Mod.secAct hHU hHC h ^ 2 ^ k = 1 := by
    rw [← map_pow]
    exact (hker _).2 hk'
  have hC : A6Mod.secAct hHU hHC h ∈ Subgroup.centralizer
      ((autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
          Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro ψ hψ
    obtain ⟨x, hxK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hKH).1 hψ
    have hx' : A6Mod.secAct hHU hHV x ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
      (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨x, hxK, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hdC _ hx'
    have h2 : A6Mod.secAct hHU hHV (x * h) = A6Mod.secAct hHU hHV (h * x) := by
      rw [map_mul, map_mul]
      exact h1
    have h3 := (heq _ _).2 h2
    rw [map_mul, map_mul] at h3
    exact h3
  exact Subgroup.mem_bot.2 ((hker h).1 (A6Sixteen.eq_one_of_odd hodd hC hρk))

end Conf

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6
