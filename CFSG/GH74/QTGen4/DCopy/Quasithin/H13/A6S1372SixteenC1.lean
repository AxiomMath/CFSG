module

public import CFSG.Quasithin.H13.A6S1372SixteenC1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372Fifteen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372Seventeen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372SixteenB51

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

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

omit hab in

theorem cLT_le_normalizer_I_sup_F4 :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤
      Subgroup.normalizer ((C.I ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  refine A5.le_normalizer_of_forall_conj_mem fun q hq x hx => ?_
  have h1 := C.cLT_le_normalizer_I_F4 hNS h13315 h1356two hH hhat hq
  have h2 : q ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    le_normalizer_pCoreOf 2 H (hF.T_le_H (S.cLT_le_T hhat hq))
  have hle : C.I ⊔ pCoreOf 2 H ≤ (C.I ⊔ pCoreOf 2 H).comap (MulAut.conj q).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp h1 y).mp hy)
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp h2 y).mp hy)
  have := hle hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem mem_I_sup_of_mem_L_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4) {l : G} (hl : l ∈ L)
    (hl3 : l ^ 3 = 1) : l ∈ C.I ⊔ pCoreOf 2 H := by
  obtain ⟨a, ha, hal⟩ := C.exists_mul_of_mem_LT_F4 hNS h13315 h1356two hH hab hna h13314
    (le_sup_left (b := T) hl)
  have hnorm := C.cLT_le_normalizer_I_sup_F4 hNS h13315 h1356two hH hhat hal
  obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨_, S.cLT_le_T hhat hal⟩
  have hqk : (a⁻¹ * l) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨a', ha', he⟩ := A5.pow_mem_mul_of_normalizes ha hnorm (2 ^ k)
  rw [hqk, mul_one, mul_inv_cancel_left] at he
  have h4 : l = (l ^ 2 ^ k) ^ 2 ^ k := by
    rw [← pow_mul, ← mul_pow, show (2 * 2 : ℕ) = 4 by norm_num, pow_eq_pow_mod _ hl3,
      Nat.pow_mod]
    norm_num
  rw [h4, he]
  exact Subgroup.pow_mem _ ha' _

omit hhat in

theorem I_sup_le_centralizer_F4 :
    C.I ⊔ pCoreOf 2 H ≤ Subgroup.centralizer ((conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓
      (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) : Subgroup G) :
        Set G) := by
  set U₁ := conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓
    (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) with hU₁
  have hVH : conjClosure V H ≤ Subgroup.centralizer (U₁ : Set G) := fun y hy =>
    Subgroup.centralizer_le (inf_le_right.trans inf_le_left)
      (S.VH_le_centralizer_UH_F4 hNS h13315 h1356two hH hab hy)
  have hVHg : C.VHg ≤ Subgroup.centralizer (U₁ : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : (C.g : G) * u * (C.g : G)⁻¹ ∈ conjClosure S.V3 H := by
      have := (mem_conjSub (g := (C.g : G)⁻¹)).1 hu.1
      rwa [inv_inv] at this
    have hc := Subgroup.mem_centralizer_iff.mp (S.VH_le_centralizer_UH_F4 hNS h13315 h1356two hH
      hab ((C.mem_VHg).1 hy)) _ hu'
    have e1 : (C.g : G) * u * (C.g : G)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹) =
        (C.g : G) * (u * y) * (C.g : G)⁻¹ := by group
    have e2 : (C.g : G) * y * (C.g : G)⁻¹ * ((C.g : G) * u * (C.g : G)⁻¹) =
        (C.g : G) * (y * u) * (C.g : G)⁻¹ := by group
    rw [e1, e2] at hc
    exact mul_left_cancel (mul_right_cancel hc)
  have hQ : pCoreOf 2 H ≤ Subgroup.centralizer (U₁ : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp hu.2.2 q hq).symm
  exact sup_le (sup_le hVH hVHg) hQ

theorem comm_mem_UHg_inf_U0_F4 {a u : G}
    (ha : a ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H))
    (hu : u ∈ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) :
    a * u * a⁻¹ * u⁻¹ ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓
      (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have haH := C.UHg_le_H_F4 hNS h13315 h1356two hH hab hhat ha
  refine ⟨?_, ?_⟩
  · have hg2 : (C.g : G) * C.g ∈ H := hF.L₁T_le_H (C.g_sq_mem hhat)
    have hga : (C.g : G) * a * (C.g : G)⁻¹ ∈ conjClosure S.V3 H := by
      have := (mem_conjSub (g := (C.g : G)⁻¹)).1 ha
      rwa [inv_inv] at this
    have hgu : (C.g : G) * u * (C.g : G)⁻¹ ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) := by
      rw [mem_conjSub, inv_inv]
      have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hg2) u).mp
        hu.1
      have e : (C.g : G) * ((C.g : G) * u * (C.g : G)⁻¹) * (C.g : G)⁻¹ =
          ((C.g : G) * C.g) * u * ((C.g : G) * C.g)⁻¹ := by group
      rw [e]
      exact h1
    have hN := C.UHg_le_normalizer_UH_F4 hNS h13315 h1356two hH hab hhat hgu
    have h3 : u * a⁻¹ * u⁻¹ ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) := by
      rw [mem_conjSub, inv_inv]
      have e : (C.g : G) * (u * a⁻¹ * u⁻¹) * (C.g : G)⁻¹ =
          ((C.g : G) * u * (C.g : G)⁻¹) * ((C.g : G) * a * (C.g : G)⁻¹)⁻¹ *
            ((C.g : G) * u * (C.g : G)⁻¹)⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hN _).mp (Subgroup.inv_mem _ hga)
    have e : a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha h3
  · have h1 := (Subgroup.mem_normalizer_iff.mp (S.le_normalizer_U0 haH) u).mp hu
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hu)

theorem exists_c1_fix_F4 [IsMulCommutative ↥(conjClosure S.V3 H)]
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4) :
    ∃ (c₁ : G) (hc₁ : c₁ ∈ H), c₁ ^ 3 = 1 ∧
      c₁ ∈ Subgroup.centralizer ((conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓
        (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) : Subgroup G) :
          Set G) ∧
      ∀ w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
          (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
            (conjClosure S.V3 H))),
        A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_U0 (H := H))
          ⟨c₁, hc₁⟩ w = w → w = 1 := by
  have hHU := le_normalizer_conjClosure S.V3 H
  obtain ⟨c₁, hc₁L, hc₁3, hρ, -⟩ := C.exists_c1_F4 hNS h13315 h1356two hH hab hhat
  have hc₁H : (c₁ : G) ∈ H := S.L1_le_of_mem_Hz_F4 hNS h13315 h1356two hH hc₁L
  have hcV3 : (c₁ : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
    S.L1T_le_NV3 (le_sup_left (a := S.L1) hc₁L)
  have hc₁0 := C.mem_I_sup_of_mem_L_F4 hNS h13315 h1356two hH hab hhat hna h13314
    (S.L1_le_L hc₁L) hc₁3
  refine ⟨c₁, hc₁H, hc₁3, C.I_sup_le_centralizer_F4 hNS h13315 h1356two hH hab hc₁0, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ hfix
  rw [A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
    A6Mod.secMk_eq_one_iff] at hfix
  rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] at hfix
  have hu' : (u : G) ∈ S.V3 := hu
  have hcu : (c₁ : G) * u * (c₁ : G)⁻¹ ∈ S.V3 :=
    (Subgroup.mem_normalizer_iff.mp hcV3 (u : G)).mp hu'
  have h1 : (c₁ : G) * u * (c₁ : G)⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
    rw [← S.V3_inf_U0_F4 hNS h13315 h1356two hH h13314]
    refine ⟨S.V3.mul_mem hcu (S.V3.inv_mem hu'), ?_, hfix⟩
    exact (conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (hHU hc₁H) (u : G)).mp u.2) ((conjClosure S.V3 H).inv_mem u.2)
  have h2 := S.mem_V1_of_c012 hρ hu' h1
  exact (A6Mod.secMk_eq_one_iff _).2 (S.V1_le_centralizer_QH_F4 hNS h13315 h1356two hH h2)

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

theorem KData.fix_commV_tilde_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) (h1352 : Stmt13_5_2_F4) (h51 : AsB51)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G))
    {c : G} (hcH : c ∈ H) (hc3 : c ^ 3 = 1)
    (hcU : c ∈ Subgroup.centralizer ((conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓
        (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) : Subgroup G) :
          Set G)) :
    ∀ x ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))),
      A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) ⟨c, hcH⟩ x =
        x := by
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set Kt := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) with hKt
  set W0 := ((conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :
      Subgroup G).subgroupOf (conjClosure S.V3 H)).map
    (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) with hW0
  set ct := A6Mod.secAct hHU hHV ⟨c, hcH⟩ with hct

  obtain ⟨D, hDmin, hDUg⟩ :=
    C.exists_isFFStarMin_UHg_tilde_F4 hNS h13315 h1356two hH hab hhat hna h13314
  obtain ⟨h1ii, hcard, hDG⟩ :=
    hK.case1ii_tilde_F4 hNS h13315 h1356two hH hhat hNU hLem h1352 h51 hab hKU hDmin.1
  obtain ⟨hGL, n, F, _, _, hF, I, π, hind, hsup, hreal, -, -⟩ := h1ii
  have hDL : D ≤ Kt := hDG.trans hGL.le

  have hF2 : Nat.card F = 2 := by
    have hc := A6B51.card_eq_of_realizesVia_nat (hreal 0)
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hn1 : n = 1 := by
        have h1 : 1 < Nat.card F := Finite.one_lt_card
        rw [hF] at h1
        rcases n with _ | _ | n
        · simp at h1
        · rfl
        · omega
      rw [hF, hn1]
      norm_num
    · have h1 := A6B51.lt_card_statedSL_three hF hn
      rw [hc, hcard] at h1
      omega

  have hU : I 0 ⊔ I 1 = commV Kt := by
    rw [← hsup]
    refine le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1)) (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right

  have hKW0 : ∀ x ∈ Kt, ∀ w ∈ W0, x w ∈ W0 := by
    intro x hx w hw
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨Setup.rho (conjClosure S.V3 H) H hHU k u, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Setup.rho_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (S.le_normalizer_U0 k.2) _).mp hu
  have hcW0 : ∀ w ∈ W0, ct w ∈ W0 := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨Setup.rho (conjClosure S.V3 H) H hHU ⟨c, hcH⟩ u, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Setup.rho_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (S.le_normalizer_U0 hcH) _).mp hu
  have hcKt : ∀ l ∈ Kt, ct * l * ct⁻¹ ∈ Kt := by
    have hctX : ct ∈ autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
      (A6Mod.mem_autSec_iff hHU hHV le_rfl).2 ⟨⟨c, hcH⟩, hcH, rfl⟩
    have hN := hK.le_normalizer_tilde_F4 hNS h13315 h1356two hH hhat hNU hLem hab hctX
    exact fun l hl => (Subgroup.mem_normalizer_iff.mp hN l).mp hl
  have hNL : ∀ l ∈ Kt, ∀ x ∈ commSub W0 Kt, l x ∈ commSub W0 Kt := fun l hl x hx =>
    A6C1.apply_mem_commSub (fun y hy => Kt.mul_mem (Kt.mul_mem hl hy) (Kt.inv_mem hl))
      (hKW0 l hl) hx
  have hcN : ∀ x ∈ commSub W0 Kt, ct x ∈ commSub W0 Kt := fun x hx =>
    A6C1.apply_mem_commSub hcKt hcW0 hx
  have hcUU : ∀ x ∈ I 0 ⊔ I 1, ct x ∈ I 0 ⊔ I 1 := by
    rw [hU, commV_eq_commSub]
    exact fun x hx => A6C1.apply_mem_commSub hcKt (fun _ _ => Subgroup.mem_top _) hx
  have hNU' : commSub W0 Kt ≤ I 0 ⊔ I 1 := by
    rw [hU, commV_eq_commSub]
    exact commSub_mono le_top le_rfl
  have hN : commSub W0 Kt ≠ ⊥ := fun h =>
    hK.not_commSub_tilde_le_F4 hNS h13315 h1356two hH hab hKU (h.le.trans bot_le)
  have hUN : ¬ I 0 ⊔ I 1 ≤ commSub W0 Kt := by
    intro h
    refine hK.not_commV_tilde_le_F4 hNS h13315 h1356two hH ?_
    calc commV Kt = I 0 ⊔ I 1 := hU.symm
      _ ≤ commSub W0 Kt := h
      _ ≤ W0 := commSub_le_of_invariant hKW0
      _ ≤ fixV Kt ⊔ W0 := le_sup_right
  have hc3' : ct ^ 3 = 1 := by
    rw [hct, ← map_pow]
    have : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]

  have hcD : ∀ x ∈ commSub (commSub W0 Kt) D, ct x = x := by
    have hle : commSub (commSub W0 Kt) D ≤ fixV (Subgroup.zpowers ct) := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨d, hd, v, hv, rfl⟩
      rw [SetLike.mem_coe, CFSG.Quasithin.H.mem_fixV_zpowers_iff]
      obtain ⟨⟨a, haH⟩, ha, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV
        (C.UHg_le_H_F4 hNS h13315 h1356two hH hab hhat)).1 (hDUg hd)
      obtain ⟨u, hu, rfl⟩ := commSub_le_of_invariant hKW0 hv
      have hz : ((Setup.rho (conjClosure S.V3 H) H hHU ⟨a, haH⟩ u * u⁻¹ :
          ↥(conjClosure S.V3 H)) : G) ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓
            (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
        rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv]
        exact C.comm_mem_UHg_inf_U0_F4 hNS h13315 h1356two hH hab hhat ha hu
      have hcz := Subgroup.mem_centralizer_iff.mp hcU _ hz
      rw [A6Mod.secAct_secMk, ← map_inv, ← map_mul, hct, A6Mod.secAct_secMk]
      congr 1
      apply Subtype.ext
      rw [Setup.rho_apply_coe, ← hcz, mul_inv_cancel_right]
    exact fun x hx => CFSG.Quasithin.H.mem_fixV_zpowers_iff.1 (hle hx)

  have hfix := A6NatPair.fix_of_two_nat hF2 hind hreal hDmin.1 hDL hNL hNU' hN hUN hcKt hcN
    hcUU hc3' hcD
  intro x hx
  rw [← hU] at hx
  exact hfix x hx

omit hab in

theorem KData.le_centralizer_U0_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) (h1352 : Stmt13_5_2_F4) (h51 : AsB51)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K) :
    K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
  by_contra hKU
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hHV := S.le_normalizer_UV1 hH
  obtain ⟨c, hcH, hc3, hcU, hcfix⟩ :=
    C.exists_c1_fix_F4 hNS h13315 h1356two hH hab hhat hna h13314
  have hfix := hK.fix_commV_tilde_F4 hNS h13315 h1356two hH hhat hNU hna h13314 hLem h1352 h51 hab
    hKU hcH hc3 hcU
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

  have hle : commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ≤
      fixV (Subgroup.zpowers (A6Mod.secAct hHU hHC ⟨c, hcH⟩)) := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨ψ, hψ, v, rfl⟩
    rw [SetLike.mem_coe, CFSG.Quasithin.H.mem_fixV_zpowers_iff]
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hKH).1 hψ
    obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ v
    set x := InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u with hx
    have hk' : A6Mod.secAct hHU hHV k ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) :=
      (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨k, hkK, rfl⟩
    have hz : A6Mod.secAct hHU hHV k x * x⁻¹ ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
      Subgroup.subset_closure ⟨_, hk', x, rfl⟩
    have e : A6Mod.secAct hHU hHC k
        (InternalSec.secMk
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) u) *
        (InternalSec.secMk
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) u)⁻¹ =
        p (A6Mod.secAct hHU hHV k x * x⁻¹) := by
      rw [map_mul, map_inv, hpeq, hx, hpmk]
    rw [e, ← hpeq, hfix _ hz]

  have hbot : (S.V3.subgroupOf (conjClosure S.V3 H)).map
      (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
        (conjClosure S.V3 H))) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hwK : w ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
      rw [hK.2.2.2.2.2.2.2.1]
      exact Subgroup.mem_top w
    exact Subgroup.mem_bot.2 (hcfix w hw (CFSG.Quasithin.H.mem_fixV_zpowers_iff.1 (hle hwK)))
  have hcard := S.card_V3_plus_F4 hNS h13315 h1356two hH h13314
  rw [hbot, Subgroup.card_bot] at hcard
  omega

end Conf

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6
