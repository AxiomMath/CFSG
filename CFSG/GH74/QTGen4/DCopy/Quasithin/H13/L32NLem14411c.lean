module

public import CFSG.Quasithin.H13.L32NLem14411c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14411b

public section

namespace CFSG.Quasithin.H13.L14411

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert L1442M

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

namespace Ctx_F4
open CFSG.Quasithin.H13.L14411.Ctx_F4

variable (C : Ctx_F4 G T L V V₂ g D e)
include C

theorem set14_F4 : ∃ _ : IsMulCommutative ↥V, L32NSet14.Setting_F4 G T L V V₂ :=
  L14332.exists_setting_F4 C.h1332 C.h1334 C.h1222 C.hyp C.plane

theorem V2U_F4 : V₂ ≤ fsuU T V := C.uA ▸ L128A.le_uA V₂ (fsuV1 T V)

theorem UQ_F4 : fsuU T V ≤ pCoreOf 2 (l32nH T V) := by
  intro u hu
  rw [← C.cHat, ← L14332.rho_eq_one_iff_mem (C.UH_F4 hu) (HN (C.UH_F4 hu))]
  exact L128A.HatU.rho_eq_one_of_mem D C.comm_center_F4 hu _

theorem gV₂_F4 : g ∈ Subgroup.normalizer (V₂ : Set G) :=
  L128P.p128_le_normalizer le_rfl C.plane.1 C.gP

theorem Wg_cent_F4 : CFSG.conjugate (l32nW T V V₂) g ≤ Subgroup.centralizer (V₂ : Set G) :=
  L14332.conj_le_centralizer_of_le inf_le_right le_rfl C.gV₂_F4

theorem WgH_F4 : CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V :=
  (L14332.conj_le_centralizer_of_le inf_le_right C.plane.2 C.gV₂_F4).trans
    (Subgroup.centralizer_le_normalizer _)

theorem conj_center_mem_F4 {z : G} (hz : z ∈ centerOf (fsuU T V)) :
    g⁻¹ * z * g ∈ pCoreOf 2 (l32nH T V) := by
  have hzV : z ∈ V₂ := C.plane.2 (C.zU ▸ hz)
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ C.gV₂_F4) z).mp hzV
  rw [inv_inv] at this
  exact C.UQ_F4 (C.V2U_F4 this)

theorem sq_mem_Q_F4 {w : G} (hw : w ∈ CFSG.conjugate (l32nW T V V₂) g) :
    w * w ∈ pCoreOf 2 (l32nH T V) := by
  rw [show CFSG.conjugate (l32nW T V V₂) g = rconj (l32nW T V V₂) g from rfl, mem_rconj] at hw
  have huU : g * w * g⁻¹ ∈ fsuU T V := hw.1
  have hsq : (g * w * g⁻¹) * (g * w * g⁻¹) ∈ centerOf (fsuU T V) := by
    rw [← L128A.HatU.π_eq_zero_iff D (Subgroup.mul_mem _ huU huU), D.π_mul _ huU _ huU]
    exact add_self_zmod2 _
  have := C.conj_center_mem_F4 hsq
  rwa [show g⁻¹ * ((g * w * g⁻¹) * (g * w * g⁻¹)) * g = w * w by group] at this

theorem comm_mem_Q_F4 {w w' : G} (hw : w ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hw' : w' ∈ CFSG.conjugate (l32nW T V V₂) g) :
    w * w' * w⁻¹ * w'⁻¹ ∈ pCoreOf 2 (l32nH T V) := by
  rw [show CFSG.conjugate (l32nW T V V₂) g = rconj (l32nW T V V₂) g from rfl, mem_rconj] at hw hw'
  have := C.conj_center_mem_F4 (C.comm_center_F4 _ hw.1 _ hw'.1)
  rwa [show g⁻¹ * ((g * w * g⁻¹) * (g * w' * g⁻¹) * (g * w * g⁻¹)⁻¹ * (g * w' * g⁻¹)⁻¹) * g =
    w * w' * w⁻¹ * w'⁻¹ by group] at this

theorem conj_a_mem_F4 {a t : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) (ht : t ∈ T) :
    (t * a * t⁻¹)⁻¹ * a ∈ centerOf (fsuU T V) := by
  obtain ⟨_, S⟩ := C.set14_F4
  have htV₂ : t * a * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (C.plane.1.2.2 ht) a).mp ha
  have htV₁ : t * a * t⁻¹ ∉ fsuV1 T V := fun h =>
    haV ((Subgroup.mem_normalizer_iff.mp (C.TH_F4 ht) a).mpr h)
  rw [C.zU]
  rcases S.mem_V2_F4 htV₂ htV₁ ha with h | h
  · exact absurd h haV
  · have hV1 : (t * a * t⁻¹) * a ∈ fsuV1 T V := h
    have hsq : (t * a * t⁻¹) * (t * a * t⁻¹) = 1 := S.mul_self_V_F4 (C.plane.1.1 htV₂)
    have : (t * a * t⁻¹)⁻¹ = t * a * t⁻¹ := inv_eq_of_mul_eq_one_right hsq
    rw [this]
    exact hV1

theorem mem_normalizer_of_fix_F4 {a h : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (hh : h ∈ l32nH T V) (hfix : D.ρ ⟨h, HN hh⟩ (D.π a) = D.π a) :
    h ∈ Subgroup.normalizer (V₂ : Set G) := by
  obtain ⟨_, S⟩ := C.set14_F4
  have haU := C.V2U_F4 ha
  rw [D.ρ_π _ a haU, D.π_eq_iff _ (L128A.HatU.conj_mem (HN hh) haU) a haU, C.zU] at hfix

  have hha : h * a * h⁻¹ ∈ V₂ := by
    have : h * a * h⁻¹ = a * ((h * a * h⁻¹)⁻¹ * a)⁻¹ := by group
    rw [this]
    exact V₂.mul_mem ha (V₂.inv_mem (C.plane.2 hfix))
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  rcases S.mem_V2_F4 ha haV hv with h1 | h1
  · exact C.plane.2 ((Subgroup.mem_normalizer_iff.mp hh v).mp h1)
  · have haa : a * a = 1 := S.mul_self_V_F4 (C.plane.1.1 ha)
    have hv' : v = a * (a * v) := by
      rw [← mul_assoc, haa, one_mul]
    rw [hv', show h * (a * (a * v)) * h⁻¹ = (h * a * h⁻¹) * (h * (a * v) * h⁻¹) by group]
    exact V₂.mul_mem hha (C.plane.2 ((Subgroup.mem_normalizer_iff.mp hh _).mp h1))

end Ctx_F4

section Cert


namespace Ctx_F4
open CFSG.Quasithin.H13.L14411.Ctx_F4

variable (C : Ctx_F4 G T L V V₂ g D e)
include C

theorem e_pi_a_F4 {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) : e (D.π a) = vec8 vStar := by
  have haU := C.V2U_F4 ha
  have hfix : ∀ γ ∈ P7, (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π a)) = e (D.π a) := by
    intro γ hγ
    rw [← C.imgT] at hγ
    obtain ⟨t, ht, htN, rfl⟩ := (mem_img8 D e).mp hγ
    rw [matOf_mulVec, D.ρ_π _ a haU]
    congr 1
    exact ((D.π_eq_iff _ (L128A.HatU.conj_mem htN haU) a haU).mpr (C.conj_a_mem_F4 ha haV ht))
  rcases eq_of_fixed_P7 (e (D.π a)) hfix with h | h
  · exfalso
    rw [map_eq_zero_iff e e.injective, L128A.HatU.π_eq_zero_iff D haU, C.zU] at h
    exact haV h
  · exact h

theorem img_Wg_F4 : img8 D e (CFSG.conjugate (l32nW T V V₂) g) = N7 := by
  obtain ⟨a, ha, haV⟩ := C.abs.exists_mem_not_mem
  have haU := C.V2U_F4 ha
  have hWgN := C.WgH_F4.trans HN

  have hfixW : ∀ w (hw : w ∈ CFSG.conjugate (l32nW T V V₂) g),
      D.ρ ⟨w, hWgN hw⟩ (D.π a) = D.π a := fun w hw => by
    rw [D.ρ_π _ a haU, (Subgroup.mem_centralizer_iff.mp (C.Wg_cent_F4 hw) a ha).symm]
    congr 1
    group
  have hcomm : ∀ x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g),
      ∀ y ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g), x * y = y * x := by
    intro x hx y hy
    obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
    obtain ⟨w', hw', hw'N, rfl⟩ := (mem_img8 D e).mp hy
    have h1 := (C.matOf_eq_one_iff_F4 (C.WgH_F4 (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hw hw') (Subgroup.inv_mem _ hw)) (Subgroup.inv_mem _ hw')))).mpr
      (C.comm_mem_Q_F4 hw hw')
    have e1 : (⟨w * w' * w⁻¹ * w'⁻¹, HN (C.WgH_F4 (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ hw hw') (Subgroup.inv_mem _ hw)) (Subgroup.inv_mem _ hw')))⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) =
        ⟨w, hwN⟩ * ⟨w', hw'N⟩ * ⟨w, hwN⟩⁻¹ * ⟨w', hw'N⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv] at h1
    calc matOf e (D.ρ ⟨w, hwN⟩) * matOf e (D.ρ ⟨w', hw'N⟩)
        = (matOf e (D.ρ ⟨w, hwN⟩) * matOf e (D.ρ ⟨w', hw'N⟩) * (matOf e (D.ρ ⟨w, hwN⟩))⁻¹ *
            (matOf e (D.ρ ⟨w', hw'N⟩))⁻¹) * matOf e (D.ρ ⟨w', hw'N⟩) *
              matOf e (D.ρ ⟨w, hwN⟩) := by group
      _ = matOf e (D.ρ ⟨w', hw'N⟩) * matOf e (D.ρ ⟨w, hwN⟩) := by rw [h1, one_mul]
  have hle : img8 D e (CFSG.conjugate (l32nW T V V₂) g) ≤ N7 := by
    intro x hx
    have hxs : x ∈ s7 := C.imgH ▸ img8_mono D e C.WgH_F4 hx
    obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
    refine mem_N7_of hxs ?_ ?_ fun n hn hnfix => ?_
    · rw [← C.e_pi_a_F4 ha haV, matOf_mulVec]
      exact congrArg e (hfixW w hw)
    · rw [← map_mul, ← map_mul]
      have e1 : (⟨w, hwN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) * ⟨w, hwN⟩ =
          ⟨w * w, HN (C.WgH_F4 (Subgroup.mul_mem _ hw hw))⟩ := rfl
      rw [e1]
      exact (C.matOf_eq_one_iff_F4 (C.WgH_F4 (Subgroup.mul_mem _ hw hw))).mpr (C.sq_mem_Q_F4 hw)
    ·
      obtain ⟨h, hh, hhN, rfl⟩ := (mem_img8 D e).mp (by rw [C.imgH]; exact hn)
      have hfix : D.ρ ⟨h, HN hh⟩ (D.π a) = D.π a := by
        apply e.injective
        rw [← matOf_mulVec, C.e_pi_a_F4 ha haV]
        exact hnfix
      have hhV₂ := C.mem_normalizer_of_fix_F4 ha haV hh hfix
      have hconj : h * w * h⁻¹ ∈ CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V :=
        (Subgroup.mem_normalizer_iff.mp (C.nWg ⟨hh, hhV₂⟩) w).mp (Subgroup.mem_sup_left hw)
      have hmem : matOf e (D.ρ ⟨h, hhN⟩) * matOf e (D.ρ ⟨w, hwN⟩) *
          (matOf e (D.ρ ⟨h, hhN⟩))⁻¹ ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
        have h1 : img8 D e (CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V) =
            img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
          rw [img8_sup D e hWgN (fun c (hc : c ∈ l32nCHat T V) => HN hc.1), img8_cHat,
            sup_bot_eq]
        rw [← h1]
        refine (mem_img8 D e).mpr ⟨h * w * h⁻¹, hconj,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN) (Subgroup.inv_mem _ hhN), ?_⟩
        rw [show (⟨h * w * h⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN)
            (Subgroup.inv_mem _ hhN)⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
            ⟨h, hhN⟩ * ⟨w, hwN⟩ * ⟨h, hhN⟩⁻¹ from rfl, map_mul, map_mul, map_inv, map_mul,
          map_mul, map_inv]
      exact hcomm _ ((mem_img8 D e).mpr ⟨w, hw, hwN, rfl⟩) _ hmem
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_N7, card_img8, C.cardW]
  norm_num

theorem mem_hatE_F4 : ∀ p ∈ eW, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈
    (D.hat (l32nE T V V₂ g)).map e.toLinearMap := by
  obtain ⟨_, S⟩ := C.set14_F4
  obtain ⟨a, ha, haV⟩ := C.abs.exists_mem_not_mem
  have haU := C.V2U_F4 ha
  intro p hp
  obtain ⟨hp1, hp2⟩ := eW_spec p hp

  obtain ⟨w₀, hw₀⟩ := mem_elemsOf hp1
  have hval := cvB_spec.2.1
  obtain ⟨x, hxN, hx⟩ := exists_evalW n8G (subB_spec hval).2.2.2.2
    (unit_of_s7E cvB_spec.2.2.1) w₀
  have hxN' : x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
    rw [C.img_Wg_F4]
    exact hxN
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hxN'

  obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm (vec8 p.2))
  have hev : e (D.π u) = vec8 p.2 := by rw [hue, LinearEquiv.apply_symm_apply]
  have huW : u ∈ l32nW T V V₂ := by
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hB : D.B (D.π u) (D.π a) = 0 := by
      rw [C.form, hev, C.e_pi_a_F4 ha haV, ← b4N_spec, hp2]
      rfl
    have hua : u * a * u⁻¹ * a⁻¹ = 1 := (D.B_spec u hu a haU).mp hB
    have hua' : a * u = u * a := by
      calc a * u = (u * a * u⁻¹ * a⁻¹)⁻¹ * u * a := by group
        _ = u * a := by rw [hua]; group
    have hcen : ∀ z ∈ fsuV1 T V, z * u = u * z := fun z hz => by
      rw [← C.zU] at hz
      exact (Subgroup.mem_centralizer_iff.mp hz.2 u hu).symm
    rcases S.mem_V2_F4 ha haV hv with h1 | h1
    · exact hcen v h1
    · have haa : a * a = 1 := S.mul_self_V_F4 (C.plane.1.1 ha)
      have hv' : v = a * (a * v) := by rw [← mul_assoc, haa, one_mul]
      rw [hv']
      calc a * (a * v) * u = a * ((a * v) * u) := by group
        _ = a * (u * (a * v)) := by rw [hcen _ h1]
        _ = (a * u) * (a * v) := by group
        _ = u * (a * (a * v)) := by rw [hua']; group

  have hcommE : w * u * w⁻¹ * u⁻¹ ∈ l32nE T V V₂ g := by
    have h1 := C.wwE (Subgroup.commutator_mem_commutator huW hw)
    have h2 : w * u * w⁻¹ * u⁻¹ = (u * w * u⁻¹ * w⁻¹)⁻¹ := by group
    rw [h2]
    exact Subgroup.inv_mem _ (by simpa [commutatorElement_def] using h1)
  have hcU : w * u * w⁻¹ * u⁻¹ ∈ fsuU T V :=
    Subgroup.mul_mem _ (L128A.HatU.conj_mem hwN hu) (Subgroup.inv_mem _ hu)
  refine ⟨D.π (w * u * w⁻¹ * u⁻¹), L128A.HatU.π_mem_hat D hcommE hcU, ?_⟩
  rw [← L128A.HatU.rho_sub_π D hwN hu, sub_eq_add_neg, neg_eq_self_zmod2, LinearEquiv.coe_coe,
    map_add, ← matOf_mulVec, hev, hx, dec8_mulVec, hw₀, vec8_xor]

end Ctx_F4

end Cert

end CFSG.Quasithin.H13.L14411
