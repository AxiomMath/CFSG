module

public import CFSG.Quasithin.H13.L32NLemE8a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem144Ba

public section

namespace CFSG.Quasithin.H13.L1442E8

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert S8Cert L1442M L14411 L144B

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

structure Ctx8_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G) (g a : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) : Prop where

  base : Base_F4 G T L V V₂ g

  aV₂ : a ∈ V₂

  aV₁ : a ∉ fsuV1 T V

  imgH : img8 D e (l32nH T V) = s8

  form : ∀ x y : D.V, D.B x y = b4V (e x) (e y)

  ePiA : e (D.π a) = vec8 vR

  hat3 : ∀ f : D.V →ₗ[ZMod 2] ZMod 2, f (D.π a) = 0 →
    ∃ x ∈ D.img (CFSG.conjugate (l32nW T V V₂) g),
      ∀ w ∈ D.hat (l32nE T V V₂ g), x w = w + f w • D.π a

  hat5 : Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) +
      Nat.log 2 ((D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
        (D.img (CFSG.conjugate (l32nW T V V₂) g))) = Module.finrank (ZMod 2) D.V - 1

namespace Ctx8_F4
open CFSG.Quasithin.H13.L1442E8.Ctx8_F4

variable (C : Ctx8_F4 G T L V V₂ g a D e)
include C

theorem img_zUg_F4 : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) = ⊥ := by
  rw [eq_bot_iff]
  intro ψ hψ
  obtain ⟨z, hz, hzN, rfl⟩ := (L128A.HatU.mem_img D).mp hψ
  rw [show CFSG.conjugate (centerOf (fsuU T V)) g = rconj (centerOf (fsuU T V)) g from rfl,
    mem_rconj] at hz
  have hzV₂ : z ∈ V₂ := by
    have h1 : g * z * g⁻¹ ∈ V₂ := C.base.plane.2 (C.base.zU ▸ hz)
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ C.base.gV₂_F4) _).mp h1
    rwa [inv_inv, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h2
  have hzU := C.base.V2U_F4 hzV₂
  rw [Subgroup.mem_bot]
  exact L128A.HatU.rho_eq_one_of_mem D C.base.comm_center_F4 hzU hzN

theorem finrank_add_F4 : Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) +
    Nat.log 2 (Nat.card (img8 D e (CFSG.conjugate (l32nW T V V₂) g))) = 7 := by
  have h := C.hat5
  rw [C.img_zUg_F4, Subgroup.relIndex_bot_left, finrank_V e] at h
  rw [card_img8]
  exact h

theorem card_hatE_sq_F4 : Nat.card ↥(D.hat (l32nE T V V₂ g)) ^ 2 ≤ 256 := by
  have hEU : l32nE T V V₂ g ≤ fsuU T V := inf_le_left.trans inf_le_left
  have hEc : ∀ x ∈ l32nE T V V₂ g, ∀ y ∈ l32nE T V V₂ g, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (C.base.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [← card_V e]
  exact card_sq_le_of_isotropic D.nondegenerate (D.isotropic_hat hEU hEc)

theorem img_Wg_le_s8_F4 : img8 D e (CFSG.conjugate (l32nW T V V₂) g) ≤ s8 :=
  (img8_mono D e C.base.WgH_F4).trans C.imgH.le

theorem img_Wg_fix_F4 {x : GL (Fin 8) (ZMod 2)}
    (hx : x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g)) :
    (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vR) = vec8 vR := by
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
  rw [← C.ePiA, matOf_mulVec, C.base.rho_Wg_pi_a_F4 D C.aV₂ hw hwN]

theorem img_Wg_comm_F4 : ∀ x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g),
    ∀ y ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g), x * y = y * x := by
  intro x hx y hy
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
  obtain ⟨w', hw', hw'N, rfl⟩ := (mem_img8 D e).mp hy
  have hm : w * w' * w⁻¹ * w'⁻¹ ∈ CFSG.conjugate (l32nW T V V₂) g :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hw') (Subgroup.inv_mem _ hw))
      (Subgroup.inv_mem _ hw')
  have h1 := (C.base.matOf_eq_one_iff_F4 D e (C.base.WgH_F4 hm)).mpr (C.base.comm_mem_Q_F4 D hw hw')
  have e1 : (⟨w * w' * w⁻¹ * w'⁻¹, L14332.l32nH_le_normalizer_fsuU T V (C.base.WgH_F4 hm)⟩ :
        ↥(Subgroup.normalizer (fsuU T V : Set G))) =
      ⟨w, hwN⟩ * ⟨w', hw'N⟩ * ⟨w, hwN⟩⁻¹ * ⟨w', hw'N⟩⁻¹ := rfl
  rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
    map_inv] at h1
  calc matOf e (D.ρ ⟨w, hwN⟩) * matOf e (D.ρ ⟨w', hw'N⟩)
      = (matOf e (D.ρ ⟨w, hwN⟩) * matOf e (D.ρ ⟨w', hw'N⟩) * (matOf e (D.ρ ⟨w, hwN⟩))⁻¹ *
          (matOf e (D.ρ ⟨w', hw'N⟩))⁻¹) * matOf e (D.ρ ⟨w', hw'N⟩) *
            matOf e (D.ρ ⟨w, hwN⟩) := by group
    _ = matOf e (D.ρ ⟨w', hw'N⟩) * matOf e (D.ρ ⟨w, hwN⟩) := by rw [h1, one_mul]

theorem conj_mem_img_F4 {n : GL (Fin 8) (ZMod 2)} (hn : n ∈ s8)
    (hnfix : (n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vR) = vec8 vR)
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g)) :
    n * x * n⁻¹ ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
  obtain ⟨h, hh, hhN, rfl⟩ := (mem_img8 D e).mp (by rw [C.imgH]; exact hn)
  have hfix : D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩ (D.π a) = D.π a := by
    apply e.injective
    rw [← matOf_mulVec, C.ePiA]
    exact hnfix
  have hhV₂ := C.base.mem_normalizer_of_fix_F4 D C.aV₂ C.aV₁ hh hfix
  have hconj : h * w * h⁻¹ ∈ CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V :=
    (Subgroup.mem_normalizer_iff.mp (C.base.nWg ⟨hh, hhV₂⟩) w).mp (Subgroup.mem_sup_left hw)
  have h1 : img8 D e (CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V) =
      img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
    rw [img8_sup D e (C.base.WgH_F4.trans HN) (fun c (hc : c ∈ l32nCHat T V) => HN hc.1),
      img8_cHat, sup_bot_eq]
  rw [← h1]
  refine (mem_img8 D e).mpr ⟨h * w * h⁻¹, hconj,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN) (Subgroup.inv_mem _ hhN), ?_⟩
  rw [show (⟨h * w * h⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hwN)
      (Subgroup.inv_mem _ hhN)⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
      ⟨h, hhN⟩ * ⟨w, hwN⟩ * ⟨h, hhN⟩⁻¹ from rfl, map_mul, map_mul, map_inv, map_mul,
    map_mul, map_inv]

end Ctx8_F4

section Cert


namespace Ctx8_F4
open CFSG.Quasithin.H13.L1442E8.Ctx8_F4

variable (C : Ctx8_F4 G T L V V₂ g a D e)
include C

theorem img_Wg_le_F4 : img8 D e (CFSG.conjugate (l32nW T V V₂) g) ≤ Z8 := by
  intro x hx
  refine mem_Z8_of (C.img_Wg_le_s8_F4 hx) (C.img_Wg_fix_F4 hx) ?_ fun n hn hnfix =>
    C.img_Wg_comm_F4 _ hx _ (C.conj_mem_img_F4 hn hnfix hx)
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp hx
  rw [← map_mul, ← map_mul]
  have e1 : (⟨w, hwN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) * ⟨w, hwN⟩ =
      ⟨w * w, L14332.l32nH_le_normalizer_fsuU T V (C.base.WgH_F4 (Subgroup.mul_mem _ hw hw))⟩ := rfl
  rw [e1]
  exact (C.base.matOf_eq_one_iff_F4 D e (C.base.WgH_F4 (Subgroup.mul_mem _ hw hw))).mpr
    (C.base.sq_mem_Q_F4 D hw)

theorem mem_hatE_F4 (hN : N8 ≤ img8 D e (CFSG.conjugate (l32nW T V V₂) g)) :
    ∀ p ∈ eW8, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈ (D.hat (l32nE T V V₂ g)).map e.toLinearMap := by
  obtain ⟨_, S⟩ := C.base.set14_F4
  have haU := C.base.V2U_F4 C.aV₂
  intro p hp
  obtain ⟨hp1, hp2⟩ := wB_spec.1 p hp
  obtain ⟨w₀, hw₀⟩ := mem_elemsOf hp1
  obtain ⟨x, hxN, hx⟩ := exists_evalW S8Cert.n8G (subB_spec nB_spec.2.1).2.2.2.2
    (unit_of_s8E N8_gens_mem) w₀
  obtain ⟨w, hw, hwN, rfl⟩ := (mem_img8 D e).mp (hN hxN)
  obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm (vec8 p.2))
  have hev : e (D.π u) = vec8 p.2 := by rw [hue, LinearEquiv.apply_symm_apply]
  have huW : u ∈ l32nW T V V₂ := by
    refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hB : D.B (D.π u) (D.π a) = 0 := by
      rw [C.form, hev, C.ePiA, ← b4N_spec, hp2]
      rfl
    have hua : u * a * u⁻¹ * a⁻¹ = 1 := (D.B_spec u hu a haU).mp hB
    have hua' : a * u = u * a := by
      calc a * u = (u * a * u⁻¹ * a⁻¹)⁻¹ * u * a := by group
        _ = u * a := by rw [hua]; group
    have hcen : ∀ z ∈ fsuV1 T V, z * u = u * z := fun z hz => by
      rw [← C.base.zU] at hz
      exact (Subgroup.mem_centralizer_iff.mp hz.2 u hu).symm
    rcases S.mem_V2_F4 C.aV₂ C.aV₁ hv with h1 | h1
    · exact hcen v h1
    · have haa : a * a = 1 := S.mul_self_V_F4 (C.base.plane.1.1 C.aV₂)
      have hv' : v = a * (a * v) := by rw [← mul_assoc, haa, one_mul]
      rw [hv']
      calc a * (a * v) * u = a * ((a * v) * u) := by group
        _ = a * (u * (a * v)) := by rw [hcen _ h1]
        _ = (a * u) * (a * v) := by group
        _ = u * (a * (a * v)) := by rw [hua']; group
  have hcommE : w * u * w⁻¹ * u⁻¹ ∈ l32nE T V V₂ g := by
    have h1 := C.base.wwE (Subgroup.commutator_mem_commutator huW hw)
    have h2 : w * u * w⁻¹ * u⁻¹ = (u * w * u⁻¹ * w⁻¹)⁻¹ := by group
    rw [h2]
    exact Subgroup.inv_mem _ (by simpa [commutatorElement_def] using h1)
  have hcU : w * u * w⁻¹ * u⁻¹ ∈ fsuU T V :=
    Subgroup.mul_mem _ (L128A.HatU.conj_mem hwN hu) (Subgroup.inv_mem _ hu)
  refine ⟨D.π (w * u * w⁻¹ * u⁻¹), L128A.HatU.π_mem_hat D hcommE hcU, ?_⟩
  rw [← L128A.HatU.rho_sub_π D hwN hu, sub_eq_add_neg, neg_eq_self_zmod2, LinearEquiv.coe_coe,
    map_add, ← matOf_mulVec, hev, hx, dec8_mulVec, hw₀, vec8_xor]

end Ctx8_F4

end Cert

end CFSG.Quasithin.H13.L1442E8
