module

public import CFSG.LargeExtraspecial.S6Swap
public import CFSG.LargeExtraspecial.S4SevenCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

section Sp

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] {β : LinearMap.BilinForm (ZMod 2) U}

theorem exists_apply_eq_one_both (hnd : β.Nondegenerate) {u v : U} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ w, β u w = 1 ∧ β v w = 1 := by
  obtain ⟨w₁, hw₁⟩ : ∃ w, β u w ≠ 0 := by
    by_contra! h
    exact hu (hnd.1 u h)
  obtain ⟨w₂, hw₂⟩ : ∃ w, β v w ≠ 0 := by
    by_contra! h
    exact hv (hnd.1 v h)
  have h1 := zmod2_eq_one_of_ne_zero hw₁
  have h2 := zmod2_eq_one_of_ne_zero hw₂
  rcases zmod2_eq_zero_or_eq_one (β v w₁) with h3 | h3
  · rcases zmod2_eq_zero_or_eq_one (β u w₂) with h4 | h4
    · exact ⟨w₁ + w₂, by rw [map_add, h1, h4, add_zero], by rw [map_add, h3, h2, zero_add]⟩
    · exact ⟨w₂, h4, h2⟩
  · exact ⟨w₁, h1, h3⟩

theorem spDer_transitive (hβ : β.IsAlt) (hnd : β.Nondegenerate) {u v : U} (hu : u ≠ 0)
    (hv : v ≠ 0) : ∃ x ∈ spDer β hβ, x u = v := by
  by_cases huv : u = v
  · exact ⟨1, one_mem _, by rw [huv]; rfl⟩
  obtain ⟨w, huw, hvw⟩ := exists_apply_eq_one_both hnd hu hv
  have hwv : β w v = 1 := by rw [isAlt_symm hβ, hvw]
  have h1 : u + w ≠ 0 := by
    intro h0
    have : w = u := by rw [← vec_neg u, ← sub_eq_zero, sub_neg_eq_add, add_comm, h0]
    rw [this, hβ.self_eq_zero] at huw
    exact zero_ne_one huw
  have h2 : w + v ≠ 0 := by
    intro h0
    have : w = v := by rw [← vec_neg v, ← sub_eq_zero, sub_neg_eq_add, h0]
    rw [this, hβ.self_eq_zero] at hvw
    exact zero_ne_one hvw
  have e1 : spTransvection β hβ (u + w) u = w := by
    rw [spTransvection_apply, map_add, hβ.self_eq_zero, huw, zero_add, one_smul, ← add_assoc,
      vec_add_self, zero_add]
  have e2 : spTransvection β hβ (w + v) w = v := by
    rw [spTransvection_apply, map_add, hβ.self_eq_zero, hwv, zero_add, one_smul, ← add_assoc,
      vec_add_self, zero_add]
  refine ⟨spTransvection β hβ (w + v) * spTransvection β hβ (u + w),
    spTransvection_mul_mem_spDer hβ h2 h1, ?_⟩
  rw [LinearEquiv.mul_apply, e1, e2]

theorem transitive_of_a6Pair [FiniteDimensional (ZMod 2) U] {X E₀ : Subgroup (U ≃ₗ[ZMod 2] U)}
    {a : U} (hA : A6Pair X E₀ a) (ha : a ≠ 0) {v : U} (hv : v ≠ 0) : ∃ x ∈ X, x a = v := by
  obtain ⟨-, β, hβ, hnd, hX, -⟩ := hA
  rw [hX, commutator_isometryGroup_eq hβ hnd]
  exact spDer_transitive hβ hnd ha hv

end Sp

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Nbar_eq_N0bar_of_omegaCase (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) : Nbar S g t = N0bar S g t := by
  rcases Nbar_eq_N0bar_or hCE H C ht (dtEqConj_of_omegaCase H hNo C hΩ)
    (naturalPair_of_omegaCase H hNo C hΩ) with h | ⟨hA, -⟩
  · exact h
  · exfalso
    obtain ⟨v, hv0, hv⟩ := hΩ.not_transitive
    exact hv (transitive_of_a6Pair hA (aV_ne_zero H ht) hv0)

theorem apply_sub_mem_Vt_of_mem_N0bar (H : Hyp4 S g) {t : S.O}
    (hL : ∀ k ∈ S.Lbar g ⊓ Nbar S g t, ∀ w ∈ Wt S g t,
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {x : S.O} (hx : x ∈ N0bar S g t) {w : S.Qt} (hw : w ∈ Wt S g t) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  have haQ := H.conj_mem
  let K : Subgroup S.O :=
    { carrier := {x | x ∈ Nbar S g t ∧ ∀ w ∈ Wt S g t,
        (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t}
      mul_mem' := by
        rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
        refine ⟨mul_mem hxN hyN, fun w hw => ?_⟩
        rw [coe_mul_apply, show (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w =
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
            (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) by abel]
        exact add_mem (hx _ (apply_mem_Wt H (Nbar_le_Rbar hyN) hw)) (hy w hw)
      one_mem' := ⟨one_mem _, fun w _ => by
        rw [show ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w from rfl, sub_self]
        exact Submodule.zero_mem _⟩
      inv_mem' := by
        rintro x ⟨hxN, hx⟩
        refine ⟨inv_mem hxN, fun w hw => ?_⟩
        have h1 := hx _ (apply_mem_Wt H (inv_mem (Nbar_le_Rbar hxN)) hw)
        rw [apply_inv_apply_O] at h1
        have h2 := neg_mem h1
        rwa [neg_sub] at h2 }
  have hle : N0bar S g t ≤ K := by
    refine iSup₂_le fun k hk => ?_
    rintro y ⟨hyL, hyN⟩
    refine ⟨hyN, fun w hw => ?_⟩
    obtain ⟨y₀, hy₀, rfl⟩ := (Lbar_mul S k g ▸ hyL : y ∈ (S.Lbar g).map _)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyN ⊢
    have hc := commute_of_mem_Rbar haQ hk
    have hc' : S.ρ k⁻¹ * t = t * S.ρ k⁻¹ := by rw [map_inv]; exact commute_inv hc
    have hy₀N : y₀ ∈ Nbar S g t := by
      have := conj_mem_Nbar haQ hc' hyN
      simpa [map_inv, mul_assoc] using this
    have hw' := apply_mem_Wt H (inv_mem hk) hw
    have h1 := hL y₀ ⟨hy₀, hy₀N⟩ _ hw'
    have h2 := apply_mem_Vt_of_mem_Rbar haQ hk h1
    rw [map_sub, apply_inv_apply_O, ← coe_mul_apply, ← coe_mul_apply] at h2
    exact h2
  exact (hle hx).2 w hw

section One

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include H C ht ht1 hVQ hh hb

theorem timmesfeld_6_1_one_W (hΩ : OmegaCase H C ht ht1 hVQ) :
    W S g t = (S.Qa g ⊓ W S g t) ⊔ (S.Qa ((h : G) * g) ⊓ W S g t) := by
  have hdec := sup_eq_Wt H C ht ht1 hVQ hh hb (clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb
    (radBound_of_omegaCase H C ht ht1 hVQ hΩ))
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_right inf_le_right)
  have hxQ : x ∈ S.QG := hx.1
  have hxW : S.cl x ∈ Wt S g t := clSub_W (S := S) ▸ S.cl_mem_clSub hx hxQ
  rw [← hdec] at hxW
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxW
  obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hu.1
  obtain ⟨y', hy', hy'Q, rfl⟩ := S.mem_clSub_iff.mp hv.1
  have hyW : y ∈ W S g t := by rw [W_eq_clPre]; exact ⟨hyQ, hu.2⟩
  have hy'W : y' ∈ W S g t := by rw [W_eq_clPre]; exact ⟨hy'Q, hv.2⟩
  have hzW : S.z ∈ W S g t := by rw [W_eq_clPre]; exact S.z_mem_clPre _
  have hmem : y * y' ∈ (S.Qa g ⊓ W S g t) ⊔ (S.Qa ((h : G) * g) ⊓ W S g t) :=
    mul_mem (mem_sup_left ⟨hy.2, hyW⟩) (mem_sup_right ⟨hy'.2, hy'W⟩)
  rw [← S.cl_mul hyQ hy'Q] at huv
  rcases (S.cl_eq_cl_iff (S.QG.mul_mem hyQ hy'Q) hxQ).mp huv with rfl | rfl
  · exact hmem
  · exact mul_mem hmem (mem_sup_left ⟨S.z_mem_Qa H.conj_mem H.conj_ne, hzW⟩)

theorem timmesfeld_6_1_one (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) {x : S.O} (hx : x ∈ Nbar S g t) {w : S.Qt}
    (hw : w ∈ Wt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  have hR := radBound_of_omegaCase H C ht ht1 hVQ hΩ
  rw [Nbar_eq_N0bar_of_omegaCase hCE H hNo C ht ht1 hVQ hΩ] at hx
  exact apply_sub_mem_Vt_of_mem_N0bar H (fun k hk w hw => apply_sub_mem_Vt_a H C ht ht1 hVQ hh hb
    (clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb hR) hk hw) hx hw

end One

end CFSG.LargeExtraspecial.S6
