module

public import CFSG.LargeExtraspecial.S8Rad
public import CFSG.LargeExtraspecial.S8Comm
public import CFSG.LargeExtraspecial.S8FusB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] noncomputable def commWV (t τ : S.O) : Submodule (ZMod 2) (S.Qt ⧸ Vt S g t) :=
  ((Wt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).map (Vt S g t).mkQ

variable (S g) in
@[expose] noncomputable def fixWV (t τ : S.O) : Submodule (ZMod 2) S.Qt :=
  Wt S g t ⊓ (Vt S g t).comap ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)

theorem mem_commWV {t τ : S.O} {u : S.Qt ⧸ Vt S g t} :
    u ∈ commWV S g t τ ↔
      ∃ w ∈ Wt S g t, (Vt S g t).mkQ ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) = u := by
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem mem_fixWV {t τ : S.O} {w : S.Qt} :
    w ∈ fixWV S g t τ ↔ w ∈ Wt S g t ∧ (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t :=
  Iff.rfl

theorem finrank_commWV_add_finrank_fixWV (t τ : S.O) :
    finrank (ZMod 2) (commWV S g t τ) + finrank (ZMod 2) (fixWV S g t τ) =
      finrank (ZMod 2) (Wt S g t) := by
  have h := finrank_map_add_finrank_inf_ker
    ((Vt S g t).mkQ ∘ₗ ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) (Wt S g t)
  rwa [Submodule.map_comp, LinearMap.ker_comp, Submodule.ker_mkQ] at h

theorem finrank_WV_add_finrank_Vt (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) :
    finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) + finrank (ZMod 2) (Vt S g t) =
      finrank (ZMod 2) (Wt S g t) := by
  have h := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ (Wt S g t)
  rwa [Submodule.ker_mkQ, inf_eq_right.mpr (Vt_le_Wt H ht1)] at h

theorem commWV_le (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) {τ : S.O} (hτt : τ * t = t * τ) :
    commWV S g t τ ≤ (Wt S g t).map (Vt S g t).mkQ := by
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨_, (Wt S g t).sub_mem (apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hw) hw, rfl⟩

theorem finrank_commSpace_conj (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {x τ : S.O} (hxτ : τ = x * t * x⁻¹) :
    finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = finrank (ZMod 2) (Vt S g t) := by
  rw [hxτ, commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1, LinearEquiv.finrank_map_eq]

theorem finrank_commWV_le (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {x τ : S.O} (hxτ : τ = x * t * x⁻¹) :
    finrank (ZMod 2) (commWV S g t τ) ≤ finrank (ZMod 2) (Vt S g t) := by
  rw [← finrank_commSpace_conj H C ht ht1 hVQ hxτ]
  refine (Submodule.finrank_map_le _ _).trans (Submodule.finrank_mono ?_)
  exact LinearMap.map_le_range

theorem finrank_commWV_add_one_le (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {x τ : S.O}
    (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ) {v : S.Qt} (hv : v ∈ Vt S g t)
    (hτv : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v) :
    finrank (ZMod 2) (commWV S g t τ) + 1 ≤ finrank (ZMod 2) (Vt S g t) := by
  set K := (Wt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) with hK
  have h := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ K
  rw [Submodule.ker_mkQ] at h
  have hτvV : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
    have hV := (commSpace_t_eq H C ht ht1 hVQ).1
    rw [← hV] at hv ⊢
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    refine mem_commSpace.mpr ⟨(τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w, ?_⟩
    rw [map_sub, ← coe_mul_apply, ← coe_mul_apply, hτt]
  have hmem : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ K ⊓ Vt S g t :=
    ⟨⟨v, Vt_le_Wt H ht1 hv, rfl⟩, (Vt S g t).sub_mem hτvV hv⟩
  have hne : K ⊓ Vt S g t ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hτv hmem
  have h1 : 1 ≤ finrank (ZMod 2) (K ⊓ Vt S g t : Submodule (ZMod 2) S.Qt) :=
    Submodule.one_le_finrank_iff.mpr hne
  have h2 : finrank (ZMod 2) K ≤ finrank (ZMod 2) (Vt S g t) := by
    rw [← finrank_commSpace_conj H C ht ht1 hVQ hxτ]
    exact Submodule.finrank_mono LinearMap.map_le_range
  change finrank (ZMod 2) (K.map (Vt S g t).mkQ) + 1 ≤ _
  omega

theorem mkQ_apply_mem_commWV (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {τ r : S.O} (hτt : τ * t = t * τ) (hr : r ∈ Rbar S g t)
    (hrτ : r * τ * r⁻¹ * τ⁻¹ ∈ Nbar S g t) {u : S.Qt} (hu : (Vt S g t).mkQ u ∈ commWV S g t τ) :
    (Vt S g t).mkQ ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) u) ∈ commWV S g t τ := by
  obtain ⟨w, hw, hwu⟩ := mem_commWV.mp hu
  have hv : u - ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ Vt S g t := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    change (Vt S g t).mkQ u - (Vt S g t).mkQ _ = 0
    rw [hwu, sub_self]
  have hrt := commute_of_mem_Rbar H.conj_mem hr
  have hrw : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t :=
    apply_mem_Wt_of_commute H C ht ht1 hVQ hrt hw
  have hτrw : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Wt S g t :=
    apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hrw
  set n := r * τ * r⁻¹ * τ⁻¹ with hn
  have hrτ' : r * τ = n * (τ * r) := by rw [hn]; group
  have e : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) =
      ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) +
      ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) -
        (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := by
    rw [map_sub, ← coe_mul_apply, ← coe_mul_apply, ← coe_mul_apply, hrτ']
    abel
  have h1 := hN n hrτ _ hτrw
  have h2 : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (u - ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) ∈ Vt S g t :=
    apply_mem_Vt_of_mem_Rbar H.conj_mem hr hv
  refine mem_commWV.mpr ⟨_, hrw, ?_⟩
  symm
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have e2 : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u -
      ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (u - ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w)) +
      ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) -
        (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := by
    rw [map_sub (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u, e]
    abel
  rw [e2]
  exact (Vt S g t).add_mem h2 h1

theorem apply_mem_fixWV (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t)
    {τ r : S.O} (hτt : τ * t = t * τ) (hr : r ∈ Rbar S g t)
    (hτr : τ * r * τ⁻¹ * r⁻¹ ∈ Nbar S g t) {w : S.Qt} (hw : w ∈ fixWV S g t τ) :
    (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ fixWV S g t τ := by
  obtain ⟨hwW, hwV⟩ := mem_fixWV.mp hw
  have hrt := commute_of_mem_Rbar H.conj_mem hr
  have hrw : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wt S g t :=
    apply_mem_Wt_of_commute H C ht ht1 hVQ hrt hwW
  have hrτw : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Wt S g t :=
    apply_mem_Wt_of_commute H C ht ht1 hVQ hrt (apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hwW)
  obtain ⟨n, hn⟩ : ∃ n, n = τ * r * τ⁻¹ * r⁻¹ := ⟨_, rfl⟩
  rw [← hn] at hτr
  have hτr' : τ * r = n * (r * τ) := by rw [hn]; group
  refine mem_fixWV.mpr ⟨hrw, ?_⟩
  have h1 : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      (n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) := by
    rw [← coe_mul_apply, hτr', coe_mul_apply, coe_mul_apply]
  have e : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
      ((n : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) -
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) +
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by
    rw [h1, map_sub]
    abel
  rw [e]
  exact (Vt S g t).add_mem (hN n hτr _ hrτw) (apply_mem_Vt_of_mem_Rbar H.conj_mem hr hwV)

end CFSG.LargeExtraspecial.S8
