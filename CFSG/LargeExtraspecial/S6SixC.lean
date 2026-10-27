module

public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S4FiveBeta
public import CFSG.LargeExtraspecial.S6Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] noncomputable def dualPair (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Vt S g t) :=
  ((fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).liftQ (betaAux S g t)
    ((fixSpace_le_Wt H ht ht1).trans Wt_le_ker_betaAux)).comp (chiU S t).symm.toLinearMap

section Pair

variable (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
include H ht ht1

theorem dualPair_chiU (y : S.Qt) (v : Vt S g t) :
    dualPair H ht ht1 (chiU S t (Submodule.Quotient.mk y)) v = polar S.q v y := by
  simp [dualPair, betaAux_apply]

theorem dualPair_apply_of {u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)} {y : S.Qt}
    (hy : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y = u) (v : Vt S g t) :
    dualPair H ht ht1 u v = polar S.q v y := by
  have hu : chiU S t (Submodule.Quotient.mk y) = u := Subtype.ext hy
  rw [← hu, dualPair_chiU H ht ht1]

theorem ker_dualPair :
    LinearMap.ker (dualPair H ht ht1) =
      (Tt S g t).comap (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).subtype := by
  ext u
  obtain ⟨y, hy⟩ := mem_commSpace.mp u.2
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h0
    have hyW : y ∈ Wt S g t := mem_Wt.mpr fun v hv => by
      have := LinearMap.congr_fun h0 ⟨v, hv⟩
      rwa [dualPair_apply_of H ht ht1 hy, LinearMap.zero_apply] at this
    rw [← hy]
    exact sub_mem_Tt hyW
  · intro hT
    obtain ⟨w, hw, hwu⟩ := mem_Tt.mp hT
    ext v
    rw [dualPair_apply_of H ht ht1 hwu, LinearMap.zero_apply]
    exact mem_Wt.mp hw v v.2

theorem finrank_commSpace_eq :
    finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Tt S g t) + finrank (ZMod 2) (Vt S g t) := by
  have h3 := S2.finrank_map_sub_one_add (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (Wt S g t)
  rw [inf_eq_right.mpr (fixSpace_le_Wt H ht ht1)] at h3
  have h5 := finrank_commSpace_add_finrank_fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have h6 := finrank_Wt (S := S) (g := g) (t := t)
  change finrank (ZMod 2) (Tt S g t) + _ = _ at h3
  omega

theorem dualPair_surjective : Function.Surjective (dualPair H ht ht1) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have h1 := LinearMap.finrank_range_add_finrank_ker (dualPair H ht ht1)
  rw [ker_dualPair H ht ht1,
    (Submodule.comapSubtypeEquivOfLe (Tt_le_commSpace (S := S) (g := g) (t := t))).finrank_eq,
    finrank_commSpace_eq H ht ht1] at h1
  rw [Subspace.dual_finrank_eq]
  omega

theorem dualPair_apply_apply {x : S.O} (hx : x ∈ Rbar S g t)
    (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) (v : Vt S g t)
    (hu : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hv : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t) :
    dualPair H ht ht1 ⟨_, hu⟩ ⟨_, hv⟩ = dualPair H ht ht1 u v := by
  obtain ⟨y, hy⟩ := mem_commSpace.mp u.2
  have hxy : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) y) -
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) y = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by
    rw [← hy, map_sub, ← coe_mul_apply, ← coe_mul_apply, commute_of_mem_Rbar H.conj_mem hx]
  rw [dualPair_apply_of H ht ht1 hxy, dualPair_apply_of H ht ht1 hy,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2]

@[expose] noncomputable def dualEquiv :
    (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ⧸
        (Tt S g t).comap (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).subtype) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (Vt S g t) :=
  (Submodule.quotEquivOfEq _ _ (ker_dualPair H ht ht1).symm).trans
    ((dualPair H ht ht1).quotKerEquivOfSurjective (dualPair_surjective H ht ht1))

theorem dualEquiv_mk (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    dualEquiv H ht ht1 (Submodule.Quotient.mk u) = dualPair H ht ht1 u := by
  simp [dualEquiv]

theorem timmesfeld_6_6_three :
    ∃ e : (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ⧸
        (Tt S g t).comap (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).subtype) ≃ₗ[ZMod 2]
          Module.Dual (ZMod 2) (Vt S g t),
      ∀ x ∈ Rbar S g t, ∀ (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) (v : Vt S g t)
        (hu : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
        (hv : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t),
        e (Submodule.Quotient.mk ⟨_, hu⟩) ⟨_, hv⟩ = e (Submodule.Quotient.mk u) v := by
  refine ⟨dualEquiv H ht ht1, fun x hx u v hu hv => ?_⟩
  rw [dualEquiv_mk, dualEquiv_mk]
  exact dualPair_apply_apply H ht ht1 hx u v hu hv

theorem mem_Nbar_of_apply_sub_mem_Tt {x : S.O} (hx : x ∈ Rbar S g t)
    (hxU : ∀ u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Tt S g t) : x ∈ Nbar S g t := by
  refine ⟨hx, fun v hv => ?_⟩
  have hx' : ∀ u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Tt S g t := by
    intro u hu
    have e : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
        -(((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u)) := by
      rw [map_sub, inv_apply_apply_O]
      abel
    rw [e]
    exact neg_mem (apply_mem_Tt H (inv_mem hx) (hxU u hu))
  have hW : ∀ y : S.Qt, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ Wt S g t := by
    intro y
    obtain ⟨w, hw, hwe⟩ := mem_Tt.mp (hx' _ (sub_mem_commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) y))
    have hcomm : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) =
        ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) y) := by
      rw [← coe_mul_apply, ← coe_mul_apply, commute_of_mem_Rbar H.conj_mem (inv_mem hx)]
    have e2 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w +
        (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) -
          ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y)) := by
      rw [← hwe]
      abel
    have hfix : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y - w ∈
        fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [mem_fixSpace, map_sub, map_sub, hcomm, e2,
        map_sub ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)]
      abel
    have h1 := (fixSpace_le_Wt H ht ht1) hfix
    have h2 := add_mem h1 hw
    rwa [sub_add_cancel] at h2
  apply sub_eq_zero.mp
  refine S.q_nondegenerate.1 _ fun y => ?_
  rw [polarBilin_apply_apply, polar_sub_left]
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2 v
    (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y)
  rw [apply_inv_apply_O] at h1
  rw [h1, ← polar_sub_right]
  exact mem_Wt.mp (hW y) v hv

end Pair

end CFSG.LargeExtraspecial.S6
