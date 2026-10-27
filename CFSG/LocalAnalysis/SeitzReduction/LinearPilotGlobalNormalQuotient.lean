module

import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormal

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore)
open CFSG.EvenSmallLie (StandardSetting)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut)

section CenterQuotient

variable {X : Type*} [Group X]

theorem centerQuotientAut_coe (α : MulAut X) (x : X) :
    centerQuotientAut α (x : X ⧸ center X) = ((α x : X) : X ⧸ center X) :=
  F4Pilot.centerQuotientAut_mk α x

theorem centerQuotientAut_mul (α β : MulAut X) :
    centerQuotientAut (α * β) = centerQuotientAut α * centerQuotientAut β := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAut.mul_apply, centerQuotientAut_coe, centerQuotientAut_coe, centerQuotientAut_coe,
    MulAut.mul_apply]

theorem centerQuotientAut_one : centerQuotientAut (1 : MulAut X) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [centerQuotientAut_coe, MulAut.one_apply, MulAut.one_apply]

theorem comap_fixedSubgroup_centerQuotientAut (α : MulAut X) :
    (fixedSubgroup (centerQuotientAut α)).comap (QuotientGroup.mk' (center X)) =
      twistedFix (fun _ : Unit => α) (center X) le_rfl := by
  ext x
  rw [mem_comap, mem_twistedFix]
  change centerQuotientAut α (x : X ⧸ center X) = (x : X ⧸ center X) ↔ _
  rw [centerQuotientAut_coe, QuotientGroup.eq]
  constructor
  · intro h _
    have h1 : x * (α x)⁻¹ ∈ center X := (center X).normal_of_characteristic.mem_comm h
    have h2 := Subgroup.inv_mem _ h1
    rwa [mul_inv_rev, inv_inv] at h2
  · intro h
    have h1 := Subgroup.inv_mem _ (h ())
    rw [mul_inv_rev, inv_inv] at h1
    exact (center X).normal_of_characteristic.mem_comm h1

theorem fixAll_const_eq_fixedSubgroup (α : MulAut X) :
    fixAll (fun _ : Unit => α) = fixedSubgroup α := by
  ext x
  rw [mem_fixAll]
  exact ⟨fun h => h (), fun h _ => h⟩

theorem perfectCore_fixedSubgroup_centerQuotientAut [Finite X] (α : MulAut X) :
    perfectCore (fixedSubgroup (centerQuotientAut α)) =
      (perfectCore (fixedSubgroup α)).map (QuotientGroup.mk' (center X)) := by
  rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (center X))
      (fixedSubgroup (centerQuotientAut α)),
    ← CFSG.Quasithin.map_perfectCore, comap_fixedSubgroup_centerQuotientAut,
    perfectCore_twistedFix, fixAll_const_eq_fixedSubgroup]

end CenterQuotient

theorem injective_mk_inclusion_of_mulEquiv_projectiveSL {G : Type*} [Group G]
    {L G₀ : Subgroup G} {n : ℕ} {K : Type*} [Field K] (hn : 3 ≤ n) (e : L ≃* projectiveSL n K)
    (hLG₀ : L ≤ G₀) :
    Function.Injective ((QuotientGroup.mk' (center G₀)).comp (inclusion hLG₀)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  have hZ : center L = ⊥ := by
    rw [← map_center_eq e.symm, CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn,
      Subgroup.map_bot]
  have hxZ : x ∈ center L := mem_center_iff.mpr fun y => by
    have h := mem_center_iff.mp hx (inclusion hLG₀ y)
    exact inclusion_injective hLG₀ (by rw [map_mul, map_mul]; exact h)
  rw [hZ, mem_bot] at hxZ
  exact hxZ

section Global

variable {G : Type} [Group G] [Finite G] {L G₀ : Subgroup G} {n : ℕ} {K F : Type} [Field K]
  [Finite K] [Field F] [Finite F] [CharP F 2]

theorem exists_mulEquiv_globalNormal_center (hn : 3 ≤ n) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (e : L ≃* projectiveSL n K) (ψ₀ : G₀ ⧸ center G₀ ≃* projectiveSL n F) (hLG₀ : L ≤ G₀)
    {t : G} (ht : t ^ 2 = 1) (htG₀ : t ∈ normalizer (G₀ : Set G))
    (hCt : perfectCore (G₀ ⊓ centralizer ({t} : Set G)) = L) :
    ∃ ψ : G₀ ⧸ center G₀ ≃* projectiveSL n F,
      (∀ x : L, ψ ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) = projMap n ι (e x)) ∧
      ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
        fieldAut n F σ (ψ (x : G₀ ⧸ center G₀)) := by
  set θ := G₀.normalizerMonoidHom ⟨t, htG₀⟩ with hθdef
  have hθ : θ * θ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one G₀ htG₀ ht
  have hθ' : centerQuotientAut θ * centerQuotientAut θ = 1 := by
    rw [← centerQuotientAut_mul, hθ, centerQuotientAut_one]
  set q := (QuotientGroup.mk' (center G₀)).comp (inclusion hLG₀) with hqdef
  set ε : projectiveSL n K →* G₀ ⧸ center G₀ := q.comp e.symm.toMonoidHom with hεdef
  have hε : Function.Injective ε :=
    (injective_mk_inclusion_of_mulEquiv_projectiveSL hn e hLG₀).comp e.symm.injective
  have hcore : perfectCore (fixedSubgroup θ) = L.subgroupOf G₀ := by
    rw [hθdef, F4Pilot.fixedSubgroup_normalizerMonoidHom]
    apply Subgroup.map_injective G₀.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, subgroupOf_map_subtype, inf_comm, hCt,
      subgroupOf_map_subtype, inf_eq_left.mpr hLG₀]
  have hεr : ε.range = perfectCore (fixedSubgroup (centerQuotientAut θ)) := by
    rw [perfectCore_fixedSubgroup_centerQuotientAut, hcore, hεdef, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e.symm.surjective, ← MonoidHom.range_eq_map, hqdef,
      MonoidHom.range_comp, Subgroup.inclusion_range]
  obtain ⟨ψ, hψε, hψθ⟩ :=
    exists_mulEquiv_projMap_eq hn ι hσ1 hσσ hfix ψ₀ hθ' ε hε hεr
  refine ⟨ψ, fun x => ?_, fun x => ?_⟩
  · have hx : ε (e x) = ((inclusion hLG₀ x : G₀) : G₀ ⧸ center G₀) := by
      rw [hεdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rfl
    rw [← hx, hψε]
  · rw [← hψθ, centerQuotientAut_coe]

end Global

end CFSG.SeitzReduction.LinearPilot
