module

public import CFSG.LocalAnalysis.ComponentInitial.BlockSylowOrder
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification OuterAutomorphisms

variable {H : Type*} [Group H] [Finite H]

theorem unique_perfect_component_normalizer_enters_layer {A : Subgroup H}
    (hA : Group.IsPerfect A) (hAF : ⁅A, CFSG.fittingSubgroup H⁆ = ⊥)
    (hnorm : ∀ K : Subgroup H, CFSG.IsComponent K → A ≤ normalizer (K : Set H))
    (hout : ∀ K : Subgroup H, CFSG.IsComponent K → Group.IsSolvable (Outer (K ⧸ center K))) :
    A ≤ CFSG.layer H := by
  classical
  have hinner : ∀ a ∈ A, ∀ K : CFSG.LocalCores.ComponentIndex H,
      ∃ k : K.1, ∀ y ∈ K.1, a * y * a⁻¹ = k * y * (k : H)⁻¹ := by
    intro a ha K
    have : Group.IsPerfect K.1 := K.2.1.1
    have : Group.IsSolvable (Outer (K.1 ⧸ center K.1)) := hout K.1 K.2
    have : Group.IsSolvable (Outer K.1) := solvable_of_centerQuotient K.1
    let act : A →* MulAut K.1 :=
      (normalizerConjHom K.1).comp (Subgroup.inclusion (hnorm K.1 K.2))
    obtain ⟨k, hk⟩ := perfect_action_inner act ⟨a, ha⟩
    refine ⟨k, fun y hy => ?_⟩
    have h1 := congrArg (fun σ : MulAut K.1 => ((σ ⟨y, hy⟩ : K.1) : H)) hk
    simpa [act, coe_normalizerConjHom_apply, MulAut.conj_apply] using h1
  have hAFs : ∀ a ∈ A, a ∈ centralizer (CFSG.fittingSubgroup H : Set H) := fun a ha =>
    (commutator_eq_bot_iff_le_centralizer.1 hAF) ha
  have hEF : CFSG.layer H ≤ centralizer (CFSG.fittingSubgroup H : Set H) := by
    have h := CFSG.LocalCores.fitting_layer_commute (G := H)
    rw [commutator_comm] at h
    exact commutator_eq_bot_iff_le_centralizer.1 h
  have hAFs' : A ≤ CFSG.generalizedFitting H := by
    intro a ha
    choose x hx using hinner a ha
    set e := CFSG.LocalCores.layerMul H x with he
    have heE : e ∈ CFSG.layer H := by
      rw [← CFSG.LocalCores.layerMul_range]
      exact ⟨x, rfl⟩
    have hcomp : ∀ K : CFSG.LocalCores.ComponentIndex H, ∀ y ∈ K.1,
        y * (e⁻¹ * a) = e⁻¹ * a * y := by
      intro K y hy
      have h1 := hx K y hy
      have h2 : Commute y (CFSG.LocalCores.layerMul H (Function.update x K 1)) :=
        CFSG.LocalCores.commute_layerMul_update x K hy
      have h3 : e * y * e⁻¹ = (x K : H) * y * (x K : H)⁻¹ := by
        rw [he, CFSG.LocalCores.layerMul_eq_mul_update x K]
        calc (x K : H) * CFSG.LocalCores.layerMul H (Function.update x K 1) * y *
              ((x K : H) * CFSG.LocalCores.layerMul H (Function.update x K 1))⁻¹
            = (x K : H) * (CFSG.LocalCores.layerMul H (Function.update x K 1) * y) *
                (CFSG.LocalCores.layerMul H (Function.update x K 1))⁻¹ * (x K : H)⁻¹ := by
              group
          _ = (x K : H) * (y * CFSG.LocalCores.layerMul H (Function.update x K 1)) *
                (CFSG.LocalCores.layerMul H (Function.update x K 1))⁻¹ * (x K : H)⁻¹ := by
              rw [h2.eq]
          _ = (x K : H) * y * (x K : H)⁻¹ := by group
      have h4 : a * y * a⁻¹ = e * y * e⁻¹ := by rw [h1, h3]
      calc y * (e⁻¹ * a) = e⁻¹ * (e * y * e⁻¹) * a := by group
        _ = e⁻¹ * (a * y * a⁻¹) * a := by rw [h4]
        _ = e⁻¹ * a * y := by group
    have hwE : CFSG.layer H ≤ centralizer ({e⁻¹ * a} : Set H) := by
      refine sSup_le fun K hK => fun y hy => ?_
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      exact (hcomp ⟨K, hK⟩ y hy).symm
    have hwF : CFSG.fittingSubgroup H ≤ centralizer ({e⁻¹ * a} : Set H) := by
      intro y hy
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff.1 hw]
      have h1 := mem_centralizer_iff.1 (hAFs a ha) y hy
      have h2 := mem_centralizer_iff.1 (hEF (inv_mem heE)) y hy
      calc e⁻¹ * a * y = e⁻¹ * (y * a) := by rw [mul_assoc, ← h1]
        _ = y * (e⁻¹ * a) := by rw [← mul_assoc, ← h2, mul_assoc]
    have hw : e⁻¹ * a ∈ CFSG.generalizedFitting H := by
      refine CFSG.centralizer_generalizedFitting_le H ?_
      rw [mem_centralizer_iff]
      intro y hy
      exact (mem_centralizer_iff.1 ((sup_le hwF hwE) hy) _ rfl).symm
    have heFs : e ∈ CFSG.generalizedFitting H := le_sup_right (a := CFSG.fittingSubgroup H) heE
    have := mul_mem heFs hw
    rwa [mul_inv_cancel_left] at this
  have : (CFSG.layer H).Characteristic := CFSG.LocalCores.layer_characteristic
  set π := QuotientGroup.mk' (CFSG.layer H) with hπ
  have hEπ : (CFSG.layer H).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  have hFsmap : (CFSG.generalizedFitting H).map π = (CFSG.fittingSubgroup H).map π := by
    rw [CFSG.generalizedFitting, Subgroup.map_sup, hEπ, sup_bot_eq]
  have hFsolv : Group.IsSolvable ((CFSG.fittingSubgroup H).map π) := by
    have : Group.IsNilpotent (CFSG.fittingSubgroup H) :=
      (CFSG.LocalCores.fitting_nilpotent (G := H)).1
    have hsurj : Function.Surjective ((π.comp (CFSG.fittingSubgroup H).subtype).rangeRestrict) :=
      MonoidHom.rangeRestrict_surjective _
    have h1 : Group.IsSolvable (π.comp (CFSG.fittingSubgroup H).subtype).range :=
      Group.isSolvable_of_surjective hsurj
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  have hAmap : A.map π ≤ (CFSG.fittingSubgroup H).map π := hFsmap ▸ map_mono hAFs'
  have hAsolv : Group.IsSolvable (A.map π) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAmap)
  have hAperf : Group.IsPerfect (A.map π) := Group.IsPerfect.map π
  have hAbot : A.map π = ⊥ := by
    by_contra hne
    have : Nontrivial (A.map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable (G := A.map π) hAsolv
  rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hAbot
  exact hAbot

end CFSG.LocalAnalysis.ComponentInitial
