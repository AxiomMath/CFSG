module

public import CFSG.GroupTheory.InnerCentralizerProjection
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.GroupTheory

open Subgroup
open CFSG.ComponentClassification.AschbacherComponentInvolution
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem le_sup_centralizer_of_perfect_of_perfect_aut_inner {K C : Subgroup G}
    [Group.IsPerfect K] (hKC : K ≤ Subgroup.normalizer (C : Set G))
    (hOut : ∀ P : Subgroup (MulAut ↥C), Group.IsPerfect P →
      P ≤ (MulAut.conj : ↥C →* MulAut ↥C).range) :
    K ≤ C ⊔ Subgroup.centralizer (C : Set G) := by
  let action : K →* MulAut ↥C :=
    C.normalizerMonoidHom.comp (Subgroup.inclusion hKC)
  have haction : Group.IsPerfect action.range := Group.IsPerfect.range action
  have hrange : action.range ≤ (MulAut.conj : ↥C →* MulAut ↥C).range :=
    hOut action.range haction
  refine le_sup_centralizer_of_forall_mem_range_conj hKC ?_
  intro r hr
  exact hrange ⟨⟨r, hr⟩, rfl⟩

theorem exists_forall_conj_eq_of_mem_sup_centralizer {C : Subgroup G} {k : G}
    (hk : k ∈ C ⊔ Subgroup.centralizer (C : Set G)) :
    ∃ c ∈ C, ∀ m ∈ C, k * m * k⁻¹ = c * m * c⁻¹ := by
  obtain ⟨c, hc, z, hz, hcz⟩ := exists_mul_of_mem_sup_of_commute
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha) hk
  refine ⟨c, hc, fun m hm => ?_⟩
  have hzm : z * m * z⁻¹ = m := by
    rw [← Subgroup.mem_centralizer_iff.mp hz m hm]
    group
  calc
    k * m * k⁻¹ = c * (z * m * z⁻¹) * c⁻¹ := by rw [← hcz]; group
    _ = c * m * c⁻¹ := by rw [hzm]

theorem le_layer_of_perfect_of_centralizes_fitting_of_component_sup_centralizer (K : Subgroup G)
    [Finite G] [Group.IsPerfect K] (hKF : ⁅K, fittingSubgroup G⁆ = ⊥)
    (hcomp : ∀ C : Subgroup G, CFSG.IsComponent C →
      K ≤ C ⊔ Subgroup.centralizer (C : Set G)) :
    K ≤ layer G := by
  have hinner : ∀ (k : G) (_ : k ∈ K) (C : Subgroup G), Open.IsComponentOf C ⊤ →
      ∃ c ∈ C, ∀ m ∈ C, k * m * k⁻¹ = c * m * c⁻¹ := by
    intro k hk C hC
    exact exists_forall_conj_eq_of_mem_sup_centralizer (C := C) (k := k)
      (hcomp C ((CFSG.isComponent_iff_open C).mpr hC) hk)
  have hproduct : K ≤ ComponentClassification.Layer.subgroup G ⊔
      Subgroup.centralizer (ComponentClassification.Layer.subgroup G : Set G) := by
    intro k hk
    obtain ⟨e, he, haction⟩ :=
      ComponentClassification.ComponentInnerActions.exists_layer_implementer k
        (fun C hC => hinner k hk C hC)
    have hcentralizes : e⁻¹ * k ∈
        Subgroup.centralizer (ComponentClassification.Layer.subgroup G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have heq := congrArg (fun value : G => e⁻¹ * value * k) (haction m hm)
      calc
        m * (e⁻¹ * k) = e⁻¹ * (e * m * e⁻¹) * k := by group
        _ = e⁻¹ * (k * m * k⁻¹) * k := heq.symm
        _ = (e⁻¹ * k) * m := by group
    have hk_eq : e * (e⁻¹ * k) = k := by group
    rw [← hk_eq]
    exact Subgroup.mul_mem_sup he hcentralizes
  have hle := perfect_layer_centralizer_product_absorption K hproduct hKF
  simpa only [CFSG.layer_eq_componentClassification] using hle

end CFSG.GroupTheory
