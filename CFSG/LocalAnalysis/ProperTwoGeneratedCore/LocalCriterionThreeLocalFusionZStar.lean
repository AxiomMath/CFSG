module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusionPartition
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion

open CFSG.ShultStronglyClosedTI CFSG.Open
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe v

variable {G : Type v} [Group G]

theorem isolated_of_centralizer_sylow_singleton [Finite G]
    {u : G} (hu : orderOf u = 2)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hsingleton : involutionPointClass u ∩
      (centralizerSylowImage u T : Set G) = {u}) :
    ∀ g : G, Commute (g⁻¹ * u * g) u → g⁻¹ * u * g = u := by
  intro g hcomm
  let C := Subgroup.centralizer ({u} : Set G)
  let w : C := ⟨g⁻¹ * u * g, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  have hw : orderOf w = 2 :=
    (Subgroup.orderOf_coe w).symm.trans
      (order_two_of_mem_pointClass hu (show rightConjugateElem u g ∈
        involutionPointClass u from ⟨g, rfl⟩))
  obtain ⟨c, hc⟩ := involution_conjugate_into_sylow T hw
  have hconjT : rightConjugateElem (rightConjugateElem u g) (c : G) ∈
      centralizerSylowImage u T :=
    Subgroup.mem_map_of_mem C.subtype hc
  have hconjclass : rightConjugateElem (rightConjugateElem u g) (c : G) ∈
      involutionPointClass u :=
    pointClass_right_conjugate_mem (show rightConjugateElem u g ∈
      involutionPointClass u from ⟨g, rfl⟩) (c : G)
  have hintersection : rightConjugateElem (rightConjugateElem u g) (c : G) ∈
      involutionPointClass u ∩ (centralizerSylowImage u T : Set G) :=
    ⟨hconjclass, hconjT⟩
  rw [hsingleton] at hintersection
  have heq : rightConjugateElem (rightConjugateElem u g) (c : G) = u :=
    Set.mem_singleton_iff.mp hintersection
  have hcu : (c : G) * u = u * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.property
  have huconj : (c : G)⁻¹ * u * (c : G) = u := by
    rw [mul_assoc, ← hcu, inv_mul_cancel_left]
  apply (MulAut.conj (c : G)⁻¹).injective
  simpa only [MulAut.conj_apply, inv_inv, rightConjugateElem] using
    heq.trans huconj.symm

theorem ThreeLocalOrbitData.isolated_central_sylow_of_not_fused [Finite G]
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z)
    (hnotfused : u * z ∉ involutionPointClass u) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = centralizerSylowImage u T ∧
      ∃ huS : u ∈ (S : Subgroup G),
        (⟨u, huS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) ∧
        (∀ g : G, Commute (g⁻¹ * u * g) u → g⁻¹ * u * g = u) := by
  obtain ⟨S, hS⟩ := h.ambient_sylow_of_not_fused hnotfused
  have huS : u ∈ (S : Subgroup G) :=
    hS.symm ▸ involution_mem_centralizerSylowImage h.involution_order T
  refine ⟨S, hS, huS, ?_,
    isolated_of_centralizer_sylow_singleton h.involution_order T
      (h.class_intersection_singleton_of_not_fused hnotfused)⟩
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact (involution_centralizes_centralizerSylowImage u T (x : G)
    (hS ▸ x.property)).symm

theorem full_oddCore_eq_bot_of_simple_involution [IsSimpleGroup G]
    {u : G} (hu : orderOf u = 2) : oddCore G = ⊥ :=
  CFSG.ComponentClassification.Helpers.oddCore_eq_bot_of_involution G u hu

theorem not_isolated_involution_of_nonabelian_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {u : G} (hu : orderOf u = 2) :
    ¬ (∀ g : G, Commute (g⁻¹ * u * g) u → g⁻¹ * u * g = u) := by
  intro hisolated
  obtain ⟨_, hfactor⟩ := native_zStar_of_isolated_involution hu hisolated
  have hcore := full_oddCore_eq_bot_of_simple_involution hu
  have hCtop : Subgroup.centralizer ({u} : Set G) = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨c, hc, x, hx, hcx⟩ := hfactor g
    rw [hcore] at hx
    rw [Subgroup.mem_bot.mp hx, mul_one] at hcx
    rw [hcx]
    exact hc
  exact (CFSG.ComponentClassification.Helpers.centralizer_ne_top_of_involution
    G hnonab u hu) hCtop

theorem ThreeLocalOrbitData.product_fused [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {u z : G} {T : Sylow 2 (Subgroup.centralizer ({u} : Set G))}
    {U : Subgroup G} (h : ThreeLocalOrbitData u T U z) :
    u * z ∈ involutionPointClass u := by
  by_contra hnotfused
  obtain ⟨_, _, _, _, hisolated⟩ := h.isolated_central_sylow_of_not_fused hnotfused
  exact not_isolated_involution_of_nonabelian_simple hnonab h.involution_order hisolated

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreeLocalFusion
