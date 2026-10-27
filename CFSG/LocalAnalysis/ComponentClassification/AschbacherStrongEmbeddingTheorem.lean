module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLocalStep
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalCriterionFromLeastFailure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCentralCase

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem normStatement_all
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity) (n : ℕ) : NormStatement n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hXn M x hx hM huniq h2 hhull hO
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hIH : NormStatement (Nat.card X - 1) := by
    intro Y _ _ hY
    exact ih (Nat.card X - 1) (by omega) Y hY
  by_cases hse : fusionStronglyEmbedded M
  · exact normSplit_of_stronglyEmbedded hx h2.1 hhull hO hse
  by_cases hcen : ∃ c ∈ Subgroup.center X, orderOf c = 2
  · obtain ⟨u, hu, hu2⟩ := hcen
    let Z : Subgroup X := Subgroup.zpowers u
    have : Z.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hu)
    let q := QuotientGroup.mk' Z
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
    have hZc : Z ≤ Subgroup.center X := Subgroup.zpowers_le.mpr hu
    have hZ2 : Nat.card Z = 2 := by rw [Nat.card_zpowers, hu2]
    have huM : u ∈ M := centralizer_le_of_unique huniq
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hu x).symm)
    have hker : q.ker ≤ M := by
      rw [QuotientGroup.ker_mk']
      exact Subgroup.zpowers_le.mpr huM
    have hcard : Nat.card (X ⧸ Z) ≤ Nat.card X - 1 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      rw [hZ2] at h
      omega
    have hN := hIH (X ⧸ Z) hcard (M.map q) (q x)
      (orderOf_central_quotient hx huniq hM hu hu2 Z rfl) (map_ne_top q hker hM)
      (unique_map q hq hker huniq) (centralProduct_central_quotient hx huniq hM h2 hu hu2 Z rfl)
      (hull_map_eq_top q hq hhull) (oddCore_central_quotient_eq_bot hO Z hZc hZ2)
    exact normSplit_of_central_involution hcov hx hM huniq h2 hhull hO hu hu2 Z rfl hN
  · exfalso
    have hnc : ∀ c ∈ Subgroup.center X, orderOf c ≠ 2 := fun c hc h => hcen ⟨c, hc, h⟩
    apply hse
    have hlocal : InvolutionPointLocalEmbedding M x :=
      ⟨hM, mem_of_unique huniq, hx, huniq, fun u hu hux hesc =>
        local_embedding_of_no_central_involution hx hM huniq h2 hhull hO hnc hIH hu hux hesc⟩
    have h := local_criterion_of_no_least_failure himp X M x hlocal h2.1
    rw [hhull] at h
    have hmap := h.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X)
    have himage : (M.subgroupOf (⊤ : Subgroup X)).map
        (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom = M := by
      change (M.subgroupOf (⊤ : Subgroup X)).map (⊤ : Subgroup X).subtype = M
      rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
    rwa [himage] at hmap

theorem theorem_3_3
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity)
    {G : Type} [Group G] [Finite G] (H : Subgroup G) (z : G) (hz : orderOf z = 2)
    (hH : H ≠ ⊤) (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) :
    (ProductUniqueContainment H z → CentralProductCentralizer H z) ∧
      (CentralProductCentralizer H z → PointHullStrongSplit H z) ∧
      (PointHullStrongSplit H z → ProductUniqueContainment H z) :=
  ⟨centralProductCentralizer_of_productUniqueContainment hz huniq hH,
    fun h2 => pointHullStrongSplit_of_normStatement hz hH huniq h2
      (normStatement_all himp hcov _),
    productUniqueContainment_of_pointHullStrongSplit hz huniq⟩

theorem theorem_3_3_tfae
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity)
    {G : Type} [Group G] [Finite G] (H : Subgroup G) (z : G) (hz : orderOf z = 2)
    (hH : H ≠ ⊤) (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) :
    [ProductUniqueContainment H z, CentralProductCentralizer H z,
      PointHullStrongSplit H z].TFAE := by
  obtain ⟨h12, h23, h31⟩ := theorem_3_3 himp hcov H z hz hH huniq
  tfae_have 1 → 2 := h12
  tfae_have 2 → 3 := h23
  tfae_have 3 → 1 := h31
  tfae_finish

end CFSG.ComponentClassification.AschbacherStrongEmbedding
