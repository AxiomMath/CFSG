module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineKernel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem ambient_sylow_frattini_factorization
    (p : ℕ) (hp : p.Prime) (K W : Subgroup G) (hWK : W ≤ K)
    (hYN : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (K : Set G))
    (P : Sylow p K) (hP : (P : Subgroup K).map K.subtype = W) :
    Subgroup.normalizer (K : Set G) = K ⊔ Subgroup.normalizer (W : Set G) ∧
      ∀ n ∈ Subgroup.normalizer (K : Set G),
        ∃ k ∈ K, ∃ y ∈ Subgroup.normalizer (W : Set G), k * y = n := by
  let : Fact p.Prime := ⟨hp⟩
  let N := Subgroup.normalizer (K : Set G)
  let KN := K.subgroupOf N
  have hKN : K ≤ N := K.le_normalizer
  let : KN.Normal := inferInstance
  let e := (Subgroup.subgroupOfEquivOfLe hKN).symm
  let Pn : Sylow p KN := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPn : (Pn : Subgroup KN).map KN.subtype = W.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (hWK.trans hKN)]
    change ((P : Subgroup K).map e.toMonoidHom).map (N.subtype.comp KN.subtype) = W
    rw [Subgroup.map_map]
    have hcomp : (N.subtype.comp KN.subtype).comp e.toMonoidHom = K.subtype := by
      ext k
      rfl
    rw [hcomp]
    exact hP
  have hfrattini := Pn.normalizer_sup_eq_top
  rw [hPn, ← Subgroup.subgroupOf_normalizer_eq (hWK.trans hKN)] at hfrattini
  have hfactor : K ⊔ Subgroup.normalizer (W : Set G) = N := by
    have hm := congrArg (Subgroup.map N.subtype) hfrattini
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYN,
      Subgroup.map_subgroupOf_eq_of_le hKN, Subgroup.map_top, N.range_subtype,
      sup_comm] at hm
    exact hm
  have hproducts : ∀ n ∈ N,
      ∃ k ∈ K, ∃ y ∈ Subgroup.normalizer (W : Set G), k * y = n := by
    intro n hn
    have hnN : (⟨n, hn⟩ : N) ∈
        KN ⊔ (Subgroup.normalizer (W : Set G)).subgroupOf N := by
      rw [sup_comm, hfrattini]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, y, hy, hky⟩ := Subgroup.mem_sup_of_normal_left.mp hnN
    exact ⟨k, hk, y, hy, congrArg Subtype.val hky⟩
  exact ⟨hfactor.symm, hproducts⟩

theorem maximal_prime_pointwise_kernel_frattini
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) :
    let K := pointwiseRightStabilizer H (pointFixedSet H W)
    Subgroup.normalizer (K : Set G) = K ⊔ Subgroup.normalizer (W : Set G) ∧
      ∀ n ∈ Subgroup.normalizer (K : Set G),
        ∃ k ∈ K, ∃ y ∈ Subgroup.normalizer (W : Set G), k * y = n := by
  obtain ⟨P, hP⟩ := globally_maximal_prime_is_sylow_pointwise_kernel H p W hW hthree hmax
  exact ambient_sylow_frattini_factorization p hp _ W
    (subgroup_le_pointwiseRightStabilizer_fixed_set H W)
    (prime_normalizer_le_pointwise_kernel_normalizer H W) P hP

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
