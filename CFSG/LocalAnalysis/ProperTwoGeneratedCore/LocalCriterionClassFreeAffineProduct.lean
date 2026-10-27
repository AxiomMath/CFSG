module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineFrattini

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open scoped Pointwise
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem maximal_prime_pointwise_kernel_normalizer_set_product
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (W : Subgroup G)
    (hW : IsPGroup p W) (hthree : 3 ≤ Nat.card (pointFixedSet H W))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W) :
    (Subgroup.normalizer
      (pointwiseRightStabilizer H (pointFixedSet H W) : Set G) : Set G) =
      (pointwiseRightStabilizer H (pointFixedSet H W) : Set G) *
        (Subgroup.normalizer (W : Set G) : Set G) := by
  ext n
  constructor
  · intro hn
    obtain ⟨k, hk, y, hy, hprod⟩ :=
      (maximal_prime_pointwise_kernel_frattini H p hp W hW hthree hmax).2 n hn
    exact Set.mem_mul.mpr ⟨k, hk, y, hy, hprod⟩
  · rintro ⟨k, hk, y, hy, rfl⟩
    exact (Subgroup.normalizer
      (pointwiseRightStabilizer H (pointFixedSet H W) : Set G)).mul_mem
      (Subgroup.le_normalizer hk)
      (prime_normalizer_le_pointwise_kernel_normalizer H W hy)

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
