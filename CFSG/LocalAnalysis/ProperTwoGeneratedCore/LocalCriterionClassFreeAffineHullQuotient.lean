module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G T A : Type*} [Group G] [Group T] [Group A]

theorem image_isSolvable_of_kernel_le (chi : G →* A) (rho : G →* T)
    [Group.IsSolvable chi.range] (hker : chi.ker ≤ rho.ker) :
    Group.IsSolvable rho.range := by
  let e := QuotientGroup.quotientKerEquivRange chi
  let : Group.IsSolvable (G ⧸ chi.ker) :=
    Group.isSolvable_of_isSolvable_injective e.injective
  have hk : chi.ker ≤ rho.rangeRestrict.ker := by
    intro g hg
    exact Subtype.ext (hker hg)
  exact Group.isSolvable_of_surjective
    (QuotientGroup.lift_surjective_of_surjective chi.ker
      rho.rangeRestrict rho.rangeRestrict_surjective hk)

variable [Finite G]

theorem normal_subgroup_centralizer_representation_ranges_eq
    (K : Subgroup G) [K.Normal]
    (hno : ∀ V : Subgroup K, CFSG.Open.IsElemAbelian 2 V → Nat.card V ≠ 4)
    (u : K) (hu : orderOf u = 2) (rho : G →* T) (hker : K ≤ rho.ker) :
    (rho.comp (Subgroup.centralizer ({(u : G)} : Set G)).subtype).range =
      rho.range := by
  ext f
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e, rfl⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨k, hk, e, he, hprod⟩ :=
      normal_subgroup_involution_centralizer_factorization K hno u hu n
    refine ⟨⟨e, he⟩, ?_⟩
    change rho e = rho n
    rw [hprod, map_mul, MonoidHom.mem_ker.mp (hker hk), one_mul]

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
