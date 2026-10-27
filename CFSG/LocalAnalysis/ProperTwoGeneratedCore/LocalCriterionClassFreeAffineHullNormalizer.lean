module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G T : Type*} [Group G] [Finite G] [Group T]

theorem normalizer_involution_centralizer_factorization
    (K : Subgroup G)
    (hno : ∀ V : Subgroup K, CFSG.Open.IsElemAbelian 2 V → Nat.card V ≠ 4)
    (u : G) (huK : u ∈ K) (hu : orderOf u = 2)
    (n : G) (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, ∃ e ∈ Subgroup.normalizer (K : Set G) ⊓
      Subgroup.centralizer ({u} : Set G), n = k * e := by
  have hvK : n * u * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn u).mp huK
  have hv : orderOf (⟨n * u * n⁻¹, hvK⟩ : K) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans (((MulAut.conj n).orderOf_eq u).trans hu)
  obtain ⟨k, hk⟩ := involutions_conjugate_of_no_four_group hno
    (⟨n * u * n⁻¹, hvK⟩ : K) ⟨u, huK⟩ hv ((Subgroup.orderOf_coe _).symm.trans hu)
  have heN : (k : G)⁻¹ * n ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem
      ((Subgroup.normalizer (K : Set G)).inv_mem (Subgroup.le_normalizer k.property)) hn
  have heC : (k : G)⁻¹ * n ∈ Subgroup.centralizer ({u} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hconj : (k : G)⁻¹ * (n * u * n⁻¹) * k = u := congrArg Subtype.val hk
    have heq : ((k : G)⁻¹ * n) * u * ((k : G)⁻¹ * n)⁻¹ = u := by
      convert hconj using 1
      group
    exact mul_inv_eq_iff_eq_mul.mp heq
  exact ⟨k, k.property, (k : G)⁻¹ * n, ⟨heN, heC⟩, by group⟩

theorem normalizer_sup_involution_centralizer_eq
    (K : Subgroup G)
    (hno : ∀ V : Subgroup K, CFSG.Open.IsElemAbelian 2 V → Nat.card V ≠ 4)
    (u : G) (huK : u ∈ K) (hu : orderOf u = 2) :
    K ⊔ (Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) =
      Subgroup.normalizer (K : Set G) := by
  apply le_antisymm (sup_le Subgroup.le_normalizer inf_le_left)
  intro n hn
  obtain ⟨k, hk, e, he, rfl⟩ :=
    normalizer_involution_centralizer_factorization K hno u huK hu n hn
  exact Subgroup.mul_mem_sup hk he

theorem normalizer_centralizer_representation_ranges_eq
    (K : Subgroup G)
    (hno : ∀ V : Subgroup K, CFSG.Open.IsElemAbelian 2 V → Nat.card V ≠ 4)
    (u : G) (huK : u ∈ K) (hu : orderOf u = 2)
    (rho : Subgroup.normalizer (K : Set G) →* T)
    (hker : K.subgroupOf (Subgroup.normalizer (K : Set G)) ≤ rho.ker) :
    (rho.comp (Subgroup.inclusion
      (show Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.normalizer (K : Set G) from inf_le_left))).range = rho.range := by
  let N := Subgroup.normalizer (K : Set G)
  let E := N ⊓ Subgroup.centralizer ({u} : Set G)
  ext f
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨⟨e, e.property.1⟩, rfl⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨k, hk, e, he, hprod⟩ :=
      normalizer_involution_centralizer_factorization K hno u huK hu n n.property
    let kN : N := ⟨k, Subgroup.le_normalizer hk⟩
    let eN : N := ⟨e, he.1⟩
    have hnprod : n = kN * eN := Subtype.ext hprod
    have hkrep : rho kN = 1 := MonoidHom.mem_ker.mp (hker hk)
    refine ⟨⟨e, he⟩, ?_⟩
    change rho eN = rho n
    rw [hnprod, map_mul, hkrep, one_mul]

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
