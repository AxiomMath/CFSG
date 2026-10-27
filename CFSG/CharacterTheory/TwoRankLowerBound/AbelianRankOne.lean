module

public import CFSG.CharacterTheory.TwoRankLowerBound.RankOne

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem square_kernel_card_eq_two_of_unique_involution (G : Type*)
    [CommGroup G] [Finite G] [Nontrivial G] (htwogroup : IsPGroup 2 G)
    (hunique : ∀ left right : G, orderOf left = 2 → orderOf right = 2 → left = right) :
    Nat.card (powMonoidHom 2 : G →* G).ker = 2 := by
  obtain ⟨involution, horder, _⟩ := exists_central_involution_of_two_group G htwogroup
  let kernel := (powMonoidHom 2 : G →* G).ker
  have hmember : involution ∈ kernel := by
    change involution ^ 2 = 1
    exact (orderOf_eq_prime_iff.mp horder).1
  apply (Nat.card_eq_two_iff' (1 : kernel)).mpr
  refine ⟨⟨involution, hmember⟩, ?_, ?_⟩
  · intro hequal
    exact (orderOf_eq_prime_iff.mp horder).2 (congrArg Subtype.val hequal)
  · intro element hne
    apply Subtype.ext
    apply hunique element involution _ horder
    apply orderOf_eq_prime
    · exact element.property
    · intro hequal
      apply hne
      exact Subtype.ext hequal

theorem abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow
    (exponent : ℕ) (G : Type*) [CommGroup G] [Finite G]
    (htwogroup : IsPGroup 2 G) (hcard : Nat.card G = 2 ^ exponent)
    (hunique : ∀ left right : G, orderOf left = 2 → orderOf right = 2 → left = right) :
    IsCyclic G := by
  induction exponent generalizing G with
  | zero =>
    have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp (by simpa using hcard)).1
    infer_instance
  | succ exponent ih =>
    cases exponent with
    | zero =>
      exact isCyclic_of_prime_card (by simpa using hcard : Nat.card G = 2)
    | succ exponent =>
      have hnontrivial : Nontrivial G := by
        apply Finite.one_lt_card_iff_nontrivial.mp
        rw [hcard]
        exact Nat.one_lt_pow (by omega) (by omega)
      let square : G →* G := powMonoidHom 2
      have hkernel : Nat.card square.ker = 2 :=
        square_kernel_card_eq_two_of_unique_involution G htwogroup hunique
      have hrangecard : Nat.card square.range = 2 ^ (exponent + 1) := by
        have hproduct := square.ker.card_mul_index
        rw [Subgroup.index_ker, hkernel, hcard] at hproduct
        rw [pow_succ] at hproduct
        omega
      have hrangeunique : ∀ left right : square.range,
          orderOf left = 2 → orderOf right = 2 → left = right := by
        intro left right hleft hright
        apply Subtype.ext
        exact hunique left right
          ((Subgroup.orderOf_coe left).trans hleft)
          ((Subgroup.orderOf_coe right).trans hright)
      have hrangecyclic : IsCyclic square.range :=
        ih square.range (htwogroup.to_subgroup _) hrangecard hrangeunique
      obtain ⟨generator, hgenerator⟩ :=
        isCyclic_iff_exists_orderOf_eq_natCard.mp hrangecyclic
      obtain ⟨preimage, hpreimage⟩ := generator.property
      have hpreimageorder : orderOf (preimage ^ 2) = 2 ^ (exponent + 1) := by
        change preimage ^ 2 = (generator : G) at hpreimage
        rw [hpreimage, Subgroup.orderOf_coe generator, hgenerator, hrangecard]
      obtain ⟨power, hpower⟩ := htwogroup.exists_orderOf_eq_pow preimage
      have hpowerpositive : power ≠ 0 := by
        intro hzero
        have hone : preimage = 1 := orderOf_eq_one_iff.mp (by simpa [hzero] using hpower)
        rw [hone, one_pow, orderOf_one] at hpreimageorder
        have hgt : 1 < 2 ^ (exponent + 1) := Nat.one_lt_pow (by omega) (by omega)
        omega
      have hdouble : orderOf preimage = 2 * orderOf (preimage ^ 2) := by
        rw [orderOf_pow_of_dvd (by omega : 2 ≠ 0)]
        · exact (Nat.mul_div_cancel' (hpower ▸ dvd_pow_self 2 hpowerpositive)).symm
        · rw [hpower]
          exact dvd_pow_self 2 hpowerpositive
      apply isCyclic_iff_exists_orderOf_eq_natCard.mpr
      refine ⟨preimage, ?_⟩
      rw [hdouble, hpreimageorder, hcard, pow_succ]
      omega

theorem abelian_rank_one_two_group_isCyclic (G : Type*) [CommGroup G] [Finite G]
    (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1) : IsCyclic G := by
  obtain ⟨exponent, hcard⟩ := htwogroup.exists_card_eq
  apply abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow exponent G
    htwogroup hcard
  intro left right hleft hright
  exact commuting_involutions_eq_of_twoRank_le_one G hrank left right hleft hright
    (mul_comm left right)

theorem abelian_subgroup_of_rank_one_two_group_isCyclic (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (subgroup : Subgroup G) [IsMulCommutative subgroup] : IsCyclic subgroup := by
  let : CommGroup subgroup := Group.commGroupOfCenterEqTop Subgroup.center_eq_top
  exact abelian_rank_one_two_group_isCyclic subgroup (htwogroup.to_subgroup _)
    ((twoRank_subgroup_le subgroup).trans hrank)

theorem center_of_rank_one_two_group_isCyclic (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1) :
    IsCyclic (Subgroup.center G) := by
  exact abelian_subgroup_of_rank_one_two_group_isCyclic G htwogroup hrank _

theorem cyclic_elementary_two_subgroup_card_dvd_two (G : Type*) [Group G] [Finite G]
    (elementary : Subgroup G) (helementary : IsElemAbelian 2 elementary)
    (hcyclic : IsCyclic elementary) : Nat.card elementary ∣ 2 := by
  obtain ⟨generator, hgenerator⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyclic
  rw [← hgenerator]
  apply orderOf_dvd_of_pow_eq_one
  apply Subtype.ext
  exact helementary.2 generator generator.property

theorem twoRank_le_one_of_abelian_subgroups_cyclic (G : Type*) [Group G] [Finite G]
    (hcyclic : ∀ subgroup : Subgroup G, IsMulCommutative subgroup → IsCyclic subgroup) :
    twoRank G ≤ 1 := by
  apply csSup_le'
  rintro rank ⟨elementary, _, helementary, hcard⟩
  have hdivides := cyclic_elementary_two_subgroup_card_dvd_two G elementary helementary
    (hcyclic elementary helementary.1)
  rw [hcard] at hdivides
  have hle := Nat.le_of_dvd (by omega : 0 < 2) hdivides
  by_contra hnot
  have hlarge : 2 ^ 2 ≤ 2 ^ rank := pow_le_pow_right' (by omega) (by omega)
  norm_num at hlarge
  omega

theorem rank_one_two_group_iff_abelian_subgroups_cyclic (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) :
    twoRank G ≤ 1 ↔
      ∀ subgroup : Subgroup G, IsMulCommutative subgroup → IsCyclic subgroup := by
  constructor
  · intro hrank subgroup hab
    have := hab
    exact abelian_subgroup_of_rank_one_two_group_isCyclic G htwogroup hrank subgroup
  · exact twoRank_le_one_of_abelian_subgroups_cyclic G

end CFSG.TwoRankLowerBound.Helpers
