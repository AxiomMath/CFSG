module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryPlanes
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylowContainment
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CentralizerPlaneGeneration

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem rank_three_planes_inf_ne_bot {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor first second : Subgroup G)
    (hcomm : IsMulCommutative actor) (hcard : Nat.card actor = prime ^ 3)
    (hfirstLe : first ≤ actor) (hsecondLe : second ≤ actor)
    (hfirstCard : Nat.card first = prime ^ 2) (hsecondCard : Nat.card second = prime ^ 2) :
    first ⊓ second ≠ ⊥ := by
  intro hbot
  have hdisjoint : Disjoint first second := disjoint_iff.mpr hbot
  have hcommute : ∀ left ∈ first, ∀ right ∈ second, Commute left right := by
    intro left hleft right hright
    exact congrArg (fun value : actor => (value : G))
      (isMulCommutative_iff.mp hcomm ⟨left, hfirstLe hleft⟩ ⟨right, hsecondLe hright⟩)
  have hjoinCard := card_join_of_commuting_disjoint first second hcommute hdisjoint
  have hbounded := Subgroup.card_le_of_le (sup_le hfirstLe hsecondLe)
  rw [hjoinCard, hfirstCard, hsecondCard, hcard] at hbounded
  have hpositive : 0 < prime ^ 3 := Nat.pow_pos hprime.pos
  have hproduct : prime ^ 2 * prime ^ 2 = prime ^ 3 * prime := by ring
  rw [hproduct] at hbounded
  nlinarith [hprime.two_le]

theorem normalized_solvable_pair_common_fixed_growth
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor first second lower : Subgroup G)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3)
    (hfirstSolvable : Group.IsSolvable first) (hsecondSolvable : Group.IsSolvable second)
    (hfirstComplement : ¬prime ∣ Nat.card first) (hsecondComplement : ¬prime ∣ Nat.card second)
    (hfirstNormalized : actor ≤ Subgroup.normalizer (first : Set G))
    (hsecondNormalized : actor ≤ Subgroup.normalizer (second : Set G))
    (hfirstNotLe : ¬first ≤ lower) (hsecondNotLe : ¬second ≤ lower) :
    ∃ member ∈ actor, member ≠ 1 ∧
      ¬first ⊓ Subgroup.centralizer ({member} : Set G) ≤ lower ∧
      ¬second ⊓ Subgroup.centralizer ({member} : Set G) ≤ lower := by
  obtain ⟨firstPlane, hfirstPlaneLe, hfirstPlaneCard, hfirstFixed⟩ :=
    exists_plane_fixed_not_le_of_rank_three_actor prime hprime actor first lower hcomm hpower
      hcard hfirstSolvable hfirstComplement hfirstNormalized hfirstNotLe
  obtain ⟨secondPlane, hsecondPlaneLe, hsecondPlaneCard, hsecondFixed⟩ :=
    exists_plane_fixed_not_le_of_rank_three_actor prime hprime actor second lower hcomm hpower
      hcard hsecondSolvable hsecondComplement hsecondNormalized hsecondNotLe
  have hinfNe := rank_three_planes_inf_ne_bot prime hprime actor firstPlane secondPlane hcomm hcard
    hfirstPlaneLe hsecondPlaneLe hfirstPlaneCard hsecondPlaneCard
  obtain ⟨member, hmemberNe⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinfNe
  refine ⟨member, hfirstPlaneLe member.property.1, fun heq => hmemberNe (Subtype.ext heq), ?_, ?_⟩
  · intro hle
    apply hfirstFixed
    exact (inf_le_inf le_rfl
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr member.property.1))).trans hle
  · intro hle
    apply hsecondFixed
    exact (inf_le_inf le_rfl
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr member.property.2))).trans hle

theorem prime_subgroup_internal_normalizer_not_le
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup lower : Subgroup G)
    (hpgroup : IsPGroup prime subgroup) (hstrict : lower < subgroup) :
    ¬subgroup ⊓ Subgroup.normalizer (lower : Set G) ≤ lower := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Group.IsNilpotent subgroup := hpgroup.isNilpotent
  intro hnormalizerLe
  have hinternalEq : Subgroup.normalizer (lower.subgroupOf subgroup : Set subgroup) =
      lower.subgroupOf subgroup := by
    rw [← Subgroup.subgroupOf_normalizer_eq hstrict.le]
    apply le_antisymm
    · intro member hmember
      exact hnormalizerLe ⟨member.property, hmember⟩
    · intro member hmember
      exact Subgroup.le_normalizer hmember
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := subgroup)))
      (lower.subgroupOf subgroup) hinternalEq
  apply hstrict.not_ge
  intro element helement
  have hmem : (⟨element, helement⟩ : subgroup) ∈ lower.subgroupOf subgroup := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hmem

theorem pairwise_normalizer_fixed_growth {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroupPrime : ℕ) (hsubgroupPrime : subgroupPrime.Prime)
    (actor first second : Subgroup G)
    (hcomm : IsMulCommutative actor) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3)
    (hfirstPGroup : IsPGroup subgroupPrime first) (hsecondPGroup : IsPGroup subgroupPrime second)
    (hfirstComplement : ¬prime ∣ Nat.card first) (hsecondComplement : ¬prime ∣ Nat.card second)
    (hfirstNormalized : actor ≤ Subgroup.normalizer (first : Set G))
    (hsecondNormalized : actor ≤ Subgroup.normalizer (second : Set G))
    (hfirstStrict : first ⊓ second < first) (hsecondStrict : first ⊓ second < second) :
    ∃ member ∈ actor, member ≠ 1 ∧
      ¬(first ⊓ Subgroup.normalizer (first ⊓ second : Set G)) ⊓
        Subgroup.centralizer ({member} : Set G) ≤ first ⊓ second ∧
      ¬(second ⊓ Subgroup.normalizer (first ⊓ second : Set G)) ⊓
        Subgroup.centralizer ({member} : Set G) ≤ first ⊓ second := by
  have : Fact subgroupPrime.Prime := ⟨hsubgroupPrime⟩
  have : Group.IsNilpotent first := hfirstPGroup.isNilpotent
  have : Group.IsNilpotent second := hsecondPGroup.isNilpotent
  let firstNormalizer := first ⊓ Subgroup.normalizer (first ⊓ second : Set G)
  let secondNormalizer := second ⊓ Subgroup.normalizer (first ⊓ second : Set G)
  have hfirstSolvable : Group.IsSolvable firstNormalizer :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hsecondSolvable : Group.IsSolvable secondNormalizer :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hlowerNormalized : actor ≤ Subgroup.normalizer (first ⊓ second : Set G) :=
    normalizes_inf_of_normalizes_both actor first second hfirstNormalized hsecondNormalized
  have hnormalizerNormalized : actor ≤
      Subgroup.normalizer (Subgroup.normalizer (first ⊓ second : Set G) : Set G) :=
    hlowerNormalized.trans (normalizer_normalizes_normalizer (first ⊓ second))
  exact normalized_solvable_pair_common_fixed_growth prime hprime actor firstNormalizer secondNormalizer
    (first ⊓ second) hcomm hpower hcard hfirstSolvable hsecondSolvable
    (fun hdiv => hfirstComplement (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left)))
    (fun hdiv => hsecondComplement (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left)))
    (normalizes_inf_of_normalizes_both actor first _ hfirstNormalized hnormalizerNormalized)
    (normalizes_inf_of_normalizes_both actor second _ hsecondNormalized hnormalizerNormalized)
    (prime_subgroup_internal_normalizer_not_le subgroupPrime hsubgroupPrime first _ hfirstPGroup hfirstStrict)
    (prime_subgroup_internal_normalizer_not_le subgroupPrime hsubgroupPrime second _ hsecondPGroup hsecondStrict)

end CFSG.RankThreeEvenClassification.Helpers
