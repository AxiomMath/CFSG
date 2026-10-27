module

public import CFSG.CharacterTheory.TwoRankLowerBound.RankOneCenter

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem zpowers_normal_of_central_quotient_of_rank_one_two_group (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (element : G) (hnoncentral : element ∉ Subgroup.center G)
    (hquotient : (QuotientGroup.mk' (Subgroup.center G)) element ∈
      Subgroup.center (G ⧸ Subgroup.center G)) :
    (Subgroup.zpowers element).Normal := by
  have hcenterle := (center_lt_zpowers_of_rank_one_two_group G htwogroup hrank element
    hnoncentral).le
  have hconjugate : ∀ conjugator : G, conjugator * element * conjugator⁻¹ ∈
      Subgroup.zpowers element := by
    intro conjugator
    have hdifference : (conjugator * element * conjugator⁻¹) / element ∈
        Subgroup.center G := by
      apply QuotientGroup.eq_iff_div_mem.mp
      change (QuotientGroup.mk' (Subgroup.center G))
        (conjugator * element * conjugator⁻¹) =
        (QuotientGroup.mk' (Subgroup.center G)) element
      simp only [map_mul, map_inv]
      rw [Subgroup.mem_center_iff.mp hquotient]
      group
    have hmember := (Subgroup.zpowers element).mul_mem (hcenterle hdifference)
      (Subgroup.mem_zpowers element)
    simpa only [div_mul_cancel] using hmember
  constructor
  intro member hmember conjugator
  obtain ⟨power, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmember
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ (hconjugate conjugator) power

theorem exists_normal_cyclic_four_subgroup_of_rank_one_two_group (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (hnonabelian : ∃ left right : G, left * right ≠ right * left) :
    ∃ cyclic : Subgroup G, cyclic.Normal ∧ IsCyclic cyclic ∧ Nat.card cyclic = 4 ∧
      Subgroup.center G ≤ cyclic := by
  obtain ⟨element, hnoncentral, hsquare, hquotient⟩ :=
    exists_noncentral_with_central_quotient_involution G htwogroup hnonabelian
  have hcentersquare := zpowers_square_eq_center_of_rank_one_two_group G htwogroup hrank
    element hnoncentral hsquare
  have hne : element ≠ 1 := by
    intro hequal
    exact hnoncentral (hequal ▸ Subgroup.one_mem _)
  refine ⟨Subgroup.zpowers element,
    zpowers_normal_of_central_quotient_of_rank_one_two_group G htwogroup hrank element
      hnoncentral hquotient, inferInstance, ?_, ?_⟩
  · rw [Nat.card_zpowers, square_order_doubled_of_two_group G htwogroup element hne,
      ← Nat.card_zpowers (element ^ 2), hcentersquare,
      center_card_eq_two_of_nonabelian_rank_one_two_group G htwogroup hrank hnonabelian]
  · exact (center_lt_zpowers_of_rank_one_two_group G htwogroup hrank element hnoncentral).le

theorem conjugation_kernel_eq_centralizer (G : Type*) [Group G]
    (normal : Subgroup G) [normal.Normal] :
    (MulAut.conjNormal : G →* MulAut normal).ker = Subgroup.centralizer (normal : Set G) := by
  ext element
  constructor
  · intro hkernel
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have hconjugate := congrArg (fun automorphism : MulAut normal =>
      (automorphism (⟨member, hmember⟩ : normal) : G)) hkernel
    change element * member * element⁻¹ = member at hconjugate
    calc
      member * element = (element * member * element⁻¹) * element := by rw [hconjugate]
      _ = element * member := by group
  · intro hcentral
    change MulAut.conjNormal element = 1
    ext member
    change element * (member : G) * element⁻¹ = (member : G)
    rw [← Subgroup.mem_centralizer_iff.mp hcentral member member.property]
    group

theorem centralizer_index_two_of_normal_cyclic_four_subgroup (G : Type*)
    [Group G] [Finite G] (normal : Subgroup G) [normal.Normal] [IsCyclic normal]
    (hfour : Nat.card normal = 4) (hcentertwo : Nat.card (Subgroup.center G) = 2) :
    (Subgroup.centralizer (normal : Set G)).index = 2 := by
  let conjugation : G →* MulAut normal := MulAut.conjNormal
  have hautomorphisms : Nat.card (MulAut normal) = 2 := by
    rw [IsCyclic.card_mulAut, hfour]
    decide
  have hrangele : Nat.card conjugation.range ≤ 2 := by
    simpa [hautomorphisms] using conjugation.range.card_le_card_group
  have hrangene : Nat.card conjugation.range ≠ 1 := by
    intro hone
    have hrangebot := Subgroup.card_eq_one.mp hone
    have hcentral : normal ≤ Subgroup.center G := by
      intro member hmember
      apply Subgroup.mem_center_iff.mpr
      intro element
      have hconjugationone : conjugation element = 1 := by
        have hmember : conjugation element ∈ conjugation.range := ⟨element, rfl⟩
        rwa [hrangebot, Subgroup.mem_bot] at hmember
      have hkernel : element ∈ conjugation.ker := hconjugationone
      rw [conjugation_kernel_eq_centralizer] at hkernel
      exact (Subgroup.mem_centralizer_iff.mp hkernel member hmember).symm
    have hle := Subgroup.card_le_of_le hcentral
    rw [hfour, hcentertwo] at hle
    omega
  have hrangepos : 0 < Nat.card conjugation.range := Nat.card_pos
  have hrangetwo : Nat.card conjugation.range = 2 := by omega
  have hkerindex := Subgroup.index_ker conjugation
  rw [conjugation_kernel_eq_centralizer, hrangetwo] at hkerindex
  exact hkerindex

theorem centralizer_isCyclic_of_normal_cyclic_four_subgroup (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (normal : Subgroup G) [normal.Normal] [IsCyclic normal] (hfour : Nat.card normal = 4) :
    IsCyclic (Subgroup.centralizer (normal : Set G)) := by
  let centralizer := Subgroup.centralizer (normal : Set G)
  have hnormalle : normal ≤ centralizer := Subgroup.le_centralizer normal
  have hnormalcenter : normal.subgroupOf centralizer ≤ Subgroup.center centralizer := by
    intro member hmember
    apply Subgroup.mem_center_iff.mpr
    intro element
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp element.property member hmember).symm
  have habelian : IsMulCommutative centralizer := by
    by_contra hnot
    have hnotall := isMulCommutative_iff.not.mp hnot
    push Not at hnotall
    have hcentertwo := center_card_eq_two_of_nonabelian_rank_one_two_group centralizer
      (htwogroup.to_subgroup centralizer) ((twoRank_subgroup_le centralizer).trans hrank) hnotall
    have hle := Subgroup.card_le_of_le hnormalcenter
    have hnormalcard : Nat.card (normal.subgroupOf centralizer) = 4 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hnormalle).toEquiv).trans hfour
    rw [hnormalcard, hcentertwo] at hle
    omega
  have := habelian
  exact abelian_subgroup_of_rank_one_two_group_isCyclic G htwogroup hrank centralizer

theorem exists_cyclic_index_two_subgroup_of_nonabelian_rank_one_two_group (G : Type*)
    [Group G] [Finite G] (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1)
    (hnonabelian : ∃ left right : G, left * right ≠ right * left) :
    ∃ normal : Subgroup G, normal.Normal ∧ IsCyclic normal ∧ Nat.card normal = 4 ∧
      IsCyclic (Subgroup.centralizer (normal : Set G)) ∧
      (Subgroup.centralizer (normal : Set G)).index = 2 := by
  obtain ⟨normal, hnormal, hcyclic, hfour, _⟩ :=
    exists_normal_cyclic_four_subgroup_of_rank_one_two_group G htwogroup hrank hnonabelian
  have := hnormal
  have := hcyclic
  refine ⟨normal, hnormal, hcyclic, hfour,
    centralizer_isCyclic_of_normal_cyclic_four_subgroup G htwogroup hrank normal hfour, ?_⟩
  exact centralizer_index_two_of_normal_cyclic_four_subgroup G normal hfour
    (center_card_eq_two_of_nonabelian_rank_one_two_group G htwogroup hrank hnonabelian)

end CFSG.TwoRankLowerBound.Helpers
