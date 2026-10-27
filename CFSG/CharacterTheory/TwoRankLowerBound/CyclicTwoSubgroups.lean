module

public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianRankOne

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

theorem center_singleton_closure_isMulCommutative (G : Type*) [Group G] (element : G) :
    IsMulCommutative (Subgroup.closure ({element} ∪ (Subgroup.center G : Set G))) := by
  apply CFSG.subgroup_isMulCommutative_closure
  intro left hleft right hright
  rcases hleft with hleft | hleft
  · have hleft : left = element := Set.mem_singleton_iff.mp hleft
    subst left
    rcases hright with hright | hright
    · have hright : right = element := Set.mem_singleton_iff.mp hright
      subst right
      rfl
    · exact Subgroup.mem_center_iff.mp hright element
  · exact (Subgroup.mem_center_iff.mp hleft right).symm

theorem subgroup_eq_power_kernel_of_cyclic (G : Type*) [CommGroup G] [Finite G]
    [IsCyclic G] (subgroup : Subgroup G) :
    subgroup = (powMonoidHom (Nat.card subgroup) : G →* G).ker := by
  have hle : subgroup ≤ (powMonoidHom (Nat.card subgroup) : G →* G).ker := by
    intro element hmember
    change element ^ Nat.card subgroup = 1
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨element, hmember⟩ : subgroup)))
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [IsCyclic.card_powMonoidHom_ker,
    Nat.gcd_eq_right subgroup.card_subgroup_dvd_card]

theorem subgroup_le_of_card_dvd_of_cyclic (G : Type*) [CommGroup G] [Finite G]
    [IsCyclic G] (left right : Subgroup G)
    (hdivides : Nat.card left ∣ Nat.card right) : left ≤ right := by
  rw [subgroup_eq_power_kernel_of_cyclic G left,
    subgroup_eq_power_kernel_of_cyclic G right]
  intro element hmember
  change element ^ Nat.card right = 1
  change element ^ Nat.card left = 1 at hmember
  obtain ⟨multiple, hmultiple⟩ := hdivides
  rw [hmultiple, pow_mul, hmember, one_pow]

theorem subgroups_comparable_of_cyclic_two_group (G : Type*) [Group G] [Finite G]
    [IsCyclic G] (htwogroup : IsPGroup 2 G) (left right : Subgroup G) :
    left ≤ right ∨ right ≤ left := by
  let : CommGroup G := IsCyclic.commGroup
  obtain ⟨leftExponent, hleft⟩ := (htwogroup.to_subgroup left).exists_card_eq
  obtain ⟨rightExponent, hright⟩ := (htwogroup.to_subgroup right).exists_card_eq
  obtain hle | hle := le_total leftExponent rightExponent
  · left
    apply subgroup_le_of_card_dvd_of_cyclic G left right
    rw [hleft, hright]
    exact Nat.pow_dvd_pow 2 hle
  · right
    apply subgroup_le_of_card_dvd_of_cyclic G right left
    rw [hleft, hright]
    exact Nat.pow_dvd_pow 2 hle

theorem center_lt_zpowers_of_rank_one_two_group (G : Type*) [Group G] [Finite G]
    (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1) (element : G)
    (hnoncentral : element ∉ Subgroup.center G) :
    Subgroup.center G < Subgroup.zpowers element := by
  let generated := Subgroup.closure ({element} ∪ (Subgroup.center G : Set G))
  have hgeneratedabelian : IsMulCommutative generated :=
    center_singleton_closure_isMulCommutative G element
  have hgeneratedcyclic : IsCyclic generated := by
    have := hgeneratedabelian
    exact abelian_subgroup_of_rank_one_two_group_isCyclic G htwogroup hrank generated
  have hcenterle : Subgroup.center G ≤ generated := by
    intro central hcentral
    exact Subgroup.subset_closure (Or.inr hcentral)
  have helementmem : element ∈ generated := Subgroup.subset_closure (Or.inl (by simp))
  have hpowersle : Subgroup.zpowers element ≤ generated :=
    Subgroup.zpowers_le_of_mem helementmem
  have hcomparable := subgroups_comparable_of_cyclic_two_group generated
    (htwogroup.to_subgroup generated)
    ((Subgroup.center G).subgroupOf generated)
    ((Subgroup.zpowers element).subgroupOf generated)
  have hcenterpowers : Subgroup.center G ≤ Subgroup.zpowers element := by
    rcases hcomparable with hle | hle
    · intro central hcentral
      exact hle (show (⟨central, hcenterle hcentral⟩ : generated) ∈
        (Subgroup.center G).subgroupOf generated from hcentral)
    · exact False.elim (hnoncentral (hle
        (show (⟨element, helementmem⟩ : generated) ∈
          (Subgroup.zpowers element).subgroupOf generated from Subgroup.mem_zpowers element)))
  apply lt_of_le_of_ne hcenterpowers
  intro hequal
  exact hnoncentral (hequal ▸ Subgroup.mem_zpowers element)

theorem center_card_lt_orderOf_of_rank_one_two_group (G : Type*) [Group G] [Finite G]
    (htwogroup : IsPGroup 2 G) (hrank : twoRank G ≤ 1) (element : G)
    (hnoncentral : element ∉ Subgroup.center G) :
    Nat.card (Subgroup.center G) < orderOf element := by
  have hlt := center_lt_zpowers_of_rank_one_two_group G htwogroup hrank element hnoncentral
  have hle := Subgroup.card_le_of_le hlt.le
  rw [Nat.card_zpowers] at hle
  apply lt_of_le_of_ne hle
  intro hequal
  exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le
    (by simpa [Nat.card_zpowers] using hequal.symm.le))

theorem square_order_doubled_of_two_group (G : Type*) [Group G]
    (htwogroup : IsPGroup 2 G) (element : G) (hne : element ≠ 1) :
    orderOf element = 2 * orderOf (element ^ 2) := by
  rw [orderOf_pow_of_dvd (by omega : 2 ≠ 0) (htwogroup.dvd_orderOf hne)]
  exact (Nat.mul_div_cancel' (htwogroup.dvd_orderOf hne)).symm

theorem proper_subgroup_le_squares_of_cyclic_two_group (G : Type*) [CommGroup G]
    [Finite G] [IsCyclic G] (htwogroup : IsPGroup 2 G) (subgroup : Subgroup G)
    (hproper : subgroup ≠ ⊤) : subgroup ≤ (powMonoidHom 2 : G →* G).range := by
  have hnontrivial : Nontrivial G := by
    by_contra hnot
    have : Subsingleton G := not_nontrivial_iff_subsingleton.mp hnot
    exact hproper (Subsingleton.elim _ _)
  obtain ⟨totalExponent, htotal⟩ := htwogroup.exists_card_eq
  obtain ⟨subExponent, hsub⟩ := (htwogroup.to_subgroup subgroup).exists_card_eq
  have htotalpositive : totalExponent ≠ 0 := by
    have hcardgt : 1 < Nat.card G := Finite.one_lt_card_iff_nontrivial.mpr hnontrivial
    intro hzero
    simp [htotal, hzero] at hcardgt
  have hsuble : subExponent < totalExponent := by
    have hle := subgroup.card_le_card_group
    rw [htotal, hsub] at hle
    have hexponents : subExponent ≤ totalExponent :=
      (pow_le_pow_iff_right₀ (by omega : 1 < (2 : ℕ))).mp hle
    apply lt_of_le_of_ne hexponents
    intro hequal
    exact hproper (subgroup.eq_top_of_card_eq (by rw [htotal, hsub, hequal]))
  apply subgroup_le_of_card_dvd_of_cyclic G subgroup (powMonoidHom 2 : G →* G).range
  rw [IsCyclic.card_powMonoidHom_range, htotal, hsub,
    Nat.gcd_eq_right (dvd_pow_self 2 htotalpositive)]
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htotalpositive
  rw [pow_succ, Nat.mul_div_cancel _ (by omega : 0 < 2)]
  exact Nat.pow_dvd_pow 2 (by omega)

end CFSG.TwoRankLowerBound.Helpers
