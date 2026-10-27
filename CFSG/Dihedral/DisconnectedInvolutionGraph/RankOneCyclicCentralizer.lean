module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneCentralizerIndex

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_order_four_centralizer_cyclic
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (element : G) (horder : orderOf element = 4) :
    IsCyclic (Subgroup.centralizer {element}) := by
  classical
  let centralizer := Subgroup.centralizer {element}
  have hcommutative : ∀ first second : centralizer, first * second = second * first := by
    by_contra hmissing
    push Not at hmissing
    have hcenterCard := rank_one_two_nonabelian_center_card_two
      (hpgroup.to_subgroup centralizer)
      (subgroup_no_commuting_distinct_involutions centralizer hrank) hmissing
    let elementInside : centralizer := ⟨element,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have helementCentral : elementInside ∈ Subgroup.center centralizer := by
      apply Subgroup.mem_center_iff.mpr
      intro other
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp other.property
    have hinsideOrder : orderOf elementInside = 4 :=
      (Subgroup.orderOf_coe elementInside).symm.trans horder
    have hdiv := (Subgroup.center centralizer).orderOf_dvd_natCard helementCentral
    rw [hinsideOrder, hcenterCard] at hdiv
    norm_num at hdiv
  exact rank_one_two_abelian_subgroup_cyclic hpgroup hrank centralizer hcommutative

theorem rank_one_two_central_coset_order_four
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first)
    (element : G)
    (hcosetOrder : orderOf (QuotientGroup.mk' (Subgroup.center G) element) = 2) :
    orderOf element = 4 := by
  have hcenterGenerates := rank_one_two_central_coset_square_generates_center
    hpgroup hrank element hcosetOrder
  have hsquareOrder : orderOf (element ^ 2) = 2 := by
    rw [← Nat.card_zpowers, hcenterGenerates,
      rank_one_two_nonabelian_center_card_two hpgroup hrank hnonabelian]
  have hsquareNe : element ^ 2 ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at hsquareOrder
    omega
  have hfourth : element ^ 4 = 1 := by
    have hsquarePower := pow_orderOf_eq_one (element ^ 2)
    rw [hsquareOrder] at hsquarePower
    simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul] using hsquarePower
  simpa only [show (2 : ℕ) ^ 1 = 2 from rfl, show (2 : ℕ) ^ (1 + 1) = 4 from rfl] using
    (orderOf_eq_prime_pow (p := 2) (n := 1) hsquareNe hfourth)

theorem rank_one_two_exists_cyclic_index_two
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first) :
    ∃ normalSubgroup : Subgroup G,
      normalSubgroup.Normal ∧ IsCyclic normalSubgroup ∧ Nat.card normalSubgroup = 4 ∧
      (Subgroup.centralizer (normalSubgroup : Set G)).index = 2 ∧
      IsCyclic (Subgroup.centralizer (normalSubgroup : Set G)) := by
  obtain ⟨element, hcosetCentral, hcosetOrder, _⟩ :=
    rank_one_two_exists_central_order_two_coset hpgroup hrank hnonabelian
  let normalSubgroup := Subgroup.zpowers element
  have hnormal : normalSubgroup.Normal := by
    constructor
    intro other hother actor
    obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hother
    have hconjugate : actor * element ^ exponent * actor⁻¹ =
        (actor * element * actor⁻¹) ^ exponent := by
      exact map_zpow (MulAut.conj actor) element exponent
    rw [hconjugate]
    rcases rank_one_two_central_coset_conjugates hpgroup hrank hnonabelian element
      hcosetCentral hcosetOrder actor with hfixed | hinverse
    · rw [hfixed]
      exact normalSubgroup.zpow_mem (Subgroup.mem_zpowers element) exponent
    · rw [hinverse]
      exact normalSubgroup.zpow_mem
        (normalSubgroup.inv_mem (Subgroup.mem_zpowers element)) exponent
  have hcentralizers : Subgroup.centralizer (normalSubgroup : Set G) =
      Subgroup.centralizer {element} := by
    ext other
    constructor
    · intro hmem
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact (Subgroup.mem_centralizer_iff.mp hmem element (Subgroup.mem_zpowers element)).symm
    · intro hmem
      apply Subgroup.mem_centralizer_iff.mpr
      intro generator hgenerator
      obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgenerator
      have hcommute : Commute other element := Subgroup.mem_centralizer_singleton_iff.mp hmem
      exact (hcommute.zpow_right exponent).symm
  have horder := rank_one_two_central_coset_order_four hpgroup hrank hnonabelian
    element hcosetOrder
  refine ⟨normalSubgroup, hnormal, inferInstance, ?_, ?_, ?_⟩
  · exact (Nat.card_zpowers element).trans horder
  · rw [hcentralizers]
    exact rank_one_two_central_coset_centralizer_index hpgroup hrank hnonabelian
      element hcosetCentral hcosetOrder
  · rw [hcentralizers]
    exact rank_one_two_order_four_centralizer_cyclic hpgroup hrank element horder

end CFSG.DisconnectedInvolutionGraph.Helpers
