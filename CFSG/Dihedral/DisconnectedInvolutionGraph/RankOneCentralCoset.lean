module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneCenterComparison

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_central_coset_square_generates_center
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (element : G) (horder : orderOf (QuotientGroup.mk' (Subgroup.center G) element) = 2) :
    Subgroup.zpowers (element ^ 2) = Subgroup.center G := by
  let cyclic := Subgroup.zpowers element
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnoncentral : element ∉ Subgroup.center G := by
    intro hcentral
    have hquotientOne := (QuotientGroup.eq_one_iff element).mpr hcentral
    change QuotientGroup.mk' (Subgroup.center G) element = 1 at hquotientOne
    rw [hquotientOne, orderOf_one] at horder
    omega
  have hcenterLe : Subgroup.center G ≤ cyclic :=
    (rank_one_two_center_lt_zpowers hpgroup hrank element hnoncentral).le
  let centerWithin := (Subgroup.center G).subgroupOf cyclic
  let restricted := (QuotientGroup.mk' (Subgroup.center G)).comp cyclic.subtype
  have hker : restricted.ker = centerWithin := by
    ext other
    change QuotientGroup.mk' (Subgroup.center G) other.val = 1 ↔ other.val ∈ Subgroup.center G
    exact QuotientGroup.eq_one_iff other.val
  have hsquareCentral : element ^ 2 ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff (element ^ 2)).mp
    change QuotientGroup.mk' (Subgroup.center G) (element ^ 2) = 1
    rw [map_pow]
    simpa only [horder] using pow_orderOf_eq_one (QuotientGroup.mk' (Subgroup.center G) element)
  have hpowerLe : Subgroup.zpowers (element ^ 2) ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr hsquareCentral
  have hrangeEq : restricted.range =
      Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center G) element) := by
    ext quotient
    constructor
    · rintro ⟨other, rfl⟩
      obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp other.property
      apply Subgroup.mem_zpowers_iff.mpr
      refine ⟨exponent, ?_⟩
      change (QuotientGroup.mk' (Subgroup.center G) element) ^ exponent =
        QuotientGroup.mk' (Subgroup.center G) other.val
      rw [← map_zpow, hexponent]
    · intro hmem
      obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine ⟨⟨element ^ exponent, (Subgroup.zpowers element).zpow_mem
        (Subgroup.mem_zpowers element) exponent⟩, ?_⟩
      change QuotientGroup.mk' (Subgroup.center G) (element ^ exponent) = quotient
      rw [map_zpow, hexponent]
  have hindex : centerWithin.index = 2 := by
    rw [← hker, Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange restricted).toEquiv,
      hrangeEq, Nat.card_zpowers, horder]
  have hcenterCard : Nat.card centerWithin = Nat.card (Subgroup.center G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcenterLe).toEquiv
  have hproduct : 2 * Nat.card (Subgroup.center G) = orderOf element := by
    have hproduct := centerWithin.index_mul_card
    rwa [hindex, hcenterCard, Nat.card_zpowers] at hproduct
  have hdiv : 2 ∣ orderOf element := ⟨Nat.card (Subgroup.center G), hproduct.symm⟩
  have hpowerCard : Nat.card (Subgroup.zpowers (element ^ 2)) = Nat.card (Subgroup.center G) := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by decide : 2 ≠ 0) hdiv, ← hproduct,
      Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  exact Subgroup.eq_of_le_of_card_ge hpowerLe hpowerCard.ge

theorem rank_one_two_exists_central_order_two_coset
    (hpgroup : IsPGroup 2 G) (hrank : NoCommutingDistinctInvolutions G)
    (hnonabelian : ∃ first second : G, first * second ≠ second * first) :
    ∃ element : G,
      QuotientGroup.mk' (Subgroup.center G) element ∈ Subgroup.center (G ⧸ Subgroup.center G) ∧
      orderOf (QuotientGroup.mk' (Subgroup.center G) element) = 2 ∧
      Subgroup.zpowers (element ^ 2) = Subgroup.center G := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hquotientNontrivial : Nontrivial (G ⧸ Subgroup.center G) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsubsingleton
    have hcenterTop := QuotientGroup.subsingleton_iff.mp hsubsingleton
    obtain ⟨first, second, hne⟩ := hnonabelian
    have hcentral : second ∈ Subgroup.center G := by rw [hcenterTop]; trivial
    exact hne (Subgroup.mem_center_iff.mp hcentral first)
  let _ := hquotientNontrivial
  let quotient := G ⧸ Subgroup.center G
  have hquotientP : IsPGroup 2 quotient := hpgroup.to_quotient (Subgroup.center G)
  let _ : Nontrivial (Subgroup.center quotient) := hquotientP.center_nontrivial
  have hdiv : 2 ∣ Nat.card (Subgroup.center quotient) := by
    rcases (hquotientP.to_subgroup (Subgroup.center quotient)).card_eq_or_dvd with hone | hdiv
    · exact (not_subsingleton (Subgroup.center quotient)
        (Nat.card_eq_one_iff_unique.mp hone).1).elim
    · exact hdiv
  obtain ⟨central, horder⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center quotient) 2 hdiv
  obtain ⟨element, helement⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) central.val
  have horderElement : orderOf (QuotientGroup.mk' (Subgroup.center G) element) = 2 := by
    rw [helement, Subgroup.orderOf_coe, horder]
  refine ⟨element, helement ▸ central.property, horderElement,
    rank_one_two_central_coset_square_generates_center hpgroup hrank element horderElement⟩

end CFSG.DisconnectedInvolutionGraph.Helpers
