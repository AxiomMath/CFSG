module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionGraph
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicPSubgroupOrder

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

@[expose] def cyclicRootSet (element : G) : Set G :=
  {root | element ∈ Subgroup.zpowers root}

structure IsTISupport (support : Set G) (subgroup : Subgroup G) : Prop where
  nonempty : support.Nonempty
  identity_not_mem : 1 ∉ support
  normalizer_eq : Subgroup.normalizer support = subgroup
  conjugate_mem_forces : ∀ actor member : G, member ∈ support →
    actor * member * actor⁻¹ ∈ support → actor ∈ subgroup

theorem ti_support_outside_conjugates_disjoint (support : Set G) (subgroup : Subgroup G)
    (hti : IsTISupport support subgroup) (actor : G) (houtside : actor ∉ subgroup) :
    Disjoint support ((MulAut.conj actor) '' support) := by
  rw [Set.disjoint_left]
  rintro member hmem ⟨other, hother, rfl⟩
  exact houtside (hti.conjugate_mem_forces actor other hother hmem)

theorem cyclic_root_set_inverse (element root : G) :
    root⁻¹ ∈ cyclicRootSet element ↔ root ∈ cyclicRootSet element := by
  change element ∈ Subgroup.zpowers root⁻¹ ↔ element ∈ Subgroup.zpowers root
  rw [Subgroup.zpowers_inv]

theorem cyclic_root_set_centralizes (element root : G) (hroot : root ∈ cyclicRootSet element) :
    root ∈ Subgroup.centralizer ({element} : Set G) := by
  obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp hroot
  rw [Subgroup.mem_centralizer_iff]
  intro other hother
  rw [Set.mem_singleton_iff.mp hother, ← hexponent]
  exact (Commute.refl root).zpow_left exponent |>.eq

theorem cyclic_overgroup_equal_card_subgroups [Finite G] (cyclic : Subgroup G) [IsCyclic cyclic]
    (first second : Subgroup G) (hfirst : first ≤ cyclic) (hsecond : second ≤ cyclic)
    (hcard : Nat.card first = Nat.card second) : first = second := by
  have hfirstCard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hfirst).toEquiv
  have hsecondCard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsecond).toEquiv
  have hrelative : first.subgroupOf cyclic = second.subgroupOf cyclic := by
    have hequal := hfirstCard.trans (hcard.trans hsecondCard.symm)
    apply le_antisymm
    · exact cyclic_subgroup_le_of_card_dvd _ _ (hequal ▸ dvd_refl _)
    · exact cyclic_subgroup_le_of_card_dvd _ _ (hequal.symm ▸ dvd_refl _)
  have hinter := Subgroup.subgroupOf_inj.mp hrelative
  simpa only [inf_eq_left.mpr hfirst, inf_eq_left.mpr hsecond] using hinter

theorem cyclic_root_conjugate_forces_normalizer [Finite G]
    (element actor root : G) (hroot : root ∈ cyclicRootSet element)
    (hconjugate : actor * root * actor⁻¹ ∈ cyclicRootSet element) :
    actor ∈ Subgroup.normalizer (Subgroup.zpowers element : Set G) := by
  let cyclic := Subgroup.zpowers root
  let first := Subgroup.zpowers element
  let second := first.map (MulAut.conj actor⁻¹).toMonoidHom
  have hfirst : first ≤ cyclic := Subgroup.zpowers_le.mpr hroot
  have hconjugateLe : first ≤ cyclic.map (MulAut.conj actor).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr hconjugate
  have hsecond : second ≤ cyclic := by
    intro member hmem
    obtain ⟨other, hother, rfl⟩ := hmem
    have hmap := Subgroup.mem_map_equiv.mp (hconjugateLe hother)
    change actor⁻¹ * other * actor ∈ cyclic at hmap
    change actor⁻¹ * other * actor⁻¹⁻¹ ∈ cyclic
    simpa only [inv_inv] using hmap
  have hcard : Nat.card first = Nat.card second :=
    Nat.card_congr ((MulAut.conj actor⁻¹).subgroupMap first).toEquiv
  have hequal := cyclic_overgroup_equal_card_subgroups cyclic first second hfirst hsecond hcard
  have hinverse : actor⁻¹ ∈ Subgroup.normalizer (first : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hequal.symm
  simpa only [inv_inv] using (Subgroup.normalizer (first : Set G)).inv_mem hinverse

theorem cyclic_root_normalizer_preserves (element actor root : G)
    (hactor : actor ∈ Subgroup.normalizer (Subgroup.zpowers element : Set G)) :
    root ∈ cyclicRootSet element ↔ actor * root * actor⁻¹ ∈ cyclicRootSet element := by
  have hnormal := Subgroup.mem_normalizer_iff_map_conj_eq.mp hactor
  change (Subgroup.zpowers element).map (MulAut.conj actor).toMonoidHom =
    Subgroup.zpowers element at hnormal
  change element ∈ Subgroup.zpowers root ↔ element ∈ Subgroup.zpowers (actor * root * actor⁻¹)
  rw [← Subgroup.zpowers_le, ← Subgroup.zpowers_le]
  have hmap := Subgroup.map_le_map_iff_of_injective
    (f := (MulAut.conj actor).toMonoidHom) (MulAut.conj actor).injective
    (H := Subgroup.zpowers element) (K := Subgroup.zpowers root)
  rw [hnormal, MonoidHom.map_zpowers] at hmap
  exact hmap.symm

theorem cyclic_root_set_ti [Finite G] (element : G) (hne : element ≠ 1) :
    IsTISupport (cyclicRootSet element) (Subgroup.normalizer (Subgroup.zpowers element : Set G)) := by
  have hself : element ∈ cyclicRootSet element := Subgroup.mem_zpowers element
  refine ⟨⟨element, hself⟩, ?_, ?_, cyclic_root_conjugate_forces_normalizer element⟩
  · simpa only [cyclicRootSet, Set.mem_ofPred_eq, Subgroup.zpowers_one_eq_bot,
      Subgroup.mem_bot] using hne
  · apply le_antisymm
    · intro actor hactor
      have hconjugate := (Subgroup.mem_set_normalizer_iff.mp hactor element).mp hself
      exact cyclic_root_conjugate_forces_normalizer element actor element hself hconjugate
    · intro actor hactor
      apply Subgroup.mem_set_normalizer_iff.mpr
      intro root
      exact cyclic_root_normalizer_preserves element actor root hactor

theorem cyclic_root_set_has_no_involution (element : G) (horder : 2 < orderOf element)
    (involution : Involution G) : (involution : G) ∉ cyclicRootSet element := by
  intro hroot
  have hdiv := orderOf_dvd_of_mem_zpowers hroot
  rw [involution.property] at hdiv
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

theorem ti_involution_product_factors_mem (support : Set G) (subgroup : Subgroup G)
    (hti : IsTISupport support subgroup)
    (hinverse : ∀ member ∈ support, member⁻¹ ∈ support)
    (first second : Involution G) (hproduct : (first : G) * second ∈ support) :
    (first : G) ∈ subgroup ∧ (second : G) ∈ subgroup := by
  have hfirstInverse : (first : G)⁻¹ = first := by
    apply inv_eq_of_mul_eq_one_left
    have hpower := pow_orderOf_eq_one (first : G)
    rwa [first.property, pow_two] at hpower
  have hsecondInverse : (second : G)⁻¹ = second := by
    apply inv_eq_of_mul_eq_one_left
    have hpower := pow_orderOf_eq_one (second : G)
    rwa [second.property, pow_two] at hpower
  have hinverted := hinverse ((first : G) * second) hproduct
  have hfirstConjugate : (first : G) * ((first : G) * second) * (first : G)⁻¹ =
      ((first : G) * second)⁻¹ := by
    rw [mul_inv_rev, hfirstInverse, hsecondInverse]
    have hfirstSquare : (first : G) * first = 1 := by
      have hpower := pow_orderOf_eq_one (first : G)
      rwa [first.property, pow_two] at hpower
    rw [← mul_assoc, hfirstSquare, one_mul]
  have hsecondConjugate : (second : G) * ((first : G) * second) * (second : G)⁻¹ =
      ((first : G) * second)⁻¹ := by
    rw [mul_inv_rev, hfirstInverse, hsecondInverse]
    have hsecondSquare : (second : G) * second = 1 := by
      have hpower := pow_orderOf_eq_one (second : G)
      rwa [second.property, pow_two] at hpower
    simp only [mul_assoc, hsecondSquare, mul_one]
  constructor
  · apply hti.conjugate_mem_forces (first : G) ((first : G) * second) hproduct
    exact hfirstConjugate ▸ hinverted
  · apply hti.conjugate_mem_forces (second : G) ((first : G) * second) hproduct
    exact hsecondConjugate ▸ hinverted

end CFSG.DisconnectedInvolutionGraph.Helpers
