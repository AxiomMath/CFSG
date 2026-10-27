module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple

public section

namespace CFSG.ComponentClassification.CatalogueBIndexTwo

theorem centralizer_solvable_of_normal_fixed {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hindex : N.index ≤ 2) (t : G)
    (hfixed : Group.IsSolvable ((Subgroup.centralizer ({t} : Set G)).subgroupOf N)) :
    Group.IsSolvable (Subgroup.centralizer ({t} : Set G)) := by
  let C := Subgroup.centralizer ({t} : Set G)
  let F := N.subgroupOf C
  let : Group.IsSolvable ((Subgroup.centralizer ({t} : Set G)).subgroupOf N) := hfixed
  let : Group.IsSolvable F := Group.isSolvable_of_isSolvable_injective
    (f := (CatalogueRelativeB.normalFixedEquivalence N t).toMonoidHom)
    (CatalogueRelativeB.normalFixedEquivalence N t).injective
  let : Group.IsSolvable (G ⧸ N) :=
    CatalogueRelativeB.quotient_solvable_of_index_le_two N hindex
  let q := (QuotientGroup.mk' N).domRestrict C
  apply Group.isSolvable_of_ker_le_range F.subtype q
  simp only [q, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', Subgroup.range_subtype]
  exact le_rfl

theorem quotient_restriction_injective_of_inf_eq_bot {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (S : Subgroup G) (hinf : S ⊓ N = ⊥) :
    Function.Injective ((QuotientGroup.mk' N).domRestrict S) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro s hs
  have hN : s.val ∈ N := (QuotientGroup.eq_one_iff s.val).mp hs
  have hboth : s.val ∈ S ⊓ N := ⟨s.property, hN⟩
  rw [hinf] at hboth
  exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hboth))

theorem disjoint_two_subgroup_eq_zpowers {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hindex : N.index ≤ 2)
    (S : Subgroup G) (hne : S ≠ ⊥) (htwo : IsPGroup 2 S) (hinf : S ⊓ N = ⊥) :
    ∃ t : G, orderOf t = 2 ∧ t ∉ N ∧ S = Subgroup.zpowers t := by
  have hcard := Nat.card_le_card_of_injective ((QuotientGroup.mk' N).domRestrict S)
    (quotient_restriction_injective_of_inf_eq_bot N S hinf)
  rw [← Subgroup.index_eq_card] at hcard
  have hcardTwo : Nat.card S ≤ 2 := hcard.trans hindex
  obtain ⟨t, ht, htS, _⟩ := BFailureLocalization.exists_central_involution S htwo hne
  have htN : t ∉ N := by
    intro hN
    have hboth : t ∈ S ⊓ N := ⟨htS, hN⟩
    rw [hinf] at hboth
    have hone : t = 1 := Subgroup.mem_bot.mp hboth
    simp [hone] at ht
  refine ⟨t, ht, htN, ?_⟩
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htS)
  simpa only [Nat.card_zpowers, ht] using hcardTwo

theorem normalizer_twoComponent_le_centralizer {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (htwo : IsPGroup 2 S)
    (L : Subgroup (Subgroup.normalizer (S : Set G)))
    (hL : TwoComponents.IsTwoComponent L) (t : G) (htS : t ∈ S) :
    L.map (Subgroup.normalizer (S : Set G)).subtype ≤
      Subgroup.centralizer ({t} : Set G) := by
  let H := Subgroup.normalizer (S : Set G)
  have hc := CatalogueBAlternating.pComponent_le_centralizer_normal_p 2 L
    (S.subgroupOf H) ((CatalogueBAlternating.pComponent_two_iff L).mpr hL)
    htwo.comap_subtype
  rintro x ⟨l, hl, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  have hy' : y = t := Set.mem_singleton_iff.mp hy
  subst y
  have hcomm := Subgroup.mem_centralizer_iff.mp (hc hl)
    (⟨t, S.le_normalizer htS⟩ : H) htS
  exact congrArg Subtype.val hcomm

end CFSG.ComponentClassification.CatalogueBIndexTwo
