module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBIndexTwoNormalizers
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBLocalB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.CatalogueBIndexTwo

theorem no_normalizer_twoComponent_of_inner_intersection {G : Type*}
    [Group G] [Finite G] (N : Subgroup G) [N.Normal] (hindex : N.index ≤ 2)
    (hinner : ∀ t : G, orderOf t = 2 → t ∈ N →
      Group.IsSolvable ((Subgroup.centralizer ({t} : Set G)).subgroupOf N))
    (S : Subgroup G) (htwo : IsPGroup 2 S) (hmeet : S ⊓ N ≠ ⊥)
    (L : Subgroup (Subgroup.normalizer (S : Set G)))
    (hL : TwoComponents.IsTwoComponent L) : False := by
  have htwoInf : IsPGroup 2 (S ⊓ N : Subgroup G) :=
    htwo.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  obtain ⟨t, ht, htInf, _⟩ :=
    BFailureLocalization.exists_central_involution (S ⊓ N) htwoInf hmeet
  let C := Subgroup.centralizer ({t} : Set G)
  let H := Subgroup.normalizer (S : Set G)
  let : Group.IsSolvable C :=
    centralizer_solvable_of_normal_fixed N hindex t (hinner t ht htInf.2)
  have hle : L.map H.subtype ≤ C :=
    normalizer_twoComponent_le_centralizer S htwo L hL t htInf.1
  let : Group.IsSolvable (L.map H.subtype) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  let e := L.equivMapOfInjective H.subtype H.subtype_injective
  let : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsPerfect L := ⟨TwoComponents.perfect hL⟩
  let : Nontrivial L := TwoComponents.nontrivial hL
  exact Group.IsPerfect.not_isSolvable L inferInstance

theorem normalizer_twoComponent_quasisimple {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hindex : N.index ≤ 2)
    (hinner : ∀ t : G, orderOf t = 2 → t ∈ N →
      Group.IsSolvable ((Subgroup.centralizer ({t} : Set G)).subgroupOf N))
    (houter : ∀ t : G, orderOf t = 2 → t ∉ N →
      ∀ J : Subgroup ((Subgroup.centralizer ({t} : Set G)).subgroupOf N),
        TwoComponents.IsTwoComponent J → Open.IsQuasisimple J)
    (S : Subgroup G) (hne : S ≠ ⊥) (htwo : IsPGroup 2 S)
    (L : Subgroup (Subgroup.normalizer (S : Set G)))
    (hL : TwoComponents.IsTwoComponent L) : Open.IsQuasisimple L := by
  classical
  by_cases hinf : S ⊓ N = ⊥
  · obtain ⟨t, ht, htN, hS⟩ :=
      disjoint_two_subgroup_eq_zpowers N hindex S hne htwo hinf
    have hnormalizer : Subgroup.normalizer (S : Set G) =
        Subgroup.centralizer ({t} : Set G) := by
      rw [hS]
      exact LocalB.normalizer_zpowers_of_involution t ht
    let : Group.IsSolvable (G ⧸ N) :=
      CatalogueRelativeB.quotient_solvable_of_index_le_two N hindex
    revert L
    rw [hnormalizer]
    intro L hL
    exact CatalogueRelativeB.involution_centralizer_twoComponent_quasisimple N t
      (houter t ht htN) L hL
  · exact (no_normalizer_twoComponent_of_inner_intersection N hindex hinner
      S htwo hinf L hL).elim

theorem native_localBProperty {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hindex : N.index ≤ 2)
    (hinner : ∀ t : G, orderOf t = 2 → t ∈ N →
      Group.IsSolvable ((Subgroup.centralizer ({t} : Set G)).subgroupOf N))
    (houter : ∀ t : G, orderOf t = 2 → t ∉ N →
      ∀ J : Subgroup ((Subgroup.centralizer ({t} : Set G)).subgroupOf N),
        TwoComponents.IsTwoComponent J → Open.IsQuasisimple J) :
    LocalB.LocalBProperty G := by
  intro S hne htwo L hL
  exact ⟨le_top, hL.1,
    normalizer_twoComponent_quasisimple N hindex hinner houter S hne htwo L hL⟩

theorem native_normalizer_badSubgroup_eq_bot {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hindex : N.index ≤ 2)
    (hinner : ∀ t : G, orderOf t = 2 → t ∈ N →
      Group.IsSolvable ((Subgroup.centralizer ({t} : Set G)).subgroupOf N))
    (houter : ∀ t : G, orderOf t = 2 → t ∉ N →
      ∀ J : Subgroup ((Subgroup.centralizer ({t} : Set G)).subgroupOf N),
        TwoComponents.IsTwoComponent J → Open.IsQuasisimple J)
    (S : Subgroup G) (hne : S ≠ ⊥) (htwo : IsPGroup 2 S) :
    TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  apply le_bot_iff.mp
  apply sSup_le
  intro L hL
  exact (hL.2 (normalizer_twoComponent_quasisimple N hindex hinner houter
    S hne htwo L hL.1)).elim

theorem localBProperty_and_normalizer_badSubgroup_eq_bot {G : Type*}
    [Group G] [Finite G] (N : Subgroup G) [N.Normal] (hindex : N.index ≤ 2)
    (hinner : ∀ t : G, orderOf t = 2 → t ∈ N →
      Group.IsSolvable ((Subgroup.centralizer ({t} : Set G)).subgroupOf N))
    (houter : ∀ t : G, orderOf t = 2 → t ∉ N →
      ∀ J : Subgroup ((Subgroup.centralizer ({t} : Set G)).subgroupOf N),
        CFSG.IsPComponent 2 J → CFSG.IsQuasisimple J) :
    Assembly.ComponentType.LocalBProperty G ∧
      ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
        TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥ := by
  have houterNative : ∀ t : G, orderOf t = 2 → t ∉ N →
      ∀ J : Subgroup ((Subgroup.centralizer ({t} : Set G)).subgroupOf N),
        TwoComponents.IsTwoComponent J → Open.IsQuasisimple J := by
    intro t ht htN J hJ
    exact CatalogueBAlternating.quasisimple_iff_native.mp
      (houter t ht htN J ((CatalogueBAlternating.pComponent_two_iff J).mpr hJ))
  exact ⟨(AssemblyBLocalB.localBProperty_iff_native G).mpr
    (native_localBProperty N hindex hinner houterNative),
    native_normalizer_badSubgroup_eq_bot N hindex hinner houterNative⟩

end CFSG.ComponentClassification.CatalogueBIndexTwo
