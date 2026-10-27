module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Foundations.Catalog

public section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.Assembly

abbrev KGroupOver (C : GroupProp) (X : Type) [Group X] : Prop :=
  KCore.KGroupAllSimple C X

theorem isKGroup_iff_kGroupOver {X : Type} [Group X] :
    CFSG.IsKGroup X ↔ KGroupOver InCatalog X :=
  Iff.rfl

theorem isKGroupCat_iff_kGroupOver {X : Type} [Group X] :
    SectionRank.IsKGroupCat X ↔ KGroupOver Blueprint.Catalog X :=
  Iff.rfl

theorem inCatalog_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : InCatalog Y) :
    InCatalog X :=
  inCatalog_isoInvariant e h

theorem catalog_of_abelian_simple (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hcomm : ∀ a b : S, a * b = b * a) : Blueprint.Catalog S :=
  SectionRank.catalog_containsAbelianSimple S hcomm

variable {C : GroupProp}

theorem kGroupOver_of_mulEquiv
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (hY : KGroupOver C Y) : KGroupOver C X :=
  KCore.KGroupAllSimple.of_mulEquiv hC hY e

theorem catalog_of_kGroupOver_of_surjective
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    {X : Type} [Group X] (hX : KGroupOver C X) (K : Subgroup X) {S : Type} [Group S]
    [IsSimpleGroup S] (φ : K →* S) (hφ : Function.Surjective φ) : C S :=
  KCore.KGroupAllSimple.catalogue_of_surjective hC hX K φ hφ

theorem kGroupOver_quotient (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    {X : Type} [Group X] (hX : KGroupOver C X) (M : Subgroup X) [M.Normal] :
    KGroupOver C (X ⧸ M) :=
  KCore.KGroupAllSimple.quotient hC hX M

theorem catalog_of_kProper_of_surjective
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    {G : Type} [Group G] (hK : KProper C G) (K : Subgroup G) (hKtop : K ≠ ⊤) {S : Type}
    [Group S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S)
    (hφ : Function.Surjective φ) : C S :=
  KCore.KProperNonab.catalogue_of_surjective hC hK K hKtop hnonab φ hφ

theorem kGroupOver_of_kProper (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hab : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∀ a b : S, a * b = b * a) → C S)
    {G : Type} [Group G] [Finite G] (hK : KProper C G) (H : Subgroup G) (hH : H ≠ ⊤) :
    KGroupOver C H :=
  KCore.KProperNonab.kGroupAllSimple hC hab hK H hH

theorem section_K_isomorphism {G H : Type} [Group G] [Group H] (f : G ≃* H) :
    (CFSG.IsKGroup G ↔ CFSG.IsKGroup H) ∧
      (SectionRank.IsKGroupCat G ↔ SectionRank.IsKGroupCat H) :=
  ⟨KCore.kGroupAllSimple_congr inCatalog_isoInvariant f,
    KCore.kGroupAllSimple_congr SectionRank.catalog_isoInvariant f⟩

end CFSG.ComponentClassification.UnbalancingLocal
