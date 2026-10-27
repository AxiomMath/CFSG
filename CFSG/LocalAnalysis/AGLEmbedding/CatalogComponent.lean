module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalComponentObstruction

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem IsCatalogGroup.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : IsCatalogGroup B) : IsCatalogGroup A :=
  isCatalogGroup_isoTransfer e.symm hB

@[expose] def CatalogSimpleSections (X : Type*) [Group X] : Prop :=
  ∀ (K : Subgroup X) (L : Subgroup K) (hL : L.Normal), letI := hL;
    IsSimpleGroup (K ⧸ L) → (∃ a b : K ⧸ L, a * b ≠ b * a) → IsCatalogGroup (K ⧸ L)

theorem catalogSimpleSections_iff_isKGroup {X : Type*} [Group X] :
    CatalogSimpleSections X ↔ IsKGroup X := by
  refine ⟨fun h K L _ _ hs hn => h K (L.subgroupOf K) inferInstance hs hn, fun h K L hL hs hn => ?_⟩
  let : L.Normal := hL
  let : IsSimpleGroup (K ⧸ L) := hs
  exact KCore.KGroupNonab.catalogue_of_surjective isCatalogGroup_isoInvariant h K hn
    (QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L)

theorem CatalogSimpleSections.surjective_image {X : Type*} [Group X]
    (hX : CatalogSimpleSections X) (K : Subgroup X) {T : Type*} [Group T] [IsSimpleGroup T]
    (f : K →* T) (hf : Function.Surjective f) (hnonab : ∃ a b : T, a * b ≠ b * a) :
    IsCatalogGroup T :=
  (catalogSimpleSections_iff_isKGroup.mp hX).catalogue_of_surjective_transfer
    isCatalogGroup_isoTransfer K hnonab f hf

theorem CatalogSimpleSections.of_surjective {X Y : Type*} [Group X] [Group Y]
    (hX : CatalogSimpleSections X) (φ : X →* Y) (hφ : Function.Surjective φ) :
    CatalogSimpleSections Y :=
  catalogSimpleSections_iff_isKGroup.mpr
    ((catalogSimpleSections_iff_isKGroup.mp hX).of_surjective_transfer isCatalogGroup_isoTransfer
      φ hφ)

theorem CatalogSimpleSections.subgroup {X : Type*} [Group X] (hX : CatalogSimpleSections X)
    (H : Subgroup X) : CatalogSimpleSections H :=
  catalogSimpleSections_iff_isKGroup.mpr
    ((catalogSimpleSections_iff_isKGroup.mp hX).subgroup H)

theorem CatalogSimpleSections.quotient {X : Type*} [Group X] (hX : CatalogSimpleSections X)
    (N : Subgroup X) [N.Normal] : CatalogSimpleSections (X ⧸ N) :=
  hX.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem CatalogSimpleSections.simple_subgroup {X : Type*} [Group X]
    (hX : CatalogSimpleSections X) (K : Subgroup X) (hsimple : IsSimpleGroup K)
    (hnonab : ∃ a b : K, a * b ≠ b * a) : IsCatalogGroup K := by
  let : IsSimpleGroup K := hsimple
  exact hX.surjective_image K (MonoidHom.id K) Function.surjective_id hnonab

theorem catalogSimpleSections_of_isKProper {G : Type*} [Group G] (hK : IsKProper G)
    (H : Subgroup G) (hH : H ≠ ⊤) : CatalogSimpleSections H :=
  catalogSimpleSections_iff_isKGroup.mpr
    (KCore.KProperNonab.kGroupNonab isCatalogGroup_isoInvariant hK H hH)

theorem isKProper_not_hasPrimeConstraint_catalog_component {G : Type*} [Group G] [Finite G]
    (hK : IsKProper G) (H : Subgroup G) (hH : H ≠ ⊤) (p : ℕ) (hp : p.Prime)
    (hcon : ¬ HasPrimeConstraint (G := H) p) :
    ∃ component : Subgroup (H ⧸ primeComplementCore p),
      IsComponentOf component ⊤ ∧
      component ≤ Subgroup.centralizer (pCore p (H ⧸ primeComplementCore p) : Set _) ∧
      ¬ component ≤ pCore p (H ⧸ primeComplementCore p) ∧
      p ∣ Nat.card component ∧
      p ∣ Nat.card (component ⧸ Subgroup.center component) ∧
      IsCatalogGroup (component ⧸ Subgroup.center component) := by
  let reduced := H ⧸ primeComplementCore (G := H) p
  let centralizing := Subgroup.centralizer (pCore p reduced : Set reduced)
  let : (pCore p centralizing).Normal := pCore_normal p
  have hsections : CatalogSimpleSections (centralizing ⧸ pCore p centralizing) :=
    (((catalogSimpleSections_of_isKProper hK H hH).quotient (primeComplementCore p)).subgroup
      centralizing).quotient (pCore p centralizing)
  obtain ⟨minimalGroup, hminimal, hperfect, hdivides⟩ :=
    non_prime_constrained_centralizer_quotient_has_minimal_normal_perfect_subgroup
      (G := H) p hp hcon
  obtain ⟨simpleFactor, hfactorNormal, hfactorSimple, hfactorNonab⟩ :=
    finite_minimal_normal_perfect_has_simple_normal_factor minimalGroup hminimal hperfect
  let : IsSimpleGroup simpleFactor := hfactorSimple
  have hfactorNontrivial : simpleFactor ≠ ⊥ :=
    simpleFactor.nontrivial_iff_ne_bot.mp inferInstance
  have hfactorDivides := characteristically_simple_normal_factor_prime_dvd
    (minimal_normal_subgroup_characteristically_simple minimalGroup hminimal)
    p hp hdivides simpleFactor hfactorNormal hfactorNontrivial
  have hfactorCatalog : IsCatalogGroup simpleFactor :=
    (hsections.subgroup minimalGroup).simple_subgroup simpleFactor hfactorSimple hfactorNonab
  have hcentral := pCore_centralizer_internal_pCore_le_center (G := reduced) p
  have hkernel : (QuotientGroup.mk' (pCore p centralizing)).ker ≤
      Subgroup.center centralizing := by
    rw [QuotientGroup.ker_mk']
    exact hcentral
  obtain ⟨internal, hinternal, ⟨quotientEquiv⟩⟩ :=
    central_extension_minimal_normal_simple_factor_has_component_lift
      (QuotientGroup.mk' (pCore p centralizing)) (QuotientGroup.mk'_surjective _)
      hkernel minimalGroup hminimal.prop.1 simpleFactor hfactorNormal hfactorSimple hfactorNonab
  have hcentralizingNormal : centralizing.Normal :=
    centralizer_normal_of_normal _ (pCore_normal p)
  let component := Subgroup.map centralizing.subtype internal
  have hcomponent := component_internal_normal_overgroup_maps_to_component
    centralizing hcentralizingNormal internal hinternal
  let componentEquiv := internal.equivMapOfInjective centralizing.subtype
    centralizing.subtype_injective
  have hcard := Nat.card_congr componentEquiv.toEquiv
  have hquotientCard := Nat.card_congr (centerQuotientEquiv componentEquiv).toEquiv
  have hinternalQuotientDivides : p ∣ Nat.card (internal ⧸ Subgroup.center internal) := by
    rw [Nat.card_congr quotientEquiv.toEquiv]
    exact hfactorDivides
  have hinternalDivides : p ∣ Nat.card internal :=
    hinternalQuotientDivides.trans (CFSG.card_dvd_of_surjective
      (QuotientGroup.mk' (Subgroup.center internal)) (QuotientGroup.mk'_surjective _))
  refine ⟨component, hcomponent, Subgroup.map_subtype_le _,
    quasisimple_subgroup_not_le_pCore p hp component hcomponent.2.2, ?_, ?_, ?_⟩
  · rwa [← hcard]
  · rwa [← hquotientCard]
  · exact IsCatalogGroup.of_mulEquiv
      ((centerQuotientEquiv componentEquiv).symm.trans quotientEquiv) hfactorCatalog

end CFSG.AGLEmbedding
