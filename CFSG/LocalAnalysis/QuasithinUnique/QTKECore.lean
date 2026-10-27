module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.Open.SQTKSimpleListTauCeti
public import CFSG.LocalAnalysis.QuasithinUnique.Reduction

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

@[expose] def quasithinIsQTKECat (G : Type) [Group G] [Finite G] : Prop :=
  CFSG.Assembly.Quasithin.QTKEOver CFSG.Blueprint.Catalog G

variable {G : Type} [Group G]

theorem catalog_of_commutative (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hcomm : ∀ a b : S, a * b = b * a) : CFSG.Blueprint.Catalog S :=
  CFSG.SectionRank.catalog_containsAbelianSimple S hcomm

theorem ne_top_of_pCoreOf_ne_bot_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {P : Subgroup G} (hP : pCoreOf 2 P ≠ ⊥) : P ≠ ⊤ := by
  rintro rfl
  have hnorm : (pCoreOf 2 (⊤ : Subgroup G)).Normal := by
    have hle : (⊤ : Subgroup G) ≤ Subgroup.normalizer (pCoreOf 2 (⊤ : Subgroup G) : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 ⊤
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact hP h
  · have h2 : IsPGroup 2 (⊤ : Subgroup G) :=
      h ▸ CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 ⊤
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hG2 : IsPGroup 2 G := h2.of_equiv Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnonab
    have : Nontrivial G := ⟨⟨a, 1, fun h => hab (by rw [h]; simp)⟩⟩
    have hZ : Nontrivial (Subgroup.center G) := hG2.center_nontrivial
    have hcomm : ∀ x y : G, x * y = y * x := by
      rcases (Subgroup.center G).normal_of_characteristic.eq_bot_or_eq_top with hc | hc
      · exfalso
        obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := hZ.exists_pair_ne
        rw [hc, Subgroup.mem_bot] at hx hy
        exact hxy (Subtype.ext (hx.trans hy.symm))
      · intro x y
        have hx : x ∈ Subgroup.center G := hc ▸ Subgroup.mem_top x
        exact (Subgroup.mem_center_iff.mp hx y).symm
    exact hab (hcomm a b)

theorem isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank [Finite G]
    (he : CFSG.Assembly.evenRank G ≤ 2) {P : Subgroup G} (hP : pCoreOf 2 P ≠ ⊥) :
    CFSG.IsStronglyQuasithin P := by
  rw [CFSG.SectionRank.isStronglyQuasithin_iff]
  intro p hp hp2
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 P : Set G)) :=
    ⟨pCoreOf 2 P, hP, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 P, rfl⟩
  have hPN : P ≤ Subgroup.normalizer (pCoreOf 2 P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 P
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup P) ≤ CFSG.Open.pRank p P := by
    have h := CFSG.SectionRank.pRank_le_map hp.one_lt P.subtype P.subtype_injective ⊤
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  calc CFSG.Open.pRank p (⊤ : Subgroup P) ≤ CFSG.Open.pRank p P := h1
    _ ≤ CFSG.Open.pRank p (Subgroup.normalizer (pCoreOf 2 P : Set G)) :=
        CFSG.SectionRank.pRank_mono hp.one_lt hPN
    _ ≤ CFSG.Assembly.evenRank G :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 _ hloc
    _ ≤ 2 := he

theorem catalog_of_kProper_of_surjective
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (K : Subgroup G) (hKtop : K ≠ ⊤)
    (S : Type) [Group S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S)
    (hφ : Function.Surjective φ) : CFSG.Blueprint.Catalog S :=
  CFSG.KCore.KProperNonab.catalogue_of_surjective CFSG.SectionRank.catalog_isoInvariant hK K hKtop
    hnonab φ hφ

theorem isKGroupCat_of_kProper [Finite G] (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {P : Subgroup G} (hP : P ≠ ⊤) : CFSG.SectionRank.IsKGroupCat P :=
  CFSG.KCore.KProperNonab.kGroupAllSimple CFSG.SectionRank.catalog_isoInvariant
    CFSG.SectionRank.catalog_containsAbelianSimple hK P hP

theorem qtkeCore_of_cat [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : quasithinIsQTKECat G) : QTKECore G :=
  ⟨fun _ hP => ⟨isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank h.2.2 hP,
    isKGroupCat_of_kProper h.1 (ne_top_of_pCoreOf_ne_bot_of_simple hnonab hP)⟩, h.2.1, h.2.2⟩

@[expose] def TCKGroupBridgeSQT : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsStronglyQuasithin X →
    CFSG.Open.SQTKTauCeti.KGroup X → CFSG.SectionRank.IsKGroupCat X

theorem tcKGroup_of_kProper (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    {P : Subgroup G} (hP : P ≠ ⊤) : CFSG.Open.SQTKTauCeti.KGroup P :=
  CFSG.KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant hK P hP

theorem qtkeCore_of_tauCeti (hB : TCKGroupBridgeSQT) [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h : CFSG.Assembly.Quasithin.quasithinIsQTKE G) :
    QTKECore G :=
  ⟨fun P hP =>
    have hSQT := isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank h.2.2 hP
    ⟨hSQT, hB P hSQT (tcKGroup_of_kProper h.1 (ne_top_of_pCoreOf_ne_bot_of_simple hnonab hP))⟩,
    h.2.1, h.2.2⟩

end CFSG.QuasithinUnique
