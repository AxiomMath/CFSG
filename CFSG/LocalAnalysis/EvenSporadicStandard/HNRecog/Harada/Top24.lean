module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24CfgOfG
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Y
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Order3

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}

theorem isKGroupCat_of_kProper [Finite G] (hKP : Assembly.KProper Blueprint.Catalog G)
    (H : Subgroup G) (hH : H ≠ ⊤) : SectionRank.IsKGroupCat H := by
  exact (KCore.kProperNonab_iff_kProperAllSimple SectionRank.catalog_isoInvariant
    SectionRank.catalog_containsAbelianSimple).mp hKP H hH

theorem centralizer_ne_top [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {a : G} (ha : orderOf a = 3) : centralizer ({a} : Set G) ≠ ⊤ := by
  intro htop
  have ha_center : a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({a} : Set G) := by rw [htop]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hcenter : Subgroup.center G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop'
    · exfalso
      have ha1 : a = 1 := by
        have : a ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ha_center
        simpa using this
      rw [ha1, orderOf_one] at ha
      exact (by norm_num : (1 : ℕ) ≠ 3) ha
    · exact htop'
  rcases hnonab with ⟨x, y, hxy⟩
  exact hxy (Subgroup.mem_center_iff.mp (by rw [hcenter]; exact Subgroup.mem_top x) y).symm

theorem harada_lemma_2_4 [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) (hGH : GH73.GH73TheoremA64K)
    (hD : HData G t z b z₁ S Eg T T' W0 ι) (hD3 : HData3 G t z z₁) :
    ¬ ((∀ v, IsConj t (coordElt ι v) ↔ qp v = 1) ∧ inducedGroup ι = OmegaPlus) := by
  rintro ⟨hconj, hind⟩
  obtain ⟨a, ha3', hai⟩ := exists_order_three_induces hD.injective_ι hD.centralizer_le hind
  have h : Setting24 ι a := ⟨hD.injective_ι, hD.centralizer_le, hind, ha3', hai⟩
  have ha3 : orderOf a = 3 := orderOf_eq_three_of_induces hD.injective_ι ha3' hai
  have hat : a ∈ centralizer ({t} : Set G) := mem_centralizer_of_induces_w3 hD.ι_tv hai
  have hcfg := cfg24_of_G hD hD3 hconj h hat ha3
  have hK : SectionRank.IsKGroupCat (Y24 a) :=
    isKGroupCat_of_kProper hKP (centralizer ({a} : Set G)) (centralizer_ne_top hnonab ha3)
  exact false_of_cfg24 hGH hK hcfg

end CFSG.EvenSporadicStandard.HNRecog.Harada
