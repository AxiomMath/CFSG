module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThreeTA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpenDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoClassical

theorem card_center_rightConjugate {G : Type} [Group G] (A : Subgroup G) (g : G) :
    Nat.card (center ↥(rightConjugate A g)) = Nat.card (center ↥A) := by
  rw [← Subgroup.map_center_eq (conjEquiv A g)]
  exact (Subgroup.card_map_of_injective (conjEquiv A g).injective).symm

theorem altThreeCover_of
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (hcfg : Section3Config) : AltThreeCover := by
  intro G _ _ A hH hO n hn6 hn7 ⟨e⟩ hodd
  have hn : n = 6 ∨ n = 7 := by omega
  obtain ⟨R, T, g, hc⟩ := exists_sec3_of hcfg (hyp31_of hH hO (by omega) e)
  obtain ⟨⟨sA⟩, ⟨sB⟩⟩ := Three.exists_sides hc h32 h4 h34 h2 hn e hodd
  have hR2 : ∀ r ∈ R, r * r = 1 := fun r hr => by
    have h := (hc.elemR h32).2 r hr
    rwa [sq] at h
  have hT2 : ∀ t ∈ T, t * t = 1 := fun t ht => by
    have h := (hc.elemT h32).2 t ht
    rwa [sq] at h
  have hTsyl : IsSylowOf 2 T (centralizer (rightConjugate A g : Set G)) := by
    rw [AS76b.centralizer_rightConjugate]
    exact hc.sylowT
  have hNR : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
    have h := Lemma36.normalizer_le hc.hyp hc.sylowR 1
    rwa [rightConjugate_one, rightConjugate_one] at h
  have hNT : normalizer (T : Set G) ≤ normalizer (rightConjugate A g : Set G) := by
    have h := Lemma36.normalizer_le hc.hyp hc.swap.sylowR g
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h
  have hoddB : Odd (Nat.card (center ↥(rightConjugate A g))) := by
    rw [card_center_rightConjugate]
    exact hodd
  exact Three.center_eq_bot sA sB hn hR2 hT2 hc.sylowR hTsyl hc.le_centralizer hNR hNT hodd
    hoddB hH.standard.1.1

theorem altThreeCover :
    AltThreeCover :=
  altThreeCover_of RankTwoFoundation.lemma32 RankTwoFoundation.asc75Theorem4 AS76b.asc08Lemma34
    RankTwoFoundation.asc76Theorem2 RankTwoFoundation.section3Config

end CFSG.ComponentClassification.RankTwoAlt
