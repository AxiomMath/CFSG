module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient

public section

namespace CFSG.ComponentClassification.Asc76.Lemma22

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_relativeNormalizer {K T S : Subgroup G} (hTK : T ≤ normalizer (K : Set G))
    (hTKb : T ⊓ K = ⊥) (hTS : T ≤ S) (hS : S ≤ K ⊔ T) :
    Nat.card (S ⊓ normalizer (T : Set G) : Subgroup G) =
      Nat.card T * Nat.card (relativeNormalizer T S ⊓ K : Subgroup G) := by
  rw [← relativeNormalizer_card K T S hTK (disjoint_iff.mpr hTKb) hTS hS, relativeNormalizer,
    inf_comm]

theorem card_sup_inf_normalizer {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) :
    Nat.card ((R ⊔ T) ⊓ normalizer (T : Set G) : Subgroup G) = Nat.card T * Nat.card T := by
  have hTKb := inf_eq_bot_of_le hKJ hT.isPGroup (hT.le.trans inf_le_left)
  rw [card_relativeNormalizer (hT.le.trans inf_le_right) hTKb le_sup_right
    (sup_le_sup_right hR.le T), relativeNormalizer_sup_inf hR.le hTR hTKb,
    card_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR]

theorem isSylowOf_sup_inf_normalizer {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) :
    IsSylowOf 2 ((R ⊔ T) ⊓ normalizer (T : Set G)) ((K ⊔ T) ⊓ normalizer (T : Set G)) := by
  have hTJ : T ≤ J := hT.le.trans inf_le_left
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTKb := inf_eq_bot_of_le hKJ hT2 hTJ
  have hS2 : IsPGroup 2 (R ⊔ T : Subgroup G) := hR.isPGroup.to_sup_of_normal_left' hT2 hTR
  obtain ⟨X, hX, hTX⟩ := AschbacherTheorem3.exists_isSylowOf_le hT2
    (le_inf le_sup_right Subgroup.le_normalizer : T ≤ (K ⊔ T) ⊓ normalizer (T : Set G))
  obtain ⟨S', hS', hXS'⟩ := AschbacherTheorem3.exists_isSylowOf_le hX.isPGroup
    (hX.le.trans inf_le_left)
  have hXN : X ≤ normalizer (T : Set G) := hX.le.trans inf_le_right
  have hXKT : X ≤ K ⊔ T := hX.le.trans inf_le_left
  have hXcard : Nat.card X = Nat.card T * Nat.card (relativeNormalizer T X ⊓ K : Subgroup G) := by
    rw [← card_relativeNormalizer hTK hTKb hTX hXKT, inf_eq_left.mpr hXN]
  have hXK : Nat.card (relativeNormalizer T X ⊓ K : Subgroup G) ≤ Nat.card T := by
    refine (Subgroup.card_le_of_le ?_).trans
      (card_relativeNormalizer_inf_le hK hJ hKJ hfac hT hT1 hS'.isPGroup)
    exact inf_le_inf_right K (inf_le_inf_left _ hXS')
  have hle : (R ⊔ T) ⊓ normalizer (T : Set G) ≤ (K ⊔ T) ⊓ normalizer (T : Set G) :=
    inf_le_inf_right _ (sup_le_sup_right hR.le T)
  have hcard : Nat.card X ≤ Nat.card ((R ⊔ T) ⊓ normalizer (T : Set G) : Subgroup G) := by
    rw [card_sup_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR, hXcard]
    exact Nat.mul_le_mul_left _ hXK
  refine isSylowOf_of_card hle (le_antisymm ?_ ?_)
  · rw [← hX.card_eq]
    exact card_le_of_isSylowOf hX hS2.to_inf_left hle
  · rw [← hX.card_eq]
    exact hcard

theorem relIndex_sup_inf_normalizer_le {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) :
    T.relIndex ((R ⊔ T) ⊓ normalizer (T : Set G)) ≤ Nat.card T := by
  have h1 := Subgroup.relIndex_mul_card T ((R ⊔ T) ⊓ normalizer (T : Set G))
  rw [inf_eq_left.mpr (le_inf le_sup_right Subgroup.le_normalizer),
    card_sup_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR] at h1
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).le

theorem thm3Conclusion (h3 : AschbacherTheorem3.Theorem3Statement) {K J T R : Subgroup G}
    (hK : TightlyEmbedded K) (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) :
    AschbacherTheorem3.Thm3Conclusion (bar K K) (bar K T) (bar K (R ⊔ T)) := by
  have hTJ : T ≤ J := hT.le.trans inf_le_left
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTKb := inf_eq_bot_of_le hKJ hT2 hTJ
  have hKTN : K ⊔ T ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  set P := J ⊓ (K ⊔ T) with hP
  have hTP : IsSylowOf 2 T P := hT.of_le (le_inf hTJ le_sup_right) (inf_le_inf_left _ hKTN)
  have heven : Even (Nat.card P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by rw [hn, pow_zero]))
    have h2T : 2 ∣ Nat.card T := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact even_iff_two_dvd.mpr (h2T.trans (Subgroup.card_dvd_of_le hTP.le))
  have htight : ∀ y ∈ K ⊔ T, y ∉ normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G)) := by
    intro y hy hyN
    have hyJ : y ∉ normalizer (J : Set G) := by
      intro hyn
      apply hyN
      rw [← rightConjugate_eq_self_iff] at hyn ⊢
      rw [hP, AschbacherTheorem3.rightConjugate_inf, hyn,
        (rightConjugate_eq_self_iff _ y).mpr (Subgroup.le_normalizer hy)]
    exact (hJ.2 y hyJ).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_inf inf_le_left (Subgroup.map_mono inf_le_left)))
  have hSN := isSylowOf_sup_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR
  exact thm3_bar h3 le_rfl (core_le K) Subgroup.le_normalizer hTK hTK hT2 hT1 hTKb inf_le_right
    hTP heven htight (isSylowOf_sup hR hT2 hTK hTR hTKb) le_sup_right hSN
    (relIndex_sup_inf_normalizer_le hK hJ hKJ hfac hT hT1 hR hTR)

end CFSG.ComponentClassification.Asc76.Lemma22
