module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSec72

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

section Lemmas

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem aParts_alpha (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (h2 : Asc76Theorem2) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hF : ClassicalCentralizerCharTwo) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    (h222 : Classical222Large) {D : ClassicalModel A} (hch : Choice74 D R T g) {t p : G}
    (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) : AParts A R T p (D.alpha p) := by
  rcases hc.case222 h32 h4 h34 h2 hOut hF hTy h222 D hch.four_le ht ht1 hp hρ with
    ⟨hle, -, hI⟩ | hII
  · have hprim := hch.primary t ht ht1 p hp hρ
    rcases hI with ⟨hJ, hreg, -⟩ | h23 | h4'
    · have hcen := hreg.centralizer_le ⟨hle t ht p hp hρ, hc.aPart_ne_one ht ht1 hρ⟩
        (le_normalizer_jGroup A p)
      rw [hJ] at hle hcen
      exact hc.aParts_of ht ht1 hp hρ hle hcen
    · exact absurd h23 (D.not_case23_of_isPrimary hprim)
    · exact absurd h4' (D.not_case4_of_isPrimary hprim)
  · exfalso
    have h : T ⊓ A = T := inf_eq_left.mpr hII.1
    rw [hch.inf_eq_bot] at h
    exact hc.T_ne_bot h.symm

theorem exists_aParts_swap (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (h2 : Asc76Theorem2) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hF : ClassicalCentralizerCharTwo) (hTy : RankTwoClassicalEvenType (rankTwoQuot A))
    (h222 : Classical222Large) {D : ClassicalModel A} (hch : Choice74 D R T g) :
    ∃ p₂ : G, AParts A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p₂ (jGroup A p₂) := by
  have hsw := hc.swap
  obtain ⟨t, ht, ht1⟩ := (rightConjugate R g⁻¹).bot_or_exists_ne_one.resolve_left hsw.T_ne_bot
  obtain ⟨p, hp, hρ⟩ := hsw.exists_aPart h32 h4 h34 ht
  refine ⟨p, ?_⟩
  rcases hsw.case222 h32 h4 h34 h2 hOut hF hTy h222 D hch.four_le ht ht1 hp hρ with
    ⟨hle, -, hI⟩ | hII
  · have hpJ : p ∈ jGroup A p := hle t ht p hp hρ
    have hp1 := hsw.aPart_ne_one ht ht1 hρ
    refine hsw.aParts_of ht ht1 hp hρ hle ?_
    rcases hI with ⟨-, hreg, -⟩ | ⟨ℓ, a, b, -, -, -, hpa, hpb, hreg, -⟩ | ⟨-, hreg, -⟩
    · exact hreg.centralizer_le ⟨hpJ, hp1⟩ (le_normalizer_jGroup A p)
    · exact hreg.centralizer_le ⟨hpJ, hpa, hpb⟩ (le_normalizer_jGroup A p)
    · exact hreg.centralizer_le ⟨hpJ, hp1⟩ (le_normalizer_jGroup A p)
  · exact absurd hII.1 (hch.not_le g⁻¹)

end Sec3

end Lemmas

end CFSG.ComponentClassification.RankTwoClassical
