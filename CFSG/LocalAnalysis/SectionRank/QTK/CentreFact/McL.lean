module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBON
public import Certificates.Certificate7263
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.QTK.CoverB

variable {G : Type} [Group G] [Finite G]

theorem mclSigned_check :
    SignedData.check (ops3 21) mclSigned = true :=
  Certificates.certificate7263

theorem exists_signed_McL :
    ∃ (R : Subgroup NativeSporadic.McL) (a b d₁ d₂ : NativeSporadic.McL),
      R ≠ ⊥ ∧ IsPGroup 2 R ∧ a ∈ normalizer (R : Set _) ∧ b ∈ normalizer (R : Set _) ∧
        a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
        (∀ i j : ℕ, i < 3 → j < 3 → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0) ∧
        d₁ * a * d₁⁻¹ = a⁻¹ ∧ d₁ * b * d₁⁻¹ = b ∧ d₂ * b * d₂⁻¹ = b⁻¹ :=
  SignedData.exists_of_check (spec3 21) mclSigned mclSigned_check

theorem not_three_dvd_card_center_of_McL
    (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G} (e : ↥Y ⧸ center ↥Y ≃* NativeSporadic.McL) :
    ¬ 3 ∣ Nat.card (center ↥Y) := by
  obtain ⟨R, a, b, d₁, d₂, hR, hR2, ha, hb, ha3, hb3, hab, hind, h1, h2, h3⟩ := exists_signed_McL
  exact @not_dvd_card_center_of_signed_equiv G _ _ he Y NativeSporadic.McL Units.instGroup e 3
    Nat.prime_three (by norm_num) R hR hR2 a b d₁ d₂ ha hb ha3 hb3 hab hind h1 h2 h3

end CFSG.SectionRank.QTK.CentreFact
