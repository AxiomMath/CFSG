module

public import CFSG.CGT.PushingUpLit.SolKNA.Lemma18C4
public import CFSG.CGT.T75N.BenderCenter
public import CFSG.CGT.T75N.UnitaryTwoGen

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem lemma18_abelian_final
    (hSz : Lemma18SzAbelian)
    {R : Subgroup G} {g : G} {Z : Subgroup G} (hgZ : g ∈ Z) (hRZ : R ≤ Z)
    (hR2 : IsPGroup 2 R) (hTI : IsTIIn Z R)
    {T C N : Subgroup G}
    (hT : T = conjSubgroup g R ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hinf : R ⊓ conjSubgroup g R = ⊥)
    (hC : C = R ⊓ Subgroup.centralizer (T : Set G))
    (hΦ₁ : ∀ x ∈ R, x * x ∈ C) (hΦ₂ : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ C)
    (hCZ : ∀ c ∈ C, ∀ x ∈ R, c * x = x * c)
    (hCT : Nonempty (↥C ≃* ↥T)) (hT2 : ∀ x ∈ T, x * x = 1) (hCR : C ≠ R)
    (hN : N = C ⊔ T) (hNnorm : R ⊔ conjSubgroup g R ≤ Subgroup.normalizer (N : Set G))
    (hΦb₁ : ∀ x ∈ conjSubgroup g R, x * x ∈ T)
    (hΦb₂ : ∀ x ∈ conjSubgroup g R, ∀ y ∈ conjSubgroup g R, x * y * x⁻¹ * y⁻¹ ∈ T)
    (hTZ : ∀ t ∈ T, ∀ x ∈ conjSubgroup g R, t * x = x * t) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a :=
  lemma18_abelian CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput hSz
    hgZ hRZ hR2 hTI hT hT0 hinf hC hΦ₁ hΦ₂ hCZ hCT hT2 hCR hN hNnorm hΦb₁ hΦb₂ hTZ

theorem lemma18_abelian_eq_final
    {R : Subgroup G} {g : G} {Z : Subgroup G} (hgZ : g ∈ Z) (hRZ : R ≤ Z)
    (hR2 : IsPGroup 2 R) (hTI : IsTIIn Z R)
    {T C N : Subgroup G}
    (hT : T = conjSubgroup g R ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hinf : R ⊓ conjSubgroup g R = ⊥)
    (hC : C = R ⊓ Subgroup.centralizer (T : Set G))
    (hΦ₁ : ∀ x ∈ R, x * x ∈ C) (hΦ₂ : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ C)
    (hCZ : ∀ c ∈ C, ∀ x ∈ R, c * x = x * c)
    (hCT : Nonempty (↥C ≃* ↥T)) (hT2 : ∀ x ∈ T, x * x = 1) (hCR : C ≠ R)
    (he : C.relIndex R = Nat.card T)
    (hN : N = C ⊔ T) (hNnorm : R ⊔ conjSubgroup g R ≤ Subgroup.normalizer (N : Set G))
    (hΦb₁ : ∀ x ∈ conjSubgroup g R, x * x ∈ T)
    (hΦb₂ : ∀ x ∈ conjSubgroup g R, ∀ y ∈ conjSubgroup g R, x * y * x⁻¹ * y⁻¹ ∈ T)
    (hTZ : ∀ t ∈ T, ∀ x ∈ conjSubgroup g R, t * x = x * t) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a :=
  lemma18_abelian_eq CFSG.CGT.T75N.benderCenterInput CFSG.CGT.T75N.unitaryTwoGenerationInput
    hgZ hRZ hR2 hTI hT hT0 hinf hC hΦ₁ hΦ₂ hCZ hCT hT2 hCR he hN hNnorm hΦb₁ hΦb₂ hTZ

theorem lemma18_normalizer_conj_final
    {R : Subgroup G} {g : G} {Z : Subgroup G} (hgZ : g ∈ Z) (hRZ : R ≤ Z)
    (hR2 : IsPGroup 2 R) (hTI : IsTIIn Z R)
    {T C N : Subgroup G}
    (hT : T = conjSubgroup g R ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hinf : R ⊓ conjSubgroup g R = ⊥)
    (hC : C = R ⊓ Subgroup.centralizer (T : Set G))
    (hΦ₁ : ∀ x ∈ R, x * x ∈ C) (hΦ₂ : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ C)
    (hCZ : ∀ c ∈ C, ∀ x ∈ R, c * x = x * c)
    (hCT : Nonempty (↥C ≃* ↥T)) (hT2 : ∀ x ∈ T, x * x = 1) (hCR : C ≠ R)
    (hrel : C.relIndex R = 4) (hT4 : Nat.card T = 4)
    (hN : N = C ⊔ T) (hNnorm : R ⊔ conjSubgroup g R ≤ Subgroup.normalizer (N : Set G))
    (hΦb₁ : ∀ x ∈ conjSubgroup g R, x * x ∈ T)
    (hΦb₂ : ∀ x ∈ conjSubgroup g R, ∀ y ∈ conjSubgroup g R, x * y * x⁻¹ * y⁻¹ ∈ T)
    (hTZ : ∀ t ∈ T, ∀ x ∈ conjSubgroup g R, t * x = x * t) :
    ∀ z ∈ C, z ≠ 1 → ∀ z' ∈ C, z' ≠ 1 →
      ∃ k ∈ R ⊔ conjSubgroup g R, k ∈ Subgroup.normalizer (R : Set G) ∧ k * z * k⁻¹ = z' :=
  lemma18_exists_normalizer_conj_of_four CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput hgZ hRZ hR2 hTI hT hT0 hinf hC hΦ₁ hΦ₂ hCZ hCT hT2 hCR
    hrel hT4 hN hNnorm hΦb₁ hΦb₂ hTZ

end CFSG.CGT.PushingUpLit.SolKNA
