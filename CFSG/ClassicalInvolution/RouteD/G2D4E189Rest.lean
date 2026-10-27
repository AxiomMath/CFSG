module

public import CFSG.ClassicalInvolution.Asc77.AscE189Final
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Twin
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime]

@[expose] def NoTwinsFund (p e : ℕ) [Fact p.Prime] (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ F ∈ modelFund p e t n, ∀ c : ModelGrp p e t n, IsUniqueInvolution F c →
    ∀ g : ModelGrp p e t n, IsUniqueInvolution (conjSub g F) c → conjSub g F = F

theorem e189ModelAt_of_noTwinsFund {e : ℕ} {t : StatedLieTag} {n : ℕ}
    (hZ : Subgroup.center (ModelGrp p e t n) = ⊥) (h : NoTwinsFund p e t n) :
    E189ModelAt p e t n := by
  intro N hN F₁ hF₁ z₁ hz₁ g hcomm _ h3 _ _
  have hc : ⁅z₁, g * z₁ * g⁻¹⁆ = 1 := by
    have h1 : ⁅z₁, g * z₁ * g⁻¹⁆ ∈ Subgroup.center (ModelGrp p e t n) := hN hcomm
    rw [hZ] at h1
    exact Subgroup.mem_bot.mp h1
  have hc' : z₁ * (g * z₁ * g⁻¹) = (g * z₁ * g⁻¹) * z₁ :=
    commutatorElement_eq_one_iff_mul_comm.mp hc
  have htz : (g * z₁ * g⁻¹) * z₁ * (g * z₁ * g⁻¹)⁻¹ = z₁ := by
    calc (g * z₁ * g⁻¹) * z₁ * (g * z₁ * g⁻¹)⁻¹
        = z₁ * (g * z₁ * g⁻¹) * (g * z₁ * g⁻¹)⁻¹ := by rw [hc']
      _ = z₁ := by group
  have hz₂ : IsUniqueInvolution (conjSub (g * z₁ * g⁻¹) F₁) z₁ := by
    have := hz₁.conj (g * z₁ * g⁻¹)
    rwa [htz] at this
  exact absurd (h F₁ hF₁ z₁ hz₁ (g * z₁ * g⁻¹) hz₂) h3

theorem noTwinsFund_g2 {e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .G2 0 p e) :
    NoTwinsFund p e .G2 0 :=
  noTwins_g2 hp2 hadm.2.1

theorem e189ModelAt_g2_odd {e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .G2 0 p e) :
    E189ModelAt p e .G2 0 :=
  e189ModelAt_of_noTwinsFund
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inl rfl) 0
      hadm.2.1)
    (noTwinsFund_g2 hp2 hadm)

theorem noTwinsFund_td4_of_maxNormalizer (hM : G2D4MaxNormalizer p) {e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 0 p e) : NoTwinsFund p e .trialityD4 0 := by
  intro F hF c hc g hg
  exact conjSub_eq_of_same_involution hc hg
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0
      hadm.2.1)
    (hM .trialityD4 0 e hadm hp2 (Or.inr rfl) F hF)

theorem e189ModelAt_td4_of_maxNormalizer (hM : G2D4MaxNormalizer p) {e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 0 p e) : E189ModelAt p e .trialityD4 0 :=
  e189ModelAt_of_noTwinsFund
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0
      hadm.2.1)
    (noTwinsFund_td4_of_maxNormalizer hM hp2 hadm)

theorem e189Rest_of_maxNormalizer (hM : G2D4MaxNormalizer p) : E189Rest p where
  g2 _ hp2 hadm := e189ModelAt_g2_odd hp2 hadm
  td4 _ hp2 hadm := e189ModelAt_td4_of_maxNormalizer hM hp2 hadm

end CFSG.ClassicalInvolution.G2D4Models
