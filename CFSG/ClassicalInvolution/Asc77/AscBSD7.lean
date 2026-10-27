module

public import CFSG.ClassicalInvolution.Asc77.AscBSD5
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.RouteD.Exotic (fundCorr_odd fundCorr_minus)
open CFSG.ClassicalInvolution.Asc77 (ih8_eq_of_map_eq finrank_eq_eight_of_proj hproj_quadMinus
  fund_noncentral_modelUniv five_le_card_galoisField)
open CFSG.Assembly.LowTwoRank

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Spin

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem spin_two_bound (hodd : Odd (Nat.card F))
    (hrange : (spinAction Q).range = elementaryGroup Q) (hZ : CenterScalar Q) [Nontrivial V]
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {𝓕 : Set (Subgroup (spinGroup Q))} (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ 𝓕, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ 𝓕, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    {R₀ R₁ R₂ : Subgroup (spinGroup Q)} (h₀ : R₀ ∈ 𝓕) (h₁ : R₁ ∈ 𝓕) (h₂ : R₂ ∈ 𝓕)
    {r₀ r₁ r₂ : spinGroup Q} (hr₀ : IsInvIn R₀ r₀) (hr₁ : IsInvIn R₁ r₁) (hr₂ : IsInvIn R₂ r₂)
    (h01 : r₀ * r₁⁻¹ ∈ Subgroup.center (spinGroup Q))
    (h12 : r₁ * r₂⁻¹ ∈ Subgroup.center (spinGroup Q)) : R₀ = R₁ ∨ R₁ = R₂ ∨ R₀ = R₂ := by
  classical
  set θ := spinAction Q with hθ
  have hker : θ.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hinj : ∀ R ∈ 𝓕, ∀ r ∈ R, θ r = 1 → r = 1 := fun R hR r hr h =>
    hnc R hR r hr (hker (MonoidHom.mem_ker.mpr h))
  have hfund : ∀ {R : Subgroup (spinGroup Q)} {r : spinGroup Q}, R ∈ 𝓕 → IsInvIn R r →
      IsFundamental Q (R.map θ) (θ r) := by
    intro R r hR hr
    obtain ⟨i, hi⟩ := hcorr R hR
    have hmem : θ r ∈ R.map θ := Subgroup.mem_map_of_mem _ hr.1
    have hsq : θ r * θ r = 1 := by rw [← map_mul, hr.2.1, map_one]
    have hne : θ r ≠ 1 := fun h => hr.2.2 (hinj R hR r hr.1 h)
    have hord : orderOf (θ r) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
    have := hi.eq_of_orderOf_eq_two hodd hmem hord
    rw [this]
    exact hi
  have hsame : ∀ {R R' : Subgroup (spinGroup Q)} {r r' : spinGroup Q}, R ∈ 𝓕 → R' ∈ 𝓕 →
      IsInvIn R r → IsInvIn R' r' → R ≠ R' → r * r'⁻¹ ∈ Subgroup.center (spinGroup Q) →
      θ r = θ r' := by
    intro R R' r r' hR hR' hr hr' hne hc
    have hψ : (QuotientGroup.mk' (Subgroup.center (spinGroup Q))).ker ≤
        Subgroup.center (spinGroup Q) := by
      rw [QuotientGroup.ker_mk']
    have hxx' : QuotientGroup.mk' (Subgroup.center (spinGroup Q)) r =
        QuotientGroup.mk' (Subgroup.center (spinGroup Q)) r' := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have e : r⁻¹ * r' = (r * r'⁻¹)⁻¹ := by
        have h1 : r' * r'⁻¹ = 1 := mul_inv_cancel r'
        have hcomm : r' * (r * r'⁻¹) = (r * r'⁻¹) * r' := Subgroup.mem_center_iff.mp hc r'
        calc r⁻¹ * r' = r⁻¹ * ((r * r'⁻¹)⁻¹ * r) := by
              congr 1
              rw [mul_inv_rev, inv_inv]
              group
          _ = (r * r'⁻¹)⁻¹ := by
              have hc' : (r * r'⁻¹)⁻¹ ∈ Subgroup.center (spinGroup Q) :=
                (Subgroup.center (spinGroup Q)).inv_mem hc
              have := Subgroup.mem_center_iff.mp hc' r⁻¹
              rw [← mul_assoc, this, mul_assoc, inv_mul_cancel, mul_one]
      rw [e]
      exact (Subgroup.center (spinGroup Q)).inv_mem hc
    obtain ⟨F₁, -, -, hx, hx'⟩ := swap_of_twin_pair hodd hrange hZ hproj (hperf R hR)
      (hperf R' hR') (hcorr R hR) (hcorr R' hR') (hinj R hR) (hinj R' hR') hne hr.1 hr.2.1
      hr.2.2 hr'.1 hr'.2.1 hr'.2.2 (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) hψ hxx'
    rw [hx, hx', Frame.La_swap_neg_one]
  by_cases e01 : R₀ = R₁
  · exact Or.inl e01
  by_cases e02 : R₀ = R₂
  · exact Or.inr (Or.inr e02)
  refine Or.inr (Or.inl ?_)
  have h02 : r₀ * r₂⁻¹ ∈ Subgroup.center (spinGroup Q) := by
    have := (Subgroup.center (spinGroup Q)).mul_mem h01 h12
    simpa [mul_assoc] using this
  have s01 := hsame h₀ h₁ hr₀ hr₁ e01 h01
  have s02 := hsame h₀ h₂ hr₀ hr₂ e02 h02
  have f₀ := hfund h₀ hr₀
  have f₁ : IsFundamental Q (R₁.map θ) (θ r₀) := s01 ▸ hfund h₁ hr₁
  have f₂ : IsFundamental Q (R₂.map θ) (θ r₀) := s02 ▸ hfund h₂ hr₂
  obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin hodd f₀
  rcases huniq _ f₁ with a1 | a1
  · exact absurd (ih8_eq_of_map_eq θ hker (hperf R₁ h₁) (hperf R₀ h₀) a1).symm e01
  rcases huniq _ f₂ with a2 | a2
  · exact absurd (ih8_eq_of_map_eq θ hker (hperf R₂ h₂) (hperf R₀ h₀) a2).symm e02
  exact ih8_eq_of_map_eq θ hker (hperf R₁ h₁) (hperf R₂ h₂) (a1.trans a2.symm)

end Spin

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
