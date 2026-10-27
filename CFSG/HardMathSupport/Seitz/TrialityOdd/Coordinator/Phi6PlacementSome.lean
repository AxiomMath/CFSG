module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWCoreDatum
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWMDatum

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.HardMathSupport.Seitz.TrialityOdd.Inner CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.RankThree.PartOne.SEITZ3



@[expose] def Phi6PlacementSome (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → 5 ≤ ℓ ^ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c,
    r.Prime → r ≠ ℓ → (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 →
    ∃ (E₀ : Subgroup (twistedGroup σ.toRingHom)) (w : twistedGroup σ.toRingHom)
      (P : Sylow r (twistedGroup σ.toRingHom)),
      (∀ x ∈ E₀, x ^ r = 1) ∧ Nat.card E₀ = r ^ 2 ∧ w * w = 1 ∧
      (∀ x ∈ E₀, w * x * w⁻¹ = x⁻¹) ∧ E₀ ≤ (P : Subgroup (twistedGroup σ.toRingHom)) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)),
        ∀ y ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x * y = y * x) ∧
      (∀ x ∈ (P : Subgroup (twistedGroup σ.toRingHom)), x ^ r = 1 → x ∈ E₀) ∧
      (∃ u x₁ : twistedGroup σ.toRingHom, u * u = 1 ∧ u ≠ 1 ∧ x₁ ∈ E₀ ∧ x₁ ≠ 1 ∧
        u * w = w * u ∧ u * x₁ = x₁ * u) ∧
      Phi6Placement σ.toRingHom hσ (ℓ ^ f) E₀ w

theorem phi6CoreWGe5_of_placementSome {r : ℕ} (hr5 : 5 ≤ r) (h : Phi6PlacementSome r) :
    Phi6CoreWGe5 r := by
  intro ℓ f hℓ hℓ2 hf hq5 K _ _ hK σ hσq hσ hr hrℓ hd
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨E₀, w, P, hEp, hEc, hww, hwE, hEP, hPc, hPΩ, hU, g, D, x₂, c, a, b, hg, hDs, hDperf,
    hDc, hDw, hx₂E, hx₂1, hDx₂, hDJ, hcE, hc1, hcJ, haE, hbE, haM, hbM, hab⟩ :=
    h ℓ f hℓ hℓ2 hf hq5 K hK σ hσq hσ hr hrℓ hd
  have hqq : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hrq : r ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := by
    have : (((ℓ ^ f) ^ 2 - ℓ ^ f + 1 : ℕ) : ℤ) =
        ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
      push_cast [Nat.cast_sub hqq]
      ring
    exact Int.natCast_dvd_natCast.1 (this ▸ hd)
  obtain ⟨ν, hν, hM⟩ := M_le_of_phi6_datum hℓ hℓ2 hf hq5 hK σ hσq hσ hr hr5 hrq E₀ hEp hEc w hwE g hg
    D hDs hDperf hDc hDw hDJ c hcE hc1 hcJ a b haE hbE haM hbM hab
  have hDH : D ≤ closure (cenGen E₀) := fun d hd' =>
    subset_closure ⟨x₂, hx₂E, hx₂1, hDx₂ d hd'⟩
  have hνE : ∀ x ∈ E₀, ν * x * ν⁻¹ ∈ E₀ := by
    rcases hν with rfl | rfl
    · exact haE
    · exact hbE
  refine ⟨E₀, w, P, hEp, hEc, hww, hwE, hEP, hPc, hPΩ, ⟨g, hg, ?_⟩, hU⟩
  refine hM.trans (sup_le hDH ?_)
  rintro _ ⟨d, hd', rfl⟩
  exact conj_mem_closure_cenGen hνE (hDH hd')

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
