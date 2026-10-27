module

public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.GH74.Uniqueness.Bender.OuterLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.BenderSuzuki

theorem BenderType.exists_conj_outer_involution {K : Type*} [Group K] {n : ℕ}
    (h : BenderType K n 1 1) (α β : MulAut K) (hα : α * α = 1) (hβ : β * β = 1)
    (hαo : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹)
    (hβo : ¬ ∃ g : K, ∀ x : K, β x = g * x * g⁻¹) :
    ∃ g : K, ∀ x : K, β x = g * α (g⁻¹ * x * g) * g⁻¹ := by
  obtain ⟨hn, ⟨e⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSL2Model n) := by
    cases h with
    | linear n hn e => exact ⟨hn, ⟨e⟩⟩
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  let θ : K ≃* coordinateG (GaloisField 2 n) := e.trans (pslEquivCoordinateG (GaloisField 2 n))
  have hα' := mulAut_congr_sq_eq_one θ hα
  have hβ' := mulAut_congr_sq_eq_one θ hβ
  have hαo' := not_inner_congr θ hαo
  have hβo' := not_inner_congr θ hβo
  obtain ⟨-, a, σ, h₀, hαa, hh₀, hah₀, -, -, hσpow, -⟩ :=
    exists_normal_form_outer_involution_coordinateG (by omega) hcard _ hα' hαo'
  obtain ⟨-, a', σ', h₀', hβa, hh₀', hah₀', -, -, hσpow', -⟩ :=
    exists_normal_form_outer_involution_coordinateG (by omega) hcard _ hβ' hβo'
  have hσσ : σ = σ' := RingEquiv.ext fun x => by rw [hσpow, hσpow']
  subst hσσ
  set g₀ : coordinateG (GaloisField 2 n) := ⟨h₀' * h₀⁻¹, mul_mem hh₀' (inv_mem hh₀)⟩ with hg₀
  have key : ∀ y : coordinateG (GaloisField 2 n), MulAut.congr θ β y =
      g₀ * MulAut.congr θ α (g₀⁻¹ * y * g₀) * g₀⁻¹ := by
    intro y
    apply Subtype.ext
    have e1 := hβa y
    have e2 := hαa (g₀⁻¹ * y * g₀)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e2 ⊢
    rw [e1, e2, hah₀', hah₀]
    have hg₀v : (g₀ : Equiv.Perm (Omega (GaloisField 2 n))) = h₀' * h₀⁻¹ := rfl
    rw [hg₀v]
    group
  refine ⟨θ.symm g₀, fun x => ?_⟩
  apply θ.injective
  have e1 : θ (β x) = MulAut.congr θ β (θ x) := by simp [MulAut.congr_apply]
  have e2 : θ (θ.symm g₀ * α ((θ.symm g₀)⁻¹ * x * θ.symm g₀) * (θ.symm g₀)⁻¹) =
      g₀ * MulAut.congr θ α (g₀⁻¹ * θ x * g₀) * g₀⁻¹ := by
    simp [MulAut.congr_apply]
  rw [e1, e2]
  exact key (θ x)

end CFSG.GH74.Uniqueness.Bender
