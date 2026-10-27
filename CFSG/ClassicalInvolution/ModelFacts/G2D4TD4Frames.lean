module

public import CFSG.LieType.Steinberg.TwistedD4.Fixed
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Characters

variable (K : Type) [Field K]

@[expose] def aLongTD4 : Fin d4.rank → Kˣ := ![-1, -1, 1, -1]

@[expose] def aShortTD4 : Fin d4.rank → Kˣ := ![1, 1, -1, 1]

variable {K}

theorem neg_one_zpow_eq_one_iff_mod (hK : (-1 : Kˣ) ≠ 1) (n : ℤ) :
    (-1 : Kˣ) ^ n = 1 ↔ n % 2 = 0 := by
  rcases Int.even_or_odd n with h | h
  · rw [h.neg_one_zpow]
    simp [Int.even_iff.mp h]
  · rw [h.neg_one_zpow]
    refine ⟨fun h1 => absurd h1 hK, fun h2 => ?_⟩
    have := Int.odd_iff.mp h
    omega

theorem rootChar_four (a : Fin d4.rank → Kˣ) (γ : Fin d4.rank → ℤ) :
    rootChar a γ = a (nd 0) ^ γ (nd 0) * a (nd 1) ^ γ (nd 1) * a (nd 2) ^ γ (nd 2) *
      a (nd 3) ^ γ (nd 3) :=
  Fin.prod_univ_four (fun i : Fin 4 => a i ^ γ i)

theorem rootChar_aLong_eq_one_iff (hK : (-1 : Kˣ) ≠ 1) (γ : Fin d4.rank → ℤ) :
    rootChar (aLongTD4 K) γ = 1 ↔ (γ (nd 0) + γ (nd 1) + γ (nd 3)) % 2 = 0 := by
  have h : rootChar (aLongTD4 K) γ = (-1 : Kˣ) ^ (γ (nd 0) + γ (nd 1) + γ (nd 3)) := by
    rw [rootChar_four, show aLongTD4 K (nd 0) = -1 from rfl, show aLongTD4 K (nd 1) = -1 from rfl,
      show aLongTD4 K (nd 2) = 1 from rfl, show aLongTD4 K (nd 3) = -1 from rfl, one_zpow,
      mul_one, zpow_add, zpow_add]
  rw [h, neg_one_zpow_eq_one_iff_mod hK]

theorem rootChar_aShort_eq_one_iff (hK : (-1 : Kˣ) ≠ 1) (γ : Fin d4.rank → ℤ) :
    rootChar (aShortTD4 K) γ = 1 ↔ γ (nd 2) % 2 = 0 := by
  have h : rootChar (aShortTD4 K) γ = (-1 : Kˣ) ^ γ (nd 2) := by
    rw [rootChar_four, show aShortTD4 K (nd 0) = 1 from rfl, show aShortTD4 K (nd 1) = 1 from rfl,
      show aShortTD4 K (nd 2) = -1 from rfl, show aShortTD4 K (nd 3) = 1 from rfl, one_zpow,
      one_zpow, one_zpow, one_mul, one_mul, mul_one]
  rw [h, neg_one_zpow_eq_one_iff_mod hK]

end Characters

section Long

theorem long_rho_fixed : ∀ γ ∈ rootFinset d4, (γ (nd 0) + γ (nd 1) + γ (nd 3)) % 2 = 0 →
    rho γ = γ → γ = Pi.single (nd 2) 1 ∨ γ = -Pi.single (nd 2) 1 := by decide +kernel

theorem long_commute : ∀ γ ∈ rootFinset d4, (γ (nd 0) + γ (nd 1) + γ (nd 3)) % 2 = 0 →
    0 < height γ → γ ≠ Pi.single (nd 2) 1 →
    γ ≠ -Pi.single (nd 2) 1 ∧ γ + Pi.single (nd 2) 1 ∉ rootFinset d4 ∧
      γ + -Pi.single (nd 2) 1 ∉ rootFinset d4 := by decide +kernel

theorem long_closed : ∀ α ∈ rootFinset d4, ∀ β ∈ rootFinset d4,
    (α (nd 0) + α (nd 1) + α (nd 3)) % 2 = 0 → (β (nd 0) + β (nd 1) + β (nd 3)) % 2 = 0 →
    0 < height α → 0 < height β → α + β ∉ rootFinset d4 := by decide +kernel

theorem long_rho_stable : ∀ γ ∈ rootFinset d4, (γ (nd 0) + γ (nd 1) + γ (nd 3)) % 2 = 0 →
    0 < height γ → rho γ ∈ rootFinset d4 ∧
      (rho γ (nd 0) + rho γ (nd 1) + rho γ (nd 3)) % 2 = 0 ∧ 0 < height (rho γ) := by
  decide +kernel

end Long

section Short

theorem short_rho_ne : ∀ γ ∈ rootFinset d4, γ (nd 2) % 2 = 0 → rho γ ≠ γ →
    (γ = Pi.single (nd 0) 1 ∨ γ = Pi.single (nd 1) 1 ∨ γ = Pi.single (nd 3) 1 ∨
      γ = -Pi.single (nd 0) 1 ∨ γ = -Pi.single (nd 1) 1 ∨ γ = -Pi.single (nd 3) 1) := by
  decide +kernel

theorem short_commute : ∀ γ ∈ rootFinset d4, γ (nd 2) % 2 = 0 → 0 < height γ →
    γ ≠ Pi.single (nd 0) 1 → γ ≠ Pi.single (nd 1) 1 → γ ≠ Pi.single (nd 3) 1 →
    (γ ≠ -Pi.single (nd 0) 1 ∧ γ + Pi.single (nd 0) 1 ∉ rootFinset d4 ∧
      γ + -Pi.single (nd 0) 1 ∉ rootFinset d4) ∧
    (γ ≠ -Pi.single (nd 1) 1 ∧ γ + Pi.single (nd 1) 1 ∉ rootFinset d4 ∧
      γ + -Pi.single (nd 1) 1 ∉ rootFinset d4) ∧
    (γ ≠ -Pi.single (nd 3) 1 ∧ γ + Pi.single (nd 3) 1 ∉ rootFinset d4 ∧
      γ + -Pi.single (nd 3) 1 ∉ rootFinset d4) := by
  decide +kernel

theorem short_closed : ∀ α ∈ rootFinset d4, ∀ β ∈ rootFinset d4,
    α (nd 2) % 2 = 0 → β (nd 2) % 2 = 0 → 0 < height α → 0 < height β →
    α + β ∉ rootFinset d4 := by decide +kernel

theorem short_rho_stable : ∀ γ ∈ rootFinset d4, γ (nd 2) % 2 = 0 → 0 < height γ →
    rho γ ∈ rootFinset d4 ∧ rho γ (nd 2) % 2 = 0 ∧ 0 < height (rho γ) := by decide +kernel

end Short

end CFSG.ClassicalInvolution.G2D4Models
