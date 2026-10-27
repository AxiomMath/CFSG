module

public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair
import CFSG.FeitThompson.Representations.ParityRealCharacterInnerProducts
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {G : Type*} [Group G]

theorem bridge_mem_span_Irr {θ Γ : G → ℂ} (hθ : θ ∈ signedIrr G)
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) :
    (1 : G → ℂ) - θ + Γ ∈ Submodule.span ℤ (Irr G) :=
  Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.subset_span one_mem_Irr)
    (mem_span_Irr_of_mem_signedIrr hθ)) hΓ

variable [Fintype G]

theorem exists_int_cfInner_bridge {α θ Γ : G → ℂ} (hα : α ∈ signedIrr G)
    (hθ : θ ∈ signedIrr G) (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) :
    ∃ c : ℤ, cfInner ((1 : G → ℂ) - θ + Γ) α = (c : ℂ) :=
  exists_int_cfInner_of_mem_span_Irr (bridge_mem_span_Irr hθ hΓ)
    (mem_span_Irr_of_mem_signedIrr hα)

theorem cfInner_add_cfInner_bridge {α θ Γ Δ : G → ℂ}
    (hα1 : cfInner α (1 : G → ℂ) = 0) (hθ1 : cfInner θ (1 : G → ℂ) = 0)
    (hαθ : cfInner α θ = 0) (hΓ1 : cfInner Γ (1 : G → ℂ) = 0)
    (hΔ1 : cfInner Δ (1 : G → ℂ) = 0)
    (hβB : cfInner ((1 : G → ℂ) - α + Δ) ((1 : G → ℂ) - θ + Γ) = 0)
    {c : ℝ} (hc : cfInner ((1 : G → ℂ) - θ + Γ) α = (c : ℂ)) :
    cfInner ((1 : G → ℂ) - α + Δ) θ + cfInner ((1 : G → ℂ) - θ + Γ) α
      = 1 + cfInner Δ Γ := by
  have h1α : cfInner (1 : G → ℂ) α = 0 := by rw [← conj_cfInner, hα1, map_zero]
  have h1θ : cfInner (1 : G → ℂ) θ = 0 := by rw [← conj_cfInner, hθ1, map_zero]
  have h1Γ : cfInner (1 : G → ℂ) Γ = 0 := by rw [← conj_cfInner, hΓ1, map_zero]
  have hθα : cfInner θ α = 0 := by rw [← conj_cfInner, hαθ, map_zero]
  have hΓα : cfInner Γ α = (c : ℂ) := by
    rw [cfInner_add_left, cfInner_sub_left, h1α, hθα] at hc; simpa using hc
  have hαΓ : cfInner α Γ = (c : ℂ) := by rw [← conj_cfInner, hΓα]; simp
  have hb : cfInner ((1 : G → ℂ) - α + Δ) θ = cfInner Δ θ := by
    rw [cfInner_add_left, cfInner_sub_left, h1θ, hαθ]; ring
  rw [hb, hc]
  simp only [cfInner_add_left, cfInner_sub_left, cfInner_add_right, cfInner_sub_right,
    cfInner_one_one, h1θ, h1Γ, hα1, hαθ, hαΓ, hΔ1] at hβB
  linear_combination -hβB

theorem add_eq_one_add_of_bridge {α θ Γ Δ : G → ℂ}
    (hα1 : cfInner α (1 : G → ℂ) = 0) (hθ1 : cfInner θ (1 : G → ℂ) = 0)
    (hαθ : cfInner α θ = 0) (hΓ1 : cfInner Γ (1 : G → ℂ) = 0)
    (hΔ1 : cfInner Δ (1 : G → ℂ) = 0)
    (hβB : cfInner ((1 : G → ℂ) - α + Δ) ((1 : G → ℂ) - θ + Γ) = 0)
    {b c d : ℤ} (hc : cfInner ((1 : G → ℂ) - θ + Γ) α = (c : ℂ))
    (hb : cfInner ((1 : G → ℂ) - α + Δ) θ = (b : ℂ))
    (hd : cfInner Δ Γ = (d : ℂ)) : b + c = 1 + d := by
  have h := cfInner_add_cfInner_bridge hα1 hθ1 hαθ hΓ1 hΔ1 hβB
    (c := (c : ℝ)) (by rw [hc]; norm_cast)
  rw [hb, hc, hd] at h
  have : ((b + c : ℤ) : ℂ) = ((1 + d : ℤ) : ℂ) := by push_cast; linear_combination h
  exact_mod_cast this

theorem odd_add_and_xor_odd_of_bridge (hodd : Odd (Nat.card G)) {α θ Γ Δ : G → ℂ}
    (hα1 : cfInner α (1 : G → ℂ) = 0) (hθ1 : cfInner θ (1 : G → ℂ) = 0)
    (hαθ : cfInner α θ = 0)
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ g, (Γ g).im = 0)
    (hΓ1 : cfInner Γ (1 : G → ℂ) = 0)
    (hΔ : Δ ∈ Submodule.span ℤ (Irr G)) (hΔreal : ∀ g, (Δ g).im = 0)
    (hΔ1 : cfInner Δ (1 : G → ℂ) = 0)
    (hβB : cfInner ((1 : G → ℂ) - α + Δ) ((1 : G → ℂ) - θ + Γ) = 0)
    {b c : ℤ} (hc : cfInner ((1 : G → ℂ) - θ + Γ) α = (c : ℂ))
    (hb : cfInner ((1 : G → ℂ) - α + Δ) θ = (b : ℂ)) :
    Odd (b + c) ∧ Xor (Odd b) (Odd c) := by
  obtain ⟨d, hd⟩ := exists_int_cfInner_of_mem_span_Irr hΔ hΓ
  have hsum := add_eq_one_add_of_bridge hα1 hθ1 hαθ hΓ1 hΔ1 hβB hc hb hd
  obtain ⟨k, hk⟩ := (intCast_cfInner_modEq_mul_of_odd hodd hΔ hΓ hΔreal hΓreal hd
    (a := 0) (by simpa using hΔ1) (b := 0) (by simpa using hΓ1)).dvd
  refine ⟨by rw [Int.odd_iff]; omega, ?_⟩
  rcases Int.even_or_odd b with hb' | hb'
  · rw [Int.even_iff] at hb'
    exact Or.inr ⟨by rw [Int.odd_iff]; omega, by rw [Int.odd_iff]; omega⟩
  · rw [Int.odd_iff] at hb'
    exact Or.inl ⟨by rw [Int.odd_iff]; omega, by rw [Int.odd_iff]; omega⟩

theorem two_bridge_parity (hodd : Odd (Nat.card G)) {α θ Γ Δ : G → ℂ}
    (hα : α ∈ signedIrr G) (hθ : θ ∈ signedIrr G)
    (hα1 : cfInner α (1 : G → ℂ) = 0) (hθ1 : cfInner θ (1 : G → ℂ) = 0)
    (hαθ : cfInner α θ = 0)
    (hΓ : Γ ∈ Submodule.span ℤ (Irr G)) (hΓreal : ∀ g, (Γ g).im = 0)
    (hΓ1 : cfInner Γ (1 : G → ℂ) = 0)
    (hΔ : Δ ∈ Submodule.span ℤ (Irr G)) (hΔreal : ∀ g, (Δ g).im = 0)
    (hΔ1 : cfInner Δ (1 : G → ℂ) = 0)
    (hβB : cfInner ((1 : G → ℂ) - α + Δ) ((1 : G → ℂ) - θ + Γ) = 0) :
    ∃ b c : ℤ, cfInner ((1 : G → ℂ) - θ + Γ) α = (c : ℂ) ∧
      cfInner ((1 : G → ℂ) - α + Δ) θ = (b : ℂ) ∧
      ((b : ℂ) + (c : ℂ) = 1 + cfInner Δ Γ) ∧ Odd (b + c) ∧ Xor (Odd b) (Odd c) := by
  obtain ⟨c, hc⟩ := exists_int_cfInner_bridge hα hθ hΓ
  obtain ⟨b, hb⟩ := exists_int_cfInner_bridge hθ hα hΔ
  refine ⟨b, c, hc, hb, ?_,
    odd_add_and_xor_odd_of_bridge hodd hα1 hθ1 hαθ hΓ hΓreal hΓ1 hΔ hΔreal hΔ1 hβB hc hb⟩
  have h := cfInner_add_cfInner_bridge hα1 hθ1 hαθ hΓ1 hΔ1 hβB
    (c := (c : ℝ)) (by rw [hc]; norm_cast)
  rw [hb, hc] at h
  linear_combination h

end CFSG.FeitThompson
