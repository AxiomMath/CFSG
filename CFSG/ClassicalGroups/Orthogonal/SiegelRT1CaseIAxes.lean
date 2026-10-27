module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1CaseII
public import CFSG.ClassicalGroups.Alternating.RT1SpUnipotent

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

theorem caseI_or_caseII (hs : Setting hBN Qf ρ) :
    CaseI hBN ρ ∨ ∀ a c : N, LinearIndependent K ![a, c] → BN a c = 0 →
      axis hBN ρ a 1 ⊓ axis hBN ρ c 1 = ⊥ := by
  by_cases hI : CaseI hBN ρ
  · exact Or.inl hI
  refine Or.inr ?_
  simp only [CaseI, not_forall, not_not] at hI
  obtain ⟨a₀, c₀, hli₀, h₀, hbot⟩ := hI
  intro a c hli hac
  obtain ⟨g, hga, hgc⟩ :=
    exists_gsp_apply_eq_of_isotropic_pair hBN hs.nondegN hli₀ hli h₀ hac
  rw [← hga, ← hgc, ← map_axis_eq, ← map_axis_eq,
    ← Submodule.map_inf _ (ρ g).injective, hbot, Submodule.map_bot]

omit [FiniteDimensional K N] [FiniteDimensional K V] in
theorem CaseI.inf_ne_bot_of_scalars (hI : CaseI hBN ρ) {a c : N}
    (hli : LinearIndependent K ![a, c]) (hac : BN a c = 0) {l m : K} (hl : l ≠ 0) (hm : m ≠ 0) :
    axis hBN ρ a l ⊓ axis hBN ρ c m ≠ ⊥ := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' l
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' m
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hl (by rw [hr, mul_zero])
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hm (by rw [hs, mul_zero])
  have e1 : axis hBN ρ a l = axis hBN ρ (r • a) 1 := by
    rw [axis_smul_eq, mul_one, hr, _root_.sq]
  have e2 : axis hBN ρ c m = axis hBN ρ (s • c) 1 := by
    rw [axis_smul_eq, mul_one, hs, _root_.sq]
  have hli' : LinearIndependent K ![r • a, s • c] := by
    rw [LinearIndependent.pair_iff] at hli ⊢
    intro u v huv
    have h : (u * r) • a + (v * s) • c = 0 := by
      rw [← huv, mul_smul, mul_smul]
    obtain ⟨h1, h2⟩ := hli _ _ h
    exact ⟨(mul_eq_zero.mp h1).resolve_right hr0, (mul_eq_zero.mp h2).resolve_right hs0⟩
  have hac' : BN (r • a) (s • c) = 0 := by
    simp [hac]
  rw [e1, e2]
  exact hI _ _ hli' hac'

theorem CaseI.finrank_axis (hs : Setting hBN Qf ρ) {x : N} (hx : x ≠ 0) {l : K} (hl : l ≠ 0) :
    finrank K (axis hBN ρ x l) = 2 :=
  (hs.siegel x hx l hl).finrank_movedSpace hs.nondeg

theorem CaseI.pow_four_ne_one (hs : Setting hBN Qf ρ) {a b : N} (hab : BN a b ≠ 0) {l m : K}
    (hl : l ≠ 0) (hm : m ≠ 0) : (ρ (Tsp hBN a l) * ρ (Tsp hBN b m)) ^ 4 ≠ 1 := by
  intro h
  refine Tsp_mul_Tsp_pow_four_ne_one hBN hab hl hm (hs.inj ?_)
  rw [map_pow, map_mul, h, map_one]

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
