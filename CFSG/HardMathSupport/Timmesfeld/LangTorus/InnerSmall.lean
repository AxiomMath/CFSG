module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallRankOne
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallG2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Two
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallB2

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false





section Assembly

def B2Two : Prop :=
  ∀ (K : Type) [Field K], (∀ x : K, x = 0 ∨ x = 1) →
    ∀ (M : Type) [CommGroup M] (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
      (i : KernelComponent χ) (s l : Fin Tag.F4.rank → ℤ),
      iform s s = 2 → iform l l = 4 → iform s l = -2 →
      componentRoots χ i = {s, -s, l, -l, s + l, -(s + l), 2 • s + l, -(2 • s + l)} →
      CFSG.IsQuasisimple ↥(⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ :
        Subgroup (ModGL Tag.F4 K))

theorem conclusion_of_perfect {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (hperf : Group.IsPerfect (componentRootSpan K χ i)) :
    CFSG.IsQuasisimple ↥(⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ :
      Subgroup (ModGL τ K)) ∧
      (Nat.card K = 2 ∨
        ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = componentRootSpan K χ i) := by
  have h := Subgroup.isPerfect_iff.1 hperf
  refine ⟨?_, Or.inr h⟩
  have := isQuasisimple_componentRootSpan_of_perfect i hperf
  rwa [h]

theorem two_ne_zero_of_card_three {K : Type} [Field K] [Finite K] (h : Nat.card K = 3) :
    (2 : K) ≠ 0 := by
  classical
  haveI := Fintype.ofFinite K
  intro h2
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hcard' : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact h
  rw [hcard'] at hcard
  have hdvd : ringChar K ∣ 3 := by
    rw [hcard]; exact dvd_pow_self _ n.pos.ne'
  have h3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
  have h2' : ringChar K ∣ 2 := (CharP.cast_eq_zero_iff K (ringChar K) 2).1 (by simpa using h2)
  rw [h3] at h2'
  omega

theorem eq_zero_or_one_of_card_two {K : Type} [Field K] [Finite K] (h : Nat.card K = 2) :
    ∀ x : K, x = 0 ∨ x = 1 := by
  classical
  haveI := Fintype.ofFinite K
  intro x
  by_contra hx
  push Not at hx
  have h3 : ({0, 1, x} : Finset K).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨0, 1, x, zero_ne_one, Ne.symm hx.1, Ne.symm hx.2, rfl⟩
  have := Finset.card_le_univ ({0, 1, x} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, h] at this
  omega

theorem smallFieldInner_of_b2 (hB2 : B2Two) : SmallFieldInner := by
  intro τ K _ _ M _ χ i p hp hp5 hχp hχ1 hK hpC
  classical
  by_cases hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α
  · exact absurd hpC (not_dvd_card_componentRootSpan_of_rank_one hK i hrank hp hp5)
  have hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α := by
    push Not at hrank
    exact hrank
  haveI := Fintype.ofFinite K
  have hcard2 : 2 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hτ : ∀ τ : Tag, τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    intro τ; cases τ <;> simp
  rcases hτ τ with rfl | rfl | h | h | h | h
  · exfalso
    obtain ⟨α, hα, δ, hδ, h1, h2⟩ := hbig
    rcases g2_component_rank_one χ hp hp5 hχp hχ1 i α hα δ hδ with h | h
    · exact h1 h
    · exact h2 h
  ·
    have hK23 : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
    rcases hK23 with hc | hc
    · have hK2 := eq_zero_or_one_of_card_two hc
      by_cases hA2 : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α ∧
          iform α α = iform δ δ ∧ iform α δ ≠ 0
      · exact conclusion_of_perfect i (isPerfect_componentRootSpan_F4_two hK2 i hA2)
      · push Not at hA2
        obtain ⟨s, l, hss, hll, hsl, hΨ⟩ := eq_b2Block_of_noA2 i hbig hA2
        exact ⟨hB2 K hK2 M χ i s l hss hll hsl hΨ, Or.inl hc⟩
    · exact conclusion_of_perfect i
        (isPerfect_componentRootSpan_F4_of_two_ne_zero (two_ne_zero_of_card_three hc) i hbig)
  all_goals
    exact conclusion_of_perfect i (isPerfect_componentRootSpan_simplyLaced (by simp [h]) i hbig)

theorem langComponentsQuasisimple_inner_of_b2 (hW : RootAutIsWeyl) (hB2 : B2Two) :
    LangComponentsQuasisimple .inner :=
  langComponentsQuasisimple_inner_of_small hW (smallFieldInner_of_b2 hB2)

theorem b2Two : B2Two := fun K _ hK2 M _ χ i s l hss hll hsl hΨ =>
  b2_two_derived_quasisimple hK2 i hss hll hsl hΨ

theorem langComponentsQuasisimple_inner_of_rootAutIsWeyl (hW : RootAutIsWeyl) :
    LangComponentsQuasisimple .inner :=
  langComponentsQuasisimple_inner_of_b2 hW b2Two

end Assembly

end CFSG.HardMathSupport.Timmesfeld.LangTorus
