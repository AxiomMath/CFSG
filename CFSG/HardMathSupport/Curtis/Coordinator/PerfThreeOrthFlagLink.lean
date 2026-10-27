module

public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthClosure

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_invariant_totSingular [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hK2 : ∀ c : K, c = 0 ∨ c = 1)
    {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hJtop : ¬ elementaryGroup Q ≤ J) {e₁ : V} (he₁ : e₁ ≠ 0) (he₁Q : Q e₁ = 0)
    (H1 : ∀ y, eichler Q e₁ y ∈ J) :
    ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧ ∀ g ∈ J, ∀ x ∈ W, g x ∈ W := by
  have hQ0 : Q 0 = 0 := QuadraticMap.map_zero Q
  have hRe : ∀ y, eichler Q (0 : V) y ∈ J := fun y => by
    rw [eichler_zero_left]
    exact J.one_mem
  have hfix : ∀ g ∈ J, g (0 : V) = 0 := fun g _ => map_zero g
  have hGood : Good Q J (0 : V) e₁ := by
    refine ⟨polar_zero_left Q e₁, ?_, he₁Q, fun y _ _ => H1 y⟩
    rw [Submodule.span_zero_singleton]
    exact fun h => he₁ (by simpa using h)
  by_cases hpair : ∃ w w₂, Good Q J (0 : V) w ∧ Good Q J (0 : V) w₂ ∧ polar Q w w₂ = 1
  · exfalso
    obtain ⟨w, w₂, hw, hw₂, hww⟩ := hpair
    apply hJtop
    refine elementaryGroup_le_of_eichler_mem fun u w' hu hw' => ?_
    by_cases hu0 : u = 0
    · subst hu0
      exact hRe w'
    · have hspan : u ∉ Submodule.span K {(0 : V)} := by
        rw [Submodule.span_zero_singleton]
        exact fun h => hu0 (by simpa using h)
      have := good_of_pair hQ hK2 hJ hQ0 hRe hfix hw hw₂ hww (polar_zero_left Q u) hspan hu
      exact this.2.2.2 w' (polar_zero_left Q w') hw'
  · push Not at hpair
    obtain ⟨W, hWQ, hWJ, -, hWgood⟩ := exists_totSingular_of_pairFree hK2 hJ hQ0 hfix
      (fun w w₂ hw hw₂ => hpair w w₂ hw hw₂)
    refine ⟨W, ?_, hWQ, hWJ⟩
    intro hbot
    have := hWgood e₁ hGood
    rw [hbot, Submodule.mem_bot] at this
    exact he₁ this

end CFSG.HardMathSupport.Curtis.Coordinator
