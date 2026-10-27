module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8One
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Split
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Dual

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

theorem tperm_eight_of (hB42 : B42L42Core) : TPerm 8 := by
  intro V _ _ hV H ψ hψ hA hP
  obtain ⟨A, hAoff⟩ := hP
  by_cases hI : ∃ Y₀ Y₁ : Subgroup V, IsChiefFac H Y₀ Y₁ ∧ ¬ IsCentralSec (altPre ψ) Y₀ Y₁ ∧
      NatSec ψ Y₀ Y₁
  ·
    obtain ⟨Y₀, Y₁, hY, -, hN⟩ := hI
    exact Or.inl (natVia_of_natSec hB42 hV hψ hA hAoff hY hN)
  ·
    push Not at hI
    have hι := threeCycleFixFreeOn_of_not_natSec hB42 hV hψ hA hAoff hI
    obtain ⟨h1, h2⟩ := exotic_one_two hV hψ hA hι
    exact Or.inr (Or.inr ⟨rfl, h1, h2, fun hrange B hB =>
      exotic_three hB42 hV hψ hA hI hrange B hB⟩)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
