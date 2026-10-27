module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.HighestRoot

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration.ExcOuterLeOne

@[expose] def d4F2Node : Fin Tag.D4.rank := ⟨2, by decide⟩

@[expose] def d4F2Theta : Fin Tag.D4.rank → ℤ := ![1, 1, 2, 1]

@[expose] def d4F2Lvl (γ : Fin Tag.D4.rank → ℤ) : ℤ := γ d4F2Node

@[expose] def d4F2Delta1 : Fin Tag.D4.rank → ℤ := Pi.single d4F2Node 1

@[expose] def d4F2Delta2 : Fin Tag.D4.rank → ℤ := d4F2Theta - Pi.single d4F2Node 1

@[expose] def d4F2Eps : Fin 3 → (Fin Tag.D4.rank → ℤ) := ![d4F2Theta, d4F2Delta2, 0]

@[expose] def d4F2A2Root (i j : Fin 3) : Fin Tag.D4.rank → ℤ := d4F2Eps i - d4F2Eps j

section Facts

theorem d4F2_theta_mem : d4F2Theta ∈ rootFinset Tag.D4 := by decide +kernel

theorem d4F2_isRoot_theta : IsRoot Tag.D4 d4F2Theta := mem_rootFinset.1 d4F2_theta_mem

theorem d4F2_theta_isMax : IsMaxHeightRoot Tag.D4 d4F2Theta := by
  refine ⟨d4F2_isRoot_theta, fun γ hγ => ?_⟩
  have key : ∀ γ ∈ rootFinset Tag.D4, height γ ≤ height d4F2Theta := by decide +kernel
  exact key γ (mem_rootFinset.2 hγ)

theorem d4F2_lvl_bound {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) :
    -2 ≤ d4F2Lvl γ ∧ d4F2Lvl γ ≤ 2 := by
  have key : ∀ γ ∈ rootFinset Tag.D4, -2 ≤ d4F2Lvl γ ∧ d4F2Lvl γ ≤ 2 := by decide +kernel
  exact key γ (mem_rootFinset.2 hγ)

theorem d4F2_eq_theta_of_lvl {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (h : d4F2Lvl γ = 2) : γ = d4F2Theta := by
  have key : ∀ γ ∈ rootFinset Tag.D4, d4F2Lvl γ = 2 → γ = d4F2Theta := by decide +kernel
  exact key γ (mem_rootFinset.2 hγ) h

theorem d4F2_height_pos_of_lvl_pos {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (h : 0 < d4F2Lvl γ) : 0 < height γ := by
  have key : ∀ γ ∈ rootFinset Tag.D4, 0 < d4F2Lvl γ → 0 < height γ := by decide +kernel
  exact key γ (mem_rootFinset.2 hγ) h

theorem d4F2_isRoot_delta1 : IsRoot Tag.D4 d4F2Delta1 := isRoot_single Tag.D4 d4F2Node

theorem d4F2_lvl_delta1 : d4F2Lvl d4F2Delta1 = 1 := by
  simp [d4F2Lvl, d4F2Delta1]

theorem d4F2_isRoot_delta2 : IsRoot Tag.D4 d4F2Delta2 := by
  have key : d4F2Delta2 ∈ rootFinset Tag.D4 := by decide +kernel
  exact mem_rootFinset.1 key

theorem d4F2_lvl_delta2 : d4F2Lvl d4F2Delta2 = 1 := by decide +kernel

end Facts

end CFSG.LieType.SeitzGeneration.ExcWideThree
