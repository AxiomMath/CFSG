module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6TwoData
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcF4TwoCent
import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6TwoPack
import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6TwoR6Pins

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Curtis.UnitaryLevi (Smat solve_int_fpf wordW wordW_append)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross (laE6 lbE6 wE6 pair_point_int)

@[expose] def e6L2AB : List (Fin Tag.E6.rank) := ([2, 3, 4, 3] : List (Fin Tag.E6.rank))

@[expose] def e6ZsAB : Fin 4 → List (Fin Tag.E6.rank) :=
  ![laE6, e6L2AB, laE6 ++ e6L2AB ++ laE6 ++ laE6, laE6 ++ laE6 ++ e6L2AB ++ laE6]

section WeylAB

theorem e6ZsAB_comm_w : (∀ i, mp6 (e6ZsAB i ++ wE6) = mp6 (wE6 ++ e6ZsAB i)) ∧
    mp6 (e6L2AB ++ wE6) = mp6 (wE6 ++ e6L2AB) := by
  refine ⟨fun i => E6Pack.eqW_spec ?_, E6Pack.eqW_spec ?_⟩
  · revert i
    decide +kernel
  · decide +kernel

theorem e6ZsAB_W : (∀ i : Fin 4, PairOK6 e6XAB (e6ZsAB i)) ∧
    mp6 (e6L2AB ++ e6L2AB ++ e6L2AB) = mp6 [] ∧ mp6 (e6XAB ++ e6L2AB) = mp6 (e6L2AB ++ e6XAB) := by
  refine ⟨fun i => E6Pack.pairOK6_of_pairB ?_, E6Pack.eqW_spec ?_, E6Pack.eqW_spec ?_⟩
  · revert i
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem e6ZsAB_mem (i : Fin 4) : wordW Tag.E6 (e6ZsAB i) ∈
    Subgroup.closure ({wordW Tag.E6 laE6, wordW Tag.E6 e6L2AB} : Set (WeylGroup Tag.E6)) := by
  have h1 : wordW Tag.E6 laE6 ∈
      Subgroup.closure ({wordW Tag.E6 laE6, wordW Tag.E6 e6L2AB} : Set (WeylGroup Tag.E6)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : wordW Tag.E6 e6L2AB ∈
      Subgroup.closure ({wordW Tag.E6 laE6, wordW Tag.E6 e6L2AB} : Set (WeylGroup Tag.E6)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  fin_cases i
  · exact h1
  · exact h2
  · show wordW Tag.E6 (laE6 ++ e6L2AB ++ laE6 ++ laE6) ∈ _
    rw [wordW_append, wordW_append, wordW_append]
    exact mul_mem (mul_mem (mul_mem h1 h2) h1) h1
  · show wordW Tag.E6 (laE6 ++ laE6 ++ e6L2AB ++ laE6) ∈ _
    rw [wordW_append, wordW_append, wordW_append]
    exact mul_mem (mul_mem (mul_mem h1 h1) h2) h1

end WeylAB

theorem e6Z_ab_tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ e : Fin 4 → ℤ,
    (1 - R6 e6XAB).mulVec e = (1 - R6 (e6ZsAB i)).mulVec
      (((a : ℕ) : ℤ) • ![-1, -1, -1, 1] + ((b : ℕ) : ℤ) • ![-1, -1, -1, 0]) := by
  have hY : ∀ i, R6 (e6ZsAB i) = E6R6.zsAB i := by
    intro i
    fin_cases i
    exacts [E6R6.r6_la, E6R6.r6_L2AB, E6R6.r6_zsAB_2, E6R6.r6_zsAB_3]
  simp only [E6R6.r6_XAB, hY]
  intro a b
  fin_cases a <;> fin_cases b
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨1, ![0, -1, -1, 1], by decide +kernel⟩
  · exact ⟨1, ![0, -2, -2, 2], by decide +kernel⟩
  · exact ⟨0, ![0, -1, 1, 0], by decide +kernel⟩
  · exact ⟨3, ![-2, 0, -2, 0], by decide +kernel⟩
  · exact ⟨2, ![-1, 1, -1, 0], by decide +kernel⟩
  · exact ⟨0, ![0, -2, 2, 0], by decide +kernel⟩
  · exact ⟨2, ![-1, 1, -3, 2], by decide +kernel⟩
  · exact ⟨3, ![-4, 0, -4, 0], by decide +kernel⟩

theorem e6Z_ab_D :
    ((1 - R6 e6XAB) * !![-1, 1, 0, 0; -2, 1, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] +
      Matrix.vecMulVec ![-1, -1, -1, 1] ![-1, 1, 0, 1] +
      Matrix.vecMulVec ![-1, -1, -1, 0] ![-1, 0, 0, -1] = 1) ∧
    ((1 - R6 e6XAB).mulVec ![-3, 0, -1, 0] = (3 : ℤ) • ![-1, -1, -1, 1]) ∧
    ((1 - R6 e6XAB).mulVec ![-2, -4, 1, -1] = (3 : ℤ) • ![-1, -1, -1, 0]) ∧
    ((1 - R6 e6XAB) * (2 + R6 e6XAB) = (3 : ℤ) • 1) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((R6 e6XAB).mulVec ![1, -1, 0, -1]) i - ![1, -1, 0, -1] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((R6 e6XAB).mulVec ![0, 0, 1, 0]) i - ![0, 0, 1, 0] i) ∧
    (![1, -1, 0, -1] : Fin 4 → ℤ) 0 = 1 ∧ (![0, 0, 1, 0] : Fin 4 → ℤ) 0 = 0 ∧
    (![1, -1, 0, -1] : Fin 4 → ℤ) 2 = 0 ∧ (![0, 0, 1, 0] : Fin 4 → ℤ) 2 = 1 := by
  rw [E6R6.r6_XAB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem e6Z_ab_data :
    (∀ i : Fin 4, R6 e6XAB * R6 (e6ZsAB i) = R6 (e6ZsAB i) * R6 e6XAB) ∧
    ((1 - R6 e6XAB).mulVec ![0, -1, 1, 0] = (1 - R6 laE6).mulVec ![-1, -1, -1, 1]) ∧
    ((1 - R6 e6XAB).mulVec ![0, -1, -1, 1] = (1 - R6 e6L2AB).mulVec ![-1, -1, -1, 0]) ∧
    (R6 e6XAB * R6 e6L2AB = R6 e6L2AB * R6 e6XAB) := by
  have hY : ∀ i, R6 (e6ZsAB i) = E6R6.zsAB i := by
    intro i
    fin_cases i
    exacts [E6R6.r6_la, E6R6.r6_L2AB, E6R6.r6_zsAB_2, E6R6.r6_zsAB_3]
  have hL : R6 e6L2AB = E6R6.zsAB 1 := E6R6.r6_L2AB
  simp only [E6R6.r6_XAB, hY, hL, E6R6.r6_la]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem e6Z_ab_solve : ∀ c : Fin 4 → ℤ, ∃ i : Fin 4, ∃ e : Fin 4 → ℤ,
    (1 - R6 e6XAB).mulVec e = (1 - R6 (e6ZsAB i)).mulVec c := by
  obtain ⟨D1, D2, D3, -, -, -, -, -, -, -⟩ := e6Z_ab_D
  exact solve_int_fpf (R6 e6XAB) (fun i => R6 (e6ZsAB i)) (e6Z_ab_data).1 _ _ _ _ _ _ _
    D1 D2 D3 e6Z_ab_tab

theorem e6Z_ab_point : ∀ κ : Fin 4 → ℤ, ∃ c d₁ d₂ : Fin 4 → ℤ,
    (1 - R6 e6XAB).mulVec d₁ = (1 - R6 laE6).mulVec c ∧
    (1 - R6 e6XAB).mulVec d₂ = (1 - R6 e6L2AB).mulVec (c - κ) := by
  obtain ⟨D1, -, -, -, -, -, -, -, -, -⟩ := e6Z_ab_D
  obtain ⟨-, h₁, h₃, hY⟩ := e6Z_ab_data
  exact pair_point_int _ _ _ _ _ _ _ _ D1 hY _ _ h₁ h₃

@[expose] def e6L2AB2 : List (Fin Tag.E6.rank) := ([2, 3, 2, 4] : List (Fin Tag.E6.rank))

@[expose] def e6ZsAB2 : Fin 4 → List (Fin Tag.E6.rank) :=
  ![laE6, e6L2AB2, laE6 ++ e6L2AB2 ++ laE6 ++ laE6, laE6 ++ laE6 ++ e6L2AB2 ++ laE6]

section WeylAB2

theorem e6ZsAB2_comm_w : (∀ i, mp6 (e6ZsAB2 i ++ wE6) = mp6 (wE6 ++ e6ZsAB2 i)) ∧
    mp6 (e6L2AB2 ++ wE6) = mp6 (wE6 ++ e6L2AB2) := by
  refine ⟨fun i => E6Pack.eqW_spec ?_, E6Pack.eqW_spec ?_⟩
  · revert i
    decide +kernel
  · decide +kernel

theorem e6ZsAB2_W : (∀ i : Fin 4, PairOK6 e6XAB2 (e6ZsAB2 i)) ∧
    mp6 (e6L2AB2 ++ e6L2AB2 ++ e6L2AB2) = mp6 [] ∧ mp6 (e6XAB2 ++ e6L2AB2) = mp6 (e6L2AB2 ++ e6XAB2) := by
  refine ⟨fun i => E6Pack.pairOK6_of_pairB ?_, E6Pack.eqW_spec ?_, E6Pack.eqW_spec ?_⟩
  · revert i
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem e6ZsAB2_mem (i : Fin 4) : wordW Tag.E6 (e6ZsAB2 i) ∈
    Subgroup.closure ({wordW Tag.E6 laE6, wordW Tag.E6 e6L2AB2} : Set (WeylGroup Tag.E6)) := by
  have h1 : wordW Tag.E6 laE6 ∈
      Subgroup.closure ({wordW Tag.E6 laE6, wordW Tag.E6 e6L2AB2} : Set (WeylGroup Tag.E6)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : wordW Tag.E6 e6L2AB2 ∈
      Subgroup.closure ({wordW Tag.E6 laE6, wordW Tag.E6 e6L2AB2} : Set (WeylGroup Tag.E6)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  fin_cases i
  · exact h1
  · exact h2
  · show wordW Tag.E6 (laE6 ++ e6L2AB2 ++ laE6 ++ laE6) ∈ _
    rw [wordW_append, wordW_append, wordW_append]
    exact mul_mem (mul_mem (mul_mem h1 h2) h1) h1
  · show wordW Tag.E6 (laE6 ++ laE6 ++ e6L2AB2 ++ laE6) ∈ _
    rw [wordW_append, wordW_append, wordW_append]
    exact mul_mem (mul_mem (mul_mem h1 h1) h2) h1

end WeylAB2

theorem e6Z_ab2_tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ e : Fin 4 → ℤ,
    (1 - R6 e6XAB2).mulVec e = (1 - R6 (e6ZsAB2 i)).mulVec
      (((a : ℕ) : ℤ) • ![-1, 0, -1, 1] + ((b : ℕ) : ℤ) • ![-1, 0, -1, -1]) := by
  have hY : ∀ i, R6 (e6ZsAB2 i) = E6R6.zsAB2 i := by
    intro i
    fin_cases i
    exacts [E6R6.r6_la2, E6R6.r6_L2AB2, E6R6.r6_zsAB2_2, E6R6.r6_zsAB2_3]
  simp only [E6R6.r6_XAB2, hY]
  intro a b
  fin_cases a <;> fin_cases b
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨1, ![1, -1, 1, 0], by decide +kernel⟩
  · exact ⟨1, ![2, -2, 2, 0], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 1, 0], by decide +kernel⟩
  · exact ⟨2, ![0, -2, -2, 2], by decide +kernel⟩
  · exact ⟨3, ![-3, -3, 1, -1], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 2, 0], by decide +kernel⟩
  · exact ⟨3, ![1, 1, -3, 3], by decide +kernel⟩
  · exact ⟨2, ![0, -4, -4, 4], by decide +kernel⟩

theorem e6Z_ab2_D :
    ((1 - R6 e6XAB2) * !![-1, 0, 0, -1; -2, 0, 1, -4; -2, 1, 0, 2; 1, -1, 0, -2] +
      Matrix.vecMulVec ![-1, 0, -1, 1] ![-2, 1, 0, 2] +
      Matrix.vecMulVec ![-1, 0, -1, -1] ![-2, 0, 0, -2] = 1) ∧
    ((1 - R6 e6XAB2).mulVec ![0, 3, -4, 3] = (3 : ℤ) • ![-1, 0, -1, 1]) ∧
    ((1 - R6 e6XAB2).mulVec ![-2, -5, 0, -1] = (3 : ℤ) • ![-1, 0, -1, -1]) ∧
    ((1 - R6 e6XAB2) * (2 + R6 e6XAB2) = (3 : ℤ) • 1) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((R6 e6XAB2).mulVec ![1, -2, 0, -1]) i - ![1, -2, 0, -1] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((R6 e6XAB2).mulVec ![0, 0, 1, 0]) i - ![0, 0, 1, 0] i) ∧
    (![1, -2, 0, -1] : Fin 4 → ℤ) 0 = 1 ∧ (![0, 0, 1, 0] : Fin 4 → ℤ) 0 = 0 ∧
    (![1, -2, 0, -1] : Fin 4 → ℤ) 2 = 0 ∧ (![0, 0, 1, 0] : Fin 4 → ℤ) 2 = 1 := by
  rw [E6R6.r6_XAB2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem e6Z_ab2_data :
    (∀ i : Fin 4, R6 e6XAB2 * R6 (e6ZsAB2 i) = R6 (e6ZsAB2 i) * R6 e6XAB2) ∧
    ((1 - R6 e6XAB2).mulVec ![0, 0, 1, 0] = (1 - R6 laE6).mulVec ![-1, 0, -1, 1]) ∧
    ((1 - R6 e6XAB2).mulVec ![1, -1, 1, 0] = (1 - R6 e6L2AB2).mulVec ![-1, 0, -1, -1]) ∧
    (R6 e6XAB2 * R6 e6L2AB2 = R6 e6L2AB2 * R6 e6XAB2) := by
  have hY : ∀ i, R6 (e6ZsAB2 i) = E6R6.zsAB2 i := by
    intro i
    fin_cases i
    exacts [E6R6.r6_la2, E6R6.r6_L2AB2, E6R6.r6_zsAB2_2, E6R6.r6_zsAB2_3]
  have hL : R6 e6L2AB2 = E6R6.zsAB2 1 := E6R6.r6_L2AB2
  simp only [E6R6.r6_XAB2, hY, hL, E6R6.r6_la2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem e6Z_ab2_solve : ∀ c : Fin 4 → ℤ, ∃ i : Fin 4, ∃ e : Fin 4 → ℤ,
    (1 - R6 e6XAB2).mulVec e = (1 - R6 (e6ZsAB2 i)).mulVec c := by
  obtain ⟨D1, D2, D3, -, -, -, -, -, -, -⟩ := e6Z_ab2_D
  exact solve_int_fpf (R6 e6XAB2) (fun i => R6 (e6ZsAB2 i)) (e6Z_ab2_data).1 _ _ _ _ _ _ _
    D1 D2 D3 e6Z_ab2_tab

theorem e6Z_ab2_point : ∀ κ : Fin 4 → ℤ, ∃ c d₁ d₂ : Fin 4 → ℤ,
    (1 - R6 e6XAB2).mulVec d₁ = (1 - R6 laE6).mulVec c ∧
    (1 - R6 e6XAB2).mulVec d₂ = (1 - R6 e6L2AB2).mulVec (c - κ) := by
  obtain ⟨D1, -, -, -, -, -, -, -, -, -⟩ := e6Z_ab2_D
  obtain ⟨-, h₁, h₃, hY⟩ := e6Z_ab2_data
  exact pair_point_int _ _ _ _ _ _ _ _ D1 hY _ _ h₁ h₃

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross

end
