module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Dec
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24D4Id

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.ClassicalInvolution.Q3.Q3Z CFSG.Timmesfeld

attribute [local instance] CFSG.Sporadic.Fi24.rAction

set_option linter.unusedSectionVars false

namespace TabFi24

noncomputable def ee (i : ℕ) : CFSG.Sporadic.Fi24.J := aE i

section Parts

theorem ee_mem_lvl_two {i : ℕ} (hi : i < 8) : ee i ∈ lvl 2 :=
  mem_lvl_two_of_fix (tf24_parts.2.2.2.1 i hi).2.1 (tf24_parts.2.2.2.1 i hi).2.2

theorem comm_nodes {a b : ℕ} (h : (a, b) ∈ [(0, 2), (0, 3), (2, 3)]) :
    ∀ u ∈ ({ee (2 * a), ee (2 * a + 1)} : Set CFSG.Sporadic.Fi24.J), ∀ v ∈ ({ee (2 * b), ee (2 * b + 1)} : Set CFSG.Sporadic.Fi24.J),
      u * v = v * u := by
  have hc := tf24_parts.2.2.2.2.2.2.2 (a, b) h
  rintro u (rfl | rfl) v (rfl | rfl)
  · exact hc 0 (by norm_num) 0 (by norm_num)
  · exact hc 0 (by norm_num) 1 (by norm_num)
  · exact hc 1 (by norm_num) 0 (by norm_num)
  · exact hc 1 (by norm_num) 1 (by norm_num)

noncomputable def dx (a : Fin 4) : CFSG.Sporadic.Fi24.J := ee (2 * a.val)

noncomputable def dy (a : Fin 4) : CFSG.Sporadic.Fi24.J := ee (2 * a.val + 1)

noncomputable abbrev fiN : Subgroup CFSG.Sporadic.Fi24.J := d4Group dx dy

theorem edgeD4_cases :
    ∀ a b : Fin 4, edgeD 4 a b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 3) := by
  decide

theorem nonadj4_cases : ∀ a b : Fin 4, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a →
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
      (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) := by
  decide

theorem d4_hrel : ∀ a b : Fin 4, edgeD 4 a b →
    RelsHold (edgeSix (dx a) (dy a) (dx b) (dy b)) a2Words := by
  have he := tf24_parts.2.2.2.2.2.2.1
  intro a b h
  rcases edgeD4_cases a b h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact he (0, 1) (by simp)
  · exact he (1, 2) (by simp)
  · exact he (1, 3) (by simp)

theorem d4_hne : ∀ a b : Fin 4, edgeD 4 a b → dx a ≠ 1 := by
  obtain ⟨-, -, -, -, hm0, hm2, -, -⟩ := tf24_parts
  intro a b h
  rcases edgeD4_cases a b h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hm0
  · exact hm2
  · exact hm2

theorem d4_hcomm : ∀ a b : Fin 4, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a →
    ∀ u ∈ ({dx a, dy a} : Set CFSG.Sporadic.Fi24.J), ∀ v ∈ ({dx b, dy b} : Set CFSG.Sporadic.Fi24.J), u * v = v * u := by
  intro a b hab h1 h2
  have c02 := comm_nodes (a := 0) (b := 2) (by simp)
  have c03 := comm_nodes (a := 0) (b := 3) (by simp)
  have c23 := comm_nodes (a := 2) (b := 3) (by simp)
  rcases nonadj4_cases a b hab h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact c02
  · exact fun u hu v hv => (c02 v hv u hu).symm
  · exact c03
  · exact fun u hu v hv => (c03 v hv u hu).symm
  · exact c23
  · exact fun u hu v hv => (c23 v hv u hu).symm

theorem fiN_le_lvl_two : fiN ≤ lvl 2 := by
  refine iSup_le fun a => ?_
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ee_mem_lvl_two (by have := a.2; omega)
  · exact ee_mem_lvl_two (by have := a.2; omega)

end Parts

section Facts

theorem fiN_facts : Nat.card fiN = 4952179814400 ∧ IsSimpleGroup fiN ∧
    (∃ a b : fiN, a * b ≠ b * a) ∧ LeafType 3 fiN := by
  refine d4_recognition dx dy d4_hrel d4_hne d4_hcomm ?_
  have h := Subgroup.card_dvd_of_le fiN_le_lvl_two
  rw [card_lvl_two] at h
  simpa using h

end Facts

end TabFi24

end CFSG.HardMathSupport.Dickson.I271
