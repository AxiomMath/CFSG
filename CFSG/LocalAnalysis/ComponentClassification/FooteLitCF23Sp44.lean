module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Matrix
open scoped commutatorElement

@[expose] def sp44J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) := fromBlocks 0 1 (-1) 0

@[expose] def sp44U : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks 0 !![0, 1; 1, 0] !![0, 1; 1, 0] 0

@[expose] def sp44V : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![0, 1; 0, 0] !![0, 1; 1, 0] !![0, 1; 1, 0] 0

@[expose] def sp44Vi : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks 0 !![0, 1; 1, 0] !![0, 1; 1, 0] !![0, 0; 1, 0]

@[expose] def sp44G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks 1 !![1, 0; 0, 0] !![0, 0; 0, 1] 1

theorem sp44_mat_facts : sp44U * sp44U = 1 ∧ sp44V * sp44Vi = 1 ∧ sp44Vi * sp44V = 1 ∧
    sp44Uᵀ * sp44J * sp44U = sp44J ∧ sp44Vᵀ * sp44J * sp44V = sp44J ∧
    sp44U * sp44V * sp44U * sp44Vi = sp44G ∧ sp44G * sp44G = 1 ∧ sp44G ≠ 1 := by
  decide

@[expose] def sp44GU : GL (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨sp44U, sp44U, sp44_mat_facts.1, sp44_mat_facts.1⟩

@[expose] def sp44GV : GL (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨sp44V, sp44Vi, sp44_mat_facts.2.1, sp44_mat_facts.2.2.1⟩

theorem coe_sp44_comm :
    ((⁅sp44GU, sp44GV⁆ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) = sp44G := by
  rw [commutatorElement_def, ← sp44_mat_facts.2.2.2.2.2.1]
  rfl

variable {K : Type} [Field K] [CharP K 2]

@[expose] def sp44K (ω : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks 1 !![ω, 0; 0, 0] !![0, 0; 0, ω] 1

omit [CharP K 2] in
theorem sp44G_map (f : ZMod 2 →+* K) :
    sp44G.map f = fromBlocks 1 !![1, 0; 0, 0] !![0, 0; 0, 1] 1 := by
  rw [sp44G, fromBlocks_map]
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem sp44K_facts (ω : K) (hω : ω ^ 2 = ω + 1) :
    sp44K ω * sp44K ω = 1 ∧
    (sp44K ω)ᵀ * fromBlocks 0 1 (-1) 0 * sp44K ω = fromBlocks 0 1 (-1) 0 ∧
    (sp44K ω).map (· ^ 2) = sp44K ω * fromBlocks 1 !![1, 0; 0, 0] !![0, 0; 0, 1] 1 := by
  have hn : (-1 : K) = 1 := CharTwo.neg_eq 1
  have hωω : ω + ω = 0 := CharTwo.add_self_eq_zero ω
  refine ⟨?_, ?_, ?_⟩
  · rw [sp44K, fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hωω]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hωω]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  · rw [sp44K, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hn]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  · rw [sp44K, fromBlocks_map, fromBlocks_multiply]
    congr 1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hω, add_comm]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hω]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp

omit [CharP K 2] in
theorem exists_omega_four [CharP K 2] (hK : Nat.card K = 4) : ∃ ω : K, ω ^ 2 = ω + 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨ω, h0, h1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at this
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  have h3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω h0
    rwa [hcard] at this
  refine ⟨ω, ?_⟩
  have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [this, h3, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · have hn : ω ^ 2 = -(ω + 1) := by linear_combination h
    rw [hn, CharTwo.neg_eq]

end CFSG.ComponentClassification.GSThmB.CF23I
