module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Local.FrobeniusKernelComplementPartition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {A : Type*} [Group A] {U W : Subgroup A}

private theorem indicator_coe_eq_indicator_sdiff_add_indicator_one
    {V : Subgroup A} (a : A) :
    (V : Set A).indicator (1 : A → ℕ) a
      = ((V : Set A) \ {1}).indicator (1 : A → ℕ) a
        + ({(1 : A)} : Set A).indicator (1 : A → ℕ) a := by
  by_cases h1 : a = 1
  · subst h1
    rw [Set.indicator_of_mem (Subgroup.one_mem V),
      Set.indicator_of_notMem (by simp : (1 : A) ∉ (V : Set A) \ {1}),
      Set.indicator_of_mem (Set.mem_singleton (1 : A))]
    simp
  · rw [Set.indicator_of_notMem (by simpa using h1 : a ∉ ({(1 : A)} : Set A)), add_zero]
    by_cases hmem : a ∈ (V : Set A)
    · rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem (show a ∈ (V : Set A) \ {1} from ⟨hmem, by simpa using h1⟩)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun h => hmem h.1)]

theorem natCard_mul_indicator_one_add_indicator_top [Finite A] (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥) (a : A) :
    Nat.card U * ({(1 : A)} : Set A).indicator (1 : A → ℕ) a
        + ((⊤ : Subgroup A) : Set A).indicator (1 : A → ℕ) a
      = (U : Set A).indicator (1 : A → ℕ) a
        + ∑ᶠ u : U, ((MulAut.conj (u : A)⁻¹ • W : Subgroup A) : Set A).indicator
            (1 : A → ℕ) a := by
  classical
  have _inst := Fintype.ofFinite U
  have key := indicator_add_finsum_indicator_conj_inv_smul hU hUW hC a
  rw [finsum_eq_sum_of_fintype] at key ⊢
  rw [Finset.sum_congr rfl
      (fun u _ => indicator_coe_eq_indicator_sdiff_add_indicator_one (V := _) a),
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    smul_eq_mul, ← add_assoc, key, Set.indicator_of_mem (Subgroup.mem_top a)]
  exact add_comm _ _

theorem natCard_mul_indicator_one_add_one [Finite A] (hU : U.Normal)
    (hUW : Subgroup.IsComplement' U W)
    (hC : ∀ w ∈ W, w ≠ 1 → U ⊓ Subgroup.centralizer {w} = ⊥) (a : A) :
    Nat.card U * ({(1 : A)} : Set A).indicator (1 : A → ℕ) a + 1
      = (U : Set A).indicator (1 : A → ℕ) a
        + ∑ᶠ u : U, ((MulAut.conj (u : A)⁻¹ • W : Subgroup A) : Set A).indicator
            (1 : A → ℕ) a := by
  rw [← natCard_mul_indicator_one_add_indicator_top hU hUW hC a,
    Set.indicator_of_mem (Subgroup.mem_top a), Pi.one_apply]

end CFSG.FeitThompson
