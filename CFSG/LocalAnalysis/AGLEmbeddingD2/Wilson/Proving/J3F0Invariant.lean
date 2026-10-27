module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3F0Mat

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving.J3F0

open Matrix
open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction (matS)

theorem key3 (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  revert x; decide

theorem scale_to_one (S : AddSubgroup (Fin 4 → ZMod 3)) (v : Fin 4 → ZMod 3) (hv : v ∈ S)
    (i : Fin 4) (hi : v i ≠ 0) : ∃ y ∈ S, y i = 1 := by
  rcases key3 (v i) with h | h | h
  · exact absurd h hi
  · exact ⟨v, hv, h⟩
  · refine ⟨(2 : ℕ) • v, S.nsmul_mem hv 2, ?_⟩
    rw [Pi.smul_apply, h]; decide

theorem all_of_basis (S : AddSubgroup (Fin 4 → ZMod 3))
    (e0 : (![1, 0, 0, 0] : Fin 4 → ZMod 3) ∈ S) (e1 : (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S)
    (e2 : (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S) (e3 : (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S)
    (w : Fin 4 → ZMod 3) : w ∈ S := by
  have hw : w = ((w 0).val : ℕ) • (![1, 0, 0, 0] : Fin 4 → ZMod 3)
      + ((w 1).val : ℕ) • (![0, 1, 0, 0] : Fin 4 → ZMod 3)
      + ((w 2).val : ℕ) • (![0, 0, 1, 0] : Fin 4 → ZMod 3)
      + ((w 3).val : ℕ) • (![0, 0, 0, 1] : Fin 4 → ZMod 3) := by
    ext k; fin_cases k <;> simp
  rw [hw]
  exact S.add_mem (S.add_mem (S.add_mem (S.nsmul_mem e0 _) (S.nsmul_mem e1 _))
    (S.nsmul_mem e2 _)) (S.nsmul_mem e3 _)

theorem all_of_hyperplane (S : AddSubgroup (Fin 4 → ZMod 3))
    (e1 : (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S) (e2 : (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S)
    (e3 : (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S) (w : Fin 4 → ZMod 3) (h0 : w 0 = 0) :
    w ∈ S := by
  have hw : w = ((w 1).val : ℕ) • (![0, 1, 0, 0] : Fin 4 → ZMod 3)
      + ((w 2).val : ℕ) • (![0, 0, 1, 0] : Fin 4 → ZMod 3)
      + ((w 3).val : ℕ) • (![0, 0, 0, 1] : Fin 4 → ZMod 3) := by
    ext k; fin_cases k <;> simp [h0]
  rw [hw]
  exact S.add_mem (S.add_mem (S.nsmul_mem e1 _) (S.nsmul_mem e2 _)) (S.nsmul_mem e3 _)


theorem e0_of_unit (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (v : Fin 4 → ZMod 3) (hv : v ∈ S) (h0 : v 0 = 1) :
    ((![1, 0, 0, 0]) : Fin 4 → ZMod 3) ∈ S := by
  have h : (![1, 0, 0, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ v) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 2, 0, 1, 0; 1, 1, 1, 1] *ᵥ v) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ v) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 1, 0, 1] *ᵥ v) + (1 : ℕ) • (!![2, 0, 0, 0; 0, 0, 1, 0; 0, 1, 1, 0; 1, 2, 1, 1] *ᵥ v) := by
    ext k; fin_cases k <;> simp [dotProduct, Fin.sum_univ_four, h0] <;>
      reduce_mod_char <;> ring_nf <;> reduce_mod_char
  rw [h]
  exact (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) v hv) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 2, 0, 1, 0; 1, 1, 1, 1] (by decide) v hv) 1)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) v hv) 2)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 1, 0, 1] (by decide) v hv) 1)) (S.nsmul_mem (hS !![2, 0, 0, 0; 0, 0, 1, 0; 0, 1, 1, 0; 1, 2, 1, 1] (by decide) v hv) 1))


theorem e1_of_unit (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (v : Fin 4 → ZMod 3) (hv : v ∈ S) (h0 : v 0 = 1) :
    ((![0, 1, 0, 0]) : Fin 4 → ZMod 3) ∈ S := by
  have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ v) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ v) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] *ᵥ v) + (1 : ℕ) • (!![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 1, 2, 1] *ᵥ v) := by
    ext k; fin_cases k <;> simp [dotProduct, Fin.sum_univ_four, h0] <;>
      reduce_mod_char <;> ring_nf <;> reduce_mod_char
  rw [h]
  exact (S.add_mem (S.add_mem (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) v hv) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) v hv) 2)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] (by decide) v hv) 1)) (S.nsmul_mem (hS !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 1, 2, 1] (by decide) v hv) 1))


theorem e2_of_unit (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (v : Fin 4 → ZMod 3) (hv : v ∈ S) (h0 : v 0 = 1) :
    ((![0, 0, 1, 0]) : Fin 4 → ZMod 3) ∈ S := by
  have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ v) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 2, 0, 1, 0; 1, 1, 1, 1] *ᵥ v) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 1, 0, 1] *ᵥ v) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 2, 0, 0; 1, 0, 2, 0; 1, 2, 1, 1] *ᵥ v) := by
    ext k; fin_cases k <;> simp [dotProduct, Fin.sum_univ_four, h0] <;>
      reduce_mod_char <;> ring_nf <;> reduce_mod_char
  rw [h]
  exact (S.add_mem (S.add_mem (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) v hv) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 2, 0, 1, 0; 1, 1, 1, 1] (by decide) v hv) 1)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 1, 0, 1] (by decide) v hv) 1)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 2, 0, 0; 1, 0, 2, 0; 1, 2, 1, 1] (by decide) v hv) 2))


theorem e3_of_unit (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (v : Fin 4 → ZMod 3) (hv : v ∈ S) (h0 : v 0 = 1) :
    ((![0, 0, 0, 1]) : Fin 4 → ZMod 3) ∈ S := by
  have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ v) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ v) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 2, 0, 1, 0; 1, 1, 1, 1] *ᵥ v) := by
    ext k; fin_cases k <;> simp [dotProduct, Fin.sum_univ_four, h0] <;>
      reduce_mod_char <;> ring_nf <;> reduce_mod_char
  rw [h]
  exact (S.add_mem (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) v hv) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) v hv) 2)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 2, 0, 1, 0; 1, 1, 1, 1] (by decide) v hv) 2))


theorem nf1_0_0 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 0, 0]) := by decide
    rw [h]; exact (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 0, 0] hu) 1)
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 0, 0]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 0, 0]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 0, 0] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 0, 0] hu) 1))
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 0, 0]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 0, 0]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 0, 0] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 0, 0] hu) 2))

theorem nf1_0_1 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 1, 0, 1] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 0, 1]) := by decide
    rw [h]; exact (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 0, 1] hu) 1)
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 0, 1]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 0, 1]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 0, 1] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 0, 1] hu) 1))
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 0, 1]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 0, 1]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 0, 1] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 0, 1] hu) 2))

theorem nf1_0_2 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 1, 0, 2] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 0, 2]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 0, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 0, 2] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 0, 2] hu) 2))
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 0, 2]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 0, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 0, 2] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 0, 2] hu) 1))
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 0, 2]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 0, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 0, 2] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 0, 2] hu) 2))

theorem nf1_1_0 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 1, 1, 0] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 1, 0]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 1, 0]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 1, 0]) := by decide
    rw [h]; exact (S.add_mem (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 1, 0] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 1, 0] hu) 1)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 1, 0] hu) 2))
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 1, 0]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 1, 0]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 1, 0]) := by decide
    rw [h]; exact (S.add_mem (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 1, 0] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 1, 0] hu) 2)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 1, 0] hu) 1))
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 1, 0]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 1, 0]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 1, 0] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 1, 0] hu) 1))

theorem nf1_1_1 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 1, 1, 1] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 1, 1]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 1, 1]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 1, 1]) := by decide
    rw [h]; exact (S.add_mem (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 1, 1] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 1, 1] hu) 2)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 1, 1] hu) 2))
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 1, 1]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 1, 1]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 1, 1] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 1, 1] hu) 1))
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 1, 1]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 1, 1]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 1, 1] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 1, 1] hu) 1))

theorem nf1_1_2 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 1, 1, 2] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 1, 2]) := by decide
    rw [h]; exact (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 1, 2] hu) 2)
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 1, 2]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 1, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 1, 2] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 1, 2] hu) 1))
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 1, 2]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 1, 1, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 1, 2] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 1, 1, 2] hu) 1))

theorem nf1_2_0 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 1, 2, 0] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 2, 0]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] *ᵥ ![0, 1, 2, 0]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 2, 0] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] (by decide) ![0, 1, 2, 0] hu) 2))
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] *ᵥ ![0, 1, 2, 0]) := by decide
    rw [h]; exact (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] (by decide) ![0, 1, 2, 0] hu) 2)
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 2, 0]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] *ᵥ ![0, 1, 2, 0]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 2, 0] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] (by decide) ![0, 1, 2, 0] hu) 1))

theorem nf1_2_1 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 1, 2, 1] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 2, 1]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] *ᵥ ![0, 1, 2, 1]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 2, 1] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] (by decide) ![0, 1, 2, 1] hu) 2))
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 2, 1]) := by decide
    rw [h]; exact (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 2, 1] hu) 2)
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 2, 1]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] *ᵥ ![0, 1, 2, 1]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 2, 1] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] (by decide) ![0, 1, 2, 1] hu) 1))

theorem nf1_2_2 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 1, 2, 2] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 1, 2, 2]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] *ᵥ ![0, 1, 2, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 1, 2, 2] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] (by decide) ![0, 1, 2, 2] hu) 2))
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 2, 2]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] *ᵥ ![0, 1, 2, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 2, 2] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] (by decide) ![0, 1, 2, 2] hu) 1))
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 1, 2, 2]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] *ᵥ ![0, 1, 2, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 1, 2, 2] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1] (by decide) ![0, 1, 2, 2] hu) 1))

theorem nf0_0 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 0, 1, 0]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 0, 1, 0]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 0, 1, 0] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 0, 1, 0] hu) 1))
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 0, 1, 0]) := by decide
    rw [h]; exact (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 0, 1, 0] hu) 1)
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 0, 1, 0]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 0, 1, 0]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 0, 1, 0] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 0, 1, 0] hu) 2))

theorem nf0_1 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 0, 1, 1] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 0, 1, 1]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 0, 1, 1]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 0, 1, 1] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 0, 1, 1] hu) 1))
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 0, 1, 1]) := by decide
    rw [h]; exact (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 0, 1, 1] hu) 1)
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 0, 1, 1]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 0, 1, 1]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 0, 1, 1] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 0, 1, 1] hu) 2))

theorem nf0_2 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (hu : (![0, 0, 1, 2] : Fin 4 → ZMod 3) ∈ S) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (![0, 1, 0, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 0, 1, 2]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 0, 1, 2]) + (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] *ᵥ ![0, 0, 1, 2]) := by decide
    rw [h]; exact (S.add_mem (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 0, 1, 2] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 0, 1, 2] hu) 2)) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1] (by decide) ![0, 0, 1, 2] hu) 1))
  · have h : (![0, 0, 1, 0] : Fin 4 → ZMod 3) = (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 0, 1, 2]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 0, 1, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 0, 1, 2] hu) 2) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 0, 1, 2] hu) 2))
  · have h : (![0, 0, 0, 1] : Fin 4 → ZMod 3) = (1 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] *ᵥ ![0, 0, 1, 2]) + (2 : ℕ) • (!![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] *ᵥ ![0, 0, 1, 2]) := by decide
    rw [h]; exact (S.add_mem (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide) ![0, 0, 1, 2] hu) 1) (S.nsmul_mem (hS !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1] (by decide) ![0, 0, 1, 2] hu) 2))

theorem hyperplane_of_nf1 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (x : Fin 4 → ZMod 3) (hx : x ∈ S) (h0 : x 0 = 0)
    (h1 : x 1 = 1) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  have hxe : x = ![0, 1, x 2, x 3] := by
    ext k; fin_cases k <;> simp [h0, h1]
  rw [hxe] at hx
  rcases key3 (x 2) with hb | hb | hb <;> rcases key3 (x 3) with hc | hc | hc <;>
    rw [hb, hc] at hx <;>
    first
    | exact nf1_0_0 S hS hx | exact nf1_0_1 S hS hx | exact nf1_0_2 S hS hx
    | exact nf1_1_0 S hS hx | exact nf1_1_1 S hS hx | exact nf1_1_2 S hS hx
    | exact nf1_2_0 S hS hx | exact nf1_2_1 S hS hx | exact nf1_2_2 S hS hx

theorem hyperplane_of_nf0 (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (x : Fin 4 → ZMod 3) (hx : x ∈ S) (h0 : x 0 = 0)
    (h1 : x 1 = 0) (h2 : x 2 = 1) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  have hxe : x = ![0, 0, 1, x 3] := by
    ext k; fin_cases k <;> simp [h0, h1, h2]
  rw [hxe] at hx
  rcases key3 (x 3) with hc | hc | hc <;> rw [hc] at hx
  · exact nf0_0 S hS hx
  · exact nf0_1 S hS hx
  · exact nf0_2 S hS hx

theorem hyperplane_of_u (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) (u : Fin 4 → ZMod 3) (hu : u ∈ S) (h0 : u 0 = 0)
    (hn : u 1 ≠ 0 ∨ u 2 ≠ 0) :
    (![0, 1, 0, 0] : Fin 4 → ZMod 3) ∈ S ∧ (![0, 0, 1, 0] : Fin 4 → ZMod 3) ∈ S ∧
      (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
  rcases key3 (u 1) with h1 | h1 | h1
  · have h2 : u 2 ≠ 0 := by
      rcases hn with hn | hn
      · exact absurd h1 hn
      · exact hn
    rcases key3 (u 2) with h2' | h2' | h2'
    · exact absurd h2' h2
    · exact hyperplane_of_nf0 S hS u hu h0 h1 h2'
    · have hy : (2 : ℕ) • u ∈ S := S.nsmul_mem hu 2
      exact hyperplane_of_nf0 S hS _ hy (by rw [Pi.smul_apply, h0]; decide)
        (by rw [Pi.smul_apply, h1]; decide) (by rw [Pi.smul_apply, h2']; decide)
  · exact hyperplane_of_nf1 S hS u hu h0 h1
  · have hy : (2 : ℕ) • u ∈ S := S.nsmul_mem hu 2
    exact hyperplane_of_nf1 S hS _ hy (by rw [Pi.smul_apply, h0]; decide)
      (by rw [Pi.smul_apply, h1]; decide)

end CFSG.AGLEmbeddingD2.Wilson.Proving.J3F0

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Matrix
open CFSG.AGLEmbeddingD2.Wilson.Proving.J3F0

theorem matS_invariant_addSubgroups
    (S : AddSubgroup (Fin 4 → ZMod 3))
    (hS : ∀ M ∈ matS, ∀ v ∈ S, M *ᵥ v ∈ S) :
    (∀ v, v ∈ S ↔ v = 0) ∨ (∀ v, v ∈ S ↔ ∃ t : ZMod 3, v = t • ![0, 0, 0, 1]) ∨
      (∀ v, v ∈ S ↔ v 0 = 0) ∨ (∀ v, v ∈ S) := by
  by_cases hA : ∃ v ∈ S, v 0 ≠ 0
  · right; right; right
    intro w
    obtain ⟨v, hv, hv0⟩ := hA
    obtain ⟨y, hy, hy0⟩ := scale_to_one S v hv 0 hv0
    have e0 := e0_of_unit S hS y hy hy0
    have e1 := (e1_of_unit S hS y hy hy0)
    have e2 := (e2_of_unit S hS y hy hy0)
    have e3 := (e3_of_unit S hS y hy hy0)
    exact all_of_basis S e0 e1 e2 e3 w
  · push Not at hA
    by_cases hB : ∃ v ∈ S, v 1 ≠ 0 ∨ v 2 ≠ 0
    · right; right; left
      intro v
      constructor
      · intro hv; exact hA v hv
      · intro h0
        obtain ⟨u, hu, hn⟩ := hB
        obtain ⟨f1, f2, f3⟩ := hyperplane_of_u S hS u hu (hA u hu) hn
        exact all_of_hyperplane S f1 f2 f3 v h0
    · push Not at hB
      by_cases hC : ∃ v ∈ S, v 3 ≠ 0
      · right; left
        obtain ⟨v, hv, hv3⟩ := hC
        obtain ⟨y, hy, hy3⟩ := scale_to_one S v hv 3 hv3
        have hy0 : y 0 = 0 := hA y hy
        have hy1 : y 1 = 0 := (hB y hy).1
        have hy2 : y 2 = 0 := (hB y hy).2
        have he3 : (![0, 0, 0, 1] : Fin 4 → ZMod 3) ∈ S := by
          have hyv : y = ![0, 0, 0, 1] := by
            funext k; fin_cases k
            · exact hy0
            · exact hy1
            · exact hy2
            · exact hy3
          rw [← hyv]; exact hy
        intro w
        constructor
        · intro hw
          refine ⟨w 3, ?_⟩
          funext k; fin_cases k
          · simp [hA w hw]
          · simp [(hB w hw).1]
          · simp [(hB w hw).2]
          · simp
        · rintro ⟨t, rfl⟩
          obtain ⟨k, rfl⟩ : ∃ k : ℕ, t = (k : ZMod 3) := ⟨t.val, (ZMod.natCast_zmod_val t).symm⟩
          rw [Nat.cast_smul_eq_nsmul]
          exact S.nsmul_mem he3 k
      · push Not at hC
        left
        intro v
        constructor
        · intro hv
          funext k; fin_cases k
          · exact hA v hv
          · exact (hB v hv).1
          · exact (hB v hv).2
          · exact hC v hv
        · rintro rfl
          exact S.zero_mem

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
