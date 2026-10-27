module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Swap
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelBasic
public import Certificates.Certificate399001

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S CFSG.ClassicalInvolution.Generic
open Certificates.AE6Model Certificates.A6h2Swap

@[expose] def ae6SwapC : Fin 3 → List (Fin 8) := ![[], [6], [4]]

theorem ae6SwapC_val : ∀ k : Fin 3, (ae6SwapC k).map Fin.val = swapConj.getD k.val [] := by decide

theorem ae6SwapC_ne : ∀ k : Fin 3, ∀ i ∈ ae6SwapC k, i ≠ ae6Omit k := by decide

theorem swap_words_val : ∀ (k : Fin 3) (s : Fin 2),
    ((ae6KWord ⟨s.val, by omega⟩).map (ae6EdgeSwap k)).map Fin.val =
      (kWords.getD s.val []).map fun i => (swapMap.getD k.val []).getD i 0 := by decide

section Cert


theorem k0Elts_mem : ∀ e ∈ k0Elts (), ∃ e' ∈ ae6ModelK, (e' : Equiv.Perm (Fin 360)) = e := by
  intro e he
  have hK : ∀ i : ℕ, ∃ a' ∈ ae6ModelK, (a' : Equiv.Perm (Fin 360)) = (k0Gens ()).getD i 1 := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : (k0Gens ())[i]? with
    | none => exact ⟨1, one_mem _, rfl⟩
    | some x =>
      obtain ⟨x', hx', hxx⟩ := k0Gens_mem x (List.mem_of_getElem? h)
      exact ⟨x', hx', hxx⟩
  obtain ⟨a, ha, hae⟩ := hK 0
  obtain ⟨b, hb, hbe⟩ := hK 1
  simp only [k0Elts, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, rfl⟩
  · exact ⟨a, ha, hae⟩
  · exact ⟨a⁻¹, inv_mem ha, by simp [hae]⟩
  · exact ⟨b, hb, hbe⟩
  · exact ⟨b⁻¹, inv_mem hb, by simp [hbe]⟩
  · exact ⟨a * b, mul_mem ha hb, by simp [hae, hbe]⟩
  · exact ⟨(a * b)⁻¹, inv_mem (mul_mem ha hb), by simp [hae, hbe]⟩
  · exact ⟨a * a, mul_mem ha ha, by simp [hae]⟩

theorem ae6EdgeSwapMem_of_cert : AE6EdgeSwapMem := by
  intro k
  refine ⟨ae6Word (ae6SwapC k), ae6Word_mem_V k (ae6SwapC_ne k), fun s => ?_⟩
  have h := Certificates.certificate399001
  simp only [swapCheck, List.all_eq_true, List.mem_range] at h
  have hk := h k.val k.2
  have hw : kWords.getD s.val [] ∈ kWords := by
    fin_cases s <;> simp [kWords]
  have hmem := List.mem_of_elem_eq_true (hk _ hw)
  obtain ⟨e', he', hee⟩ := k0Elts_mem _ hmem
  rw [mem_conjSub_iff]
  suffices hy : (ae6Word (ae6SwapC k))⁻¹ * ae6Word ((ae6KWord ⟨s.val, by omega⟩).map (ae6EdgeSwap k)) *
      ae6Word (ae6SwapC k) = e' by
    rw [hy]; exact he'
  apply Subtype.ext
  rw [hee]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_ae6Word, ae6SwapC_val, swap_words_val]

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2
