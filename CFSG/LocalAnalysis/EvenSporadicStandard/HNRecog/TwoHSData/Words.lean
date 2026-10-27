module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Hmod
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def h1408Perms : List (Equiv.Perm (Fin 1408)) :=
  (List.finRange 7).map h1408GenPerm

theorem h1408Gens_map_tp : h1408Gens.map (tp 1408) = h1408Perms := by
  simp only [h1408Gens, h1408Perms, List.map_map]
  rfl

theorem h1408Gens_length : h1408Gens.length = 7 := by simp [h1408Gens]

theorem genOf_h1408Gens : genOf 1408 h1408Gens = P1408 := by
  unfold genOf P1408
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, Array.mem_toArray, h1408Gens, List.mem_map,
    List.mem_finRange, true_and, Set.mem_range]
  constructor
  · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨j, rfl⟩, rfl⟩

@[expose] noncomputable def elemW (w : List ℕ) : Equiv.Perm (Fin 1408) := wordVal h1408Perms w

theorem elemW_mem (w : List ℕ) : elemW w ∈ P1408 := by
  unfold elemW wordVal
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
  by_cases h : l - 1 < h1408Perms.length
  · rw [List.getD_eq_getElem _ _ h]
    obtain ⟨j, -, hj⟩ := List.mem_map.1 (List.getElem_mem h)
    rw [← hj]
    exact h1408GenPerm_mem_P1408 j
  · rw [List.getD_eq_default _ _ (by omega)]
    exact P1408.one_mem

section Cert


theorem permOK_h1408Gens : ∀ g ∈ h1408Gens, permOK 1408 g = true := by
  have h := h1408PermOK_true
  simp only [h1408PermOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  intro g hg
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
  by_cases hj : j.val < 6
  · exact (h.1.1 ⟨j.val, hj⟩).1
  · have h6 : j.val = 6 := by omega
    rw [h6]
    exact h.1.2

theorem rep_elemW (w : List ℕ) (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 7) :
    Rep 1408 (wordTbl 1408 h1408Gens w) (elemW w) := by
  have := rep_wordTbl'' (n := 1408) (by norm_num) permOK_h1408Gens w
    (by rw [h1408Gens_length]; exact hw)
  rw [h1408Gens_map_tp] at this
  exact this

end Cert

@[expose] noncomputable def elemA : Equiv.Perm (Fin 1408) := elemW wordA

@[expose] noncomputable def elemZ : Equiv.Perm (Fin 1408) := elemW wordZ

@[expose] noncomputable def elemB : Equiv.Perm (Fin 1408) := elemW wordB

@[expose] noncomputable def elemZ₁ : Equiv.Perm (Fin 1408) := elemW wordZ₁

theorem elemA_mem : elemA ∈ P1408 := elemW_mem _
theorem elemZ_mem : elemZ ∈ P1408 := elemW_mem _
theorem elemB_mem : elemB ∈ P1408 := elemW_mem _
theorem elemZ₁_mem : elemZ₁ ∈ P1408 := elemW_mem _

end CFSG.EvenSporadicStandard.HNRecog
