
module

public import CFSG.Fischer.T46Base
import all CFSG.Fischer.T46Base

public import CFSG.Sporadic.Fi22.LocalCert
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Fi22.Native Matrix

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

theorem localCert_parts : uPtsOK = true ∧
    chainOK 693 t46Letters t46Base t46Q t46Base t46Trees 3 = true ∧
    orbitSizes t46Trees = [693, 512, 120, 36, 6] := by
  have h := CFSG.Sporadic.Fi22.local_certificate
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem t46_chain_facts :
    (∀ i < t46Base.size, TreeFacts 693 t46Trees[i]! (levelLetters t46Letters t46Base i)
      (pairG t46gs) t46Base[i]!) ∧
      (∀ i < t46Base.size, ∀ g ∈ t46lvl i,
        idx 693 g t46Base[i]! = t46Base[i]! ↔ g ∈ t46lvl (i + 1)) ∧
      ∀ i ≤ t46Base.size, Nat.card (t46lvl i) =
        ∏ l ∈ Finset.Ico i t46Base.size, t46Trees[l]!.pts.size :=
  chain_facts rep_t46Letters t46_sep localCert_parts.2.1

theorem t46_tree_size {l v : ℕ} (hv : [693, 512, 120, 36, 6][l]? = some v) :
    t46Trees[l]!.pts.size = v := by
  have h2 := congrArg (fun L : List ℕ => L[l]?) localCert_parts.2.2
  simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList] at h2
  rw [hv] at h2
  have hl : l < t46Trees.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h2
    simp at h2
  rw [Array.getElem?_eq_getElem hl] at h2
  simp only [Option.map_some, Option.some.injEq] at h2
  rw [getElem!_pos t46Trees l hl]
  exact h2

theorem card_T46 : Nat.card T46 = 9196830720 := by
  rw [t46_chain_facts.2.2 0 (by rw [t46Base_size]; norm_num), t46Base_size]
  have hs : ∀ l ∈ Finset.Ico 0 5, t46Trees[l]!.pts.size =
      [693, 512, 120, 36, 6].getD l 0 := fun l hl =>
    t46_tree_size (by have := (Finset.mem_Ico.mp hl).2; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

end CFSG.Fischer
