module

public import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.LieType.Chevalley.SignCharacterMasks
import CFSG.RankThree.Lattice.SteinbergBIRoots

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

private def e7Mask (S : Finset (Fin Tag.E7.rank)) : ℕ :=
  ∑ i ∈ S, 2 ^ (i : ℕ)

private def e7EvenCount (m : ℕ) : ℕ :=
  (Tag.E7.artifactRoots.filter fun l =>
    decide (Even (maskPairing (fun j => m.testBit (j : ℕ))
      (CFSG.RankThree.Lattice.toVec Tag.E7.rank l)))).length

private def e7EvenCheck (_ : Unit := ()) : Bool :=
  (List.range 128).all fun m => decide (56 ≤ e7EvenCount m)

private theorem e7EvenCheck_true : e7EvenCheck () = true := by
  decide +kernel

private theorem e7EvenCount_ge (m : ℕ) (hm : m < 128) : 56 ≤ e7EvenCount m := by
  have h : (List.range 128).all (fun m => decide (56 ≤ e7EvenCount m)) = true := by
    simpa [e7EvenCheck] using e7EvenCheck_true
  exact of_decide_eq_true ((List.all_eq_true.mp h) m (List.mem_range.mpr hm))

private theorem e7Mask_lt (S : Finset (Fin Tag.E7.rank)) : e7Mask S < 128 := by
  have hsub : S.image (fun i : Fin Tag.E7.rank => (i : ℕ)) ⊆ Finset.range 7 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr i.isLt
  have hsum : e7Mask S =
      ∑ i ∈ S.image (fun i : Fin Tag.E7.rank => (i : ℕ)), 2 ^ i := by
    rw [e7Mask, Finset.sum_image]
    intro x _ y _ hxy
    exact Fin.ext hxy
  rw [hsum]
  calc ∑ i ∈ S.image (fun i : Fin Tag.E7.rank => (i : ℕ)), 2 ^ i
      ≤ ∑ i ∈ Finset.range 7, 2 ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x _ _; positivity)
    _ = 127 := by norm_num
    _ < 128 := by norm_num

private theorem e7Mask_testBit (S : Finset (Fin Tag.E7.rank)) (j : Fin Tag.E7.rank) :
    (e7Mask S).testBit (j : ℕ) = decide (j ∈ S) := by
  have hsum : e7Mask S =
      ∑ i ∈ S.image (fun i : Fin Tag.E7.rank => (i : ℕ)), 2 ^ i := by
    rw [e7Mask, Finset.sum_image]
    intro x _ y _ hxy
    exact Fin.ext hxy
  have hmem : (j : ℕ) ∈
      (∑ i ∈ S.image (fun i : Fin Tag.E7.rank => (i : ℕ)), 2 ^ i).bitIndices ↔ j ∈ S := by
    rw [← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, hji⟩
      simpa [Fin.ext hji] using hi
    · exact fun h => ⟨j, h, rfl⟩
  rw [hsum]
  by_cases h : j ∈ S
  · have hb : (∑ i ∈ S.image (fun i : Fin Tag.E7.rank => (i : ℕ)), 2 ^ i).testBit
        (j : ℕ) = true := Nat.mem_bitIndices.mp (hmem.mpr h)
    simp [h, hb]
  · have hb : (∑ i ∈ S.image (fun i : Fin Tag.E7.rank => (i : ℕ)), 2 ^ i).testBit
        (j : ℕ) = false := by
      by_contra hbot
      exact h (hmem.mp (Nat.mem_bitIndices.mpr (by simpa using hbot)))
    simp [h, hb]

private theorem e7Mask_pairing (S : Finset (Fin Tag.E7.rank))
    (v : Fin Tag.E7.rank → ℤ) :
    maskPairing (fun j => (e7Mask S).testBit (j : ℕ)) v = ∑ i ∈ S, v i := by
  rw [maskPairing, ← Finset.sum_filter]
  congr 1
  ext j
  rw [Finset.mem_filter, e7Mask_testBit]
  simp

theorem e7_even_root_count_ge (S : Finset (Fin Tag.E7.rank)) :
    56 ≤ Nat.card {α : {v : Fin Tag.E7.rank → ℤ // IsRoot .E7 v} // Even (∑ i ∈ S, α.1 i)} := by
  classical
  have hcount := e7EvenCount_ge (e7Mask S) (e7Mask_lt S)
  have hfilter : e7EvenCount (e7Mask S) =
      (Tag.E7.artifactRoots.filter fun l =>
        decide (Even (∑ i ∈ S, CFSG.RankThree.Lattice.toVec Tag.E7.rank l i))).length := by
    unfold e7EvenCount
    congr 1
    apply List.filter_congr
    intro l _
    rw [e7Mask_pairing]
  rw [hfilter] at hcount
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun v => IsRoot .E7 v)
    (fun v => Even (∑ i ∈ S, v i)))]
  change 56 ≤ {γ : Fin Tag.E7.rank → ℤ | IsRoot .E7 γ ∧ Even (∑ i ∈ S, γ i)}.ncard
  rw [CFSG.RankThree.Lattice.ncard_isRoot_and (τ := .E7)
    (P := fun v => Even (∑ i ∈ S, v i))]
  exact hcount

end CFSG.LieType.Chevalley

end
