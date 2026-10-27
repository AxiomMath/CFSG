module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private def moveC0 : Fin 8 → ZMod 2 := ![1, 1, 1, 1, 0, 0, 0, 0]

private def moveSw (i j : Fin 8) : Equiv.Perm (Fin 8) := Equiv.swap i j

private def moveHi (i : Fin 4) : Fin 8 := ⟨4 + i.1, by have := i.2; omega⟩

private def movePairs : List (Fin 8 → ZMod 2) :=
  (List.finRange 8).flatMap (fun i => (List.finRange 8).filterMap
    (fun j => if i < j then some (Pi.single i 1 + Pi.single j 1) else none))

private def moveInvC : List (Equiv.Perm (Fin 8)) :=
  [1, moveSw 0 1, moveSw 0 2, moveSw 0 3, moveSw 1 2, moveSw 1 3, moveSw 2 3,
    moveSw 0 1 * moveSw 2 3, moveSw 0 2 * moveSw 1 3, moveSw 0 3 * moveSw 1 2]

private def moveInvC' : List (Equiv.Perm (Fin 8)) :=
  [1, moveSw 4 5, moveSw 4 6, moveSw 4 7, moveSw 5 6, moveSw 5 7, moveSw 6 7,
    moveSw 4 5 * moveSw 6 7, moveSw 4 6 * moveSw 5 7, moveSw 4 7 * moveSw 5 6]

private def moveCands1 : List (Equiv.Perm (Fin 8)) :=
  moveInvC.flatMap (fun x => moveInvC'.map (fun y => x * y))

private def moveCands2 : List (Equiv.Perm (Fin 8)) :=
  (List.finRange 4).flatMap fun i0 => (List.finRange 4).flatMap fun i1 =>
    (List.finRange 4).flatMap fun i2 => (List.finRange 4).filterMap fun i3 =>
      if i0 ≠ i1 ∧ i0 ≠ i2 ∧ i0 ≠ i3 ∧ i1 ≠ i2 ∧ i1 ≠ i3 ∧ i2 ≠ i3 then
        some (moveSw 0 (moveHi i0) * moveSw 1 (moveHi i1) * moveSw 2 (moveHi i2) *
          moveSw 3 (moveHi i3)) else none

private theorem moveC0_weight : vecWeight moveC0 = 4 := by
  decide +kernel

private theorem move_pairs_complete :
    ∀ a : Fin 8 → ZMod 2, vecWeight a = 2 → a ∈ movePairs := by
  decide +kernel

private theorem move_std : ∀ a ∈ movePairs, ∀ b ∈ movePairs,
    (vecWeight (a + moveC0) = 2 ∨ vecWeight (a + moveC0) = 6) →
    (vecWeight (b + moveC0) = 2 ∨ vecWeight (b + moveC0) = 6) → a ≠ b →
    ∃ σ ∈ moveCands1 ++ moveCands2, Equiv.Perm.sign σ = 1 ∧ σ * σ = 1 ∧
      (permVec σ moveC0 = moveC0 ∨ permVec σ moveC0 = moveC0 + 1) ∧ permVec σ a = b := by
  decide +kernel

private theorem move_permVec_inv (τ : Equiv.Perm (Fin 8)) (v : Fin 8 → ZMod 2) :
    permVec τ⁻¹ (permVec τ v) = v := by
  rw [← sec5b_permVec_mul, inv_mul_cancel]
  funext i
  rfl

theorem sec5b_heart_move {a b c : Fin 8 → ZMod 2} (hwa : vecWeight a = 2) (hwb : vecWeight b = 2)
    (hwc : vecWeight c = 4) (hac : vecWeight (a + c) = 2 ∨ vecWeight (a + c) = 6)
    (hbc : vecWeight (b + c) = 2 ∨ vecWeight (b + c) = 6) (hab : a ≠ b) :
    ∃ σ ∈ alternatingGroup (Fin 8), σ * σ = 1 ∧
      (permVec σ c = c ∨ permVec σ c = c + 1) ∧ permVec σ a = b := by
  obtain ⟨τ, hτ, hτc⟩ := sec5b_exists_alt (v := c) (w := moveC0) (by rw [hwc, moveC0_weight])
  have ha' : permVec τ a ∈ movePairs :=
    move_pairs_complete _ (by rw [vecWeight_permVec]; exact hwa)
  have hb' : permVec τ b ∈ movePairs :=
    move_pairs_complete _ (by rw [vecWeight_permVec]; exact hwb)
  have hac' : vecWeight (permVec τ a + moveC0) = 2 ∨ vecWeight (permVec τ a + moveC0) = 6 := by
    rw [← hτc, ← sec5b_permVec_add, vecWeight_permVec]; exact hac
  have hbc' : vecWeight (permVec τ b + moveC0) = 2 ∨ vecWeight (permVec τ b + moveC0) = 6 := by
    rw [← hτc, ← sec5b_permVec_add, vecWeight_permVec]; exact hbc
  have hne : permVec τ a ≠ permVec τ b := fun h => hab (by
    have := congrArg (permVec τ⁻¹) h
    rwa [move_permVec_inv, move_permVec_inv] at this)
  obtain ⟨σ₀, hσ₀m, hsign, hsq, hc, hσ₀a⟩ := move_std _ ha' _ hb' hac' hbc' hne
  have hσ₀A : σ₀ ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.mpr hsign
  refine ⟨τ⁻¹ * σ₀ * τ, ?_, ?_, ?_, ?_⟩
  · exact (alternatingGroup (Fin 8)).mul_mem
      ((alternatingGroup (Fin 8)).mul_mem (inv_mem hτ) hσ₀A) hτ
  · calc τ⁻¹ * σ₀ * τ * (τ⁻¹ * σ₀ * τ) = τ⁻¹ * (σ₀ * σ₀) * τ := by group
      _ = 1 := by rw [hsq]; group
  · rw [sec5b_permVec_mul, sec5b_permVec_mul, hτc]
    rcases hc with hc | hc
    · left
      rw [hc, ← hτc, move_permVec_inv]
    · right
      rw [hc, sec5b_permVec_add, sec5b_permVec_one, ← hτc, move_permVec_inv]
  · rw [sec5b_permVec_mul, sec5b_permVec_mul, hσ₀a, move_permVec_inv]

end CFSG.OddStandard.SmallF3.Omega
