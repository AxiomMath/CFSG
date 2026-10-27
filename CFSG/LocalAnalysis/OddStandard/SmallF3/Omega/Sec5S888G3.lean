module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888G1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartPhi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private def s888V1 : Fin 8 → ZMod 2 := fun i => if (i : ℕ) = 0 ∨ (i : ℕ) = 1 then 1 else 0

private def s888V2 : Fin 8 → ZMod 2 := fun i => if (i : ℕ) = 4 ∨ (i : ℕ) = 5 then 1 else 0

private def s888Sigma : Equiv.Perm (Fin 8) := Equiv.swap 2 4 * Equiv.swap 3 5

private lemma s888V1_even : IsEvenVec s888V1 := by
  unfold IsEvenVec s888V1
  decide +kernel

private lemma s888V2_even : IsEvenVec s888V2 := by
  unfold IsEvenVec s888V2
  decide +kernel

private lemma s888ZVec_even : IsEvenVec heartZVec := by
  unfold IsEvenVec heartZVec
  decide +kernel

private lemma s888V1_first : IsFirstBlockVec s888V1 := by
  unfold IsFirstBlockVec IsEvenVec s888V1
  decide +kernel

private lemma s888V2_second : IsSecondBlockVec s888V2 := by
  unfold IsSecondBlockVec IsEvenVec s888V2
  decide +kernel

private lemma s888Sigma_mem_alt : s888Sigma ∈ alternatingGroup (Fin 8) := by
  unfold s888Sigma
  exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    (Equiv.Perm.swap_isSwap_iff.mpr (by decide))
    (Equiv.Perm.swap_isSwap_iff.mpr (by decide))

private lemma s888_sigma_perm : permVec s888Sigma heartZVec = s888V1 + s888V2 := by
  unfold s888Sigma s888V1 s888V2 heartZVec permVec
  decide +kernel

theorem heart_fuse_data {G : Type} [Group G] {φ : (Fin 8 → ZMod 2) → G} {A : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hAlt : Alt = alternatingGroup (Fin 8) ∨ Alt = ⊤)
    (hd : HeartData φ A (normalizer (A : Set G)) Alt) :
    ∃ m ∈ normalizer (A : Set G), ∃ v₁ v₂ : Fin 8 → ZMod 2,
      IsFirstBlockVec v₁ ∧ IsSecondBlockVec v₂ ∧
      m⁻¹ * φ heartZVec * m = φ v₁ * φ v₂ ∧
      (φ v₁ * φ v₁ = 1 ∧ φ v₁ ≠ 1 ∧ φ v₁ ≠ φ heartZVec) ∧
      (φ v₂ * φ v₂ = 1 ∧ φ v₂ ≠ 1 ∧ φ v₂ ≠ φ heartZVec) := by
  have hσ : s888Sigma ∈ Alt := by
    rcases hAlt with h | h
    · rw [h]; exact s888Sigma_mem_alt
    · rw [h]; exact Subgroup.mem_top s888Sigma
  obtain ⟨h, hh, hhφ⟩ := hd.lift s888Sigma hσ
  have h0 : φ 0 = 1 := by
    have h := hd.add 0 0 sec5b_isEvenVec_zero sec5b_isEvenVec_zero
    rw [add_zero] at h
    exact mul_right_cancel (by rw [← h, one_mul])
  have hsq1 : φ s888V1 * φ s888V1 = 1 := by
    have h := hd.add s888V1 s888V1 s888V1_even s888V1_even
    have hv : s888V1 + s888V1 = 0 := by
      unfold s888V1; decide +kernel
    rw [hv, h0] at h
    exact h.symm
  have hne1 : φ s888V1 ≠ 1 := by
    intro heq
    have heq0 : φ s888V1 = φ 0 := by rw [heq, h0]
    rcases hd.inj s888V1 0 s888V1_even sec5b_isEvenVec_zero heq0 with h | h
    · exact absurd h (by unfold s888V1; decide +kernel)
    · exact absurd h (by unfold s888V1; decide +kernel)
  have hneZ1 : φ s888V1 ≠ φ heartZVec := by
    intro heq
    rcases hd.inj s888V1 heartZVec s888V1_even s888ZVec_even heq with h | h
    · exact absurd h (by unfold heartZVec s888V1; decide +kernel)
    · exact absurd h (by unfold heartZVec s888V1; decide +kernel)
  have hsq2 : φ s888V2 * φ s888V2 = 1 := by
    have h := hd.add s888V2 s888V2 s888V2_even s888V2_even
    have hv : s888V2 + s888V2 = 0 := by
      unfold s888V2; decide +kernel
    rw [hv, h0] at h
    exact h.symm
  have hne2 : φ s888V2 ≠ 1 := by
    intro heq
    have heq0 : φ s888V2 = φ 0 := by rw [heq, h0]
    rcases hd.inj s888V2 0 s888V2_even sec5b_isEvenVec_zero heq0 with h | h
    · exact absurd h (by unfold s888V2; decide +kernel)
    · exact absurd h (by unfold s888V2; decide +kernel)
  have hneZ2 : φ s888V2 ≠ φ heartZVec := by
    intro heq
    rcases hd.inj s888V2 heartZVec s888V2_even s888ZVec_even heq with h | h
    · exact absurd h (by unfold heartZVec s888V2; decide +kernel)
    · exact absurd h (by unfold heartZVec s888V2; decide +kernel)
  refine ⟨h⁻¹, ?_, s888V1, s888V2, s888V1_first, s888V2_second, ?_,
    ⟨hsq1, hne1, hneZ1⟩, ⟨hsq2, hne2, hneZ2⟩⟩
  · exact inv_mem hh
  · calc (h⁻¹)⁻¹ * φ heartZVec * h⁻¹ = h * φ heartZVec * h⁻¹ := by rw [inv_inv]
      _ = φ (permVec s888Sigma heartZVec) := hhφ heartZVec s888ZVec_even
      _ = φ (s888V1 + s888V2) := by rw [s888_sigma_perm]
      _ = φ s888V1 * φ s888V2 := hd.add s888V1 s888V2 s888V1_even s888V2_even

end CFSG.OddStandard.SmallF3.Omega
