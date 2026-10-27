module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Leaf.CaseTwoCore

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false


variable (K : Type) [Field K]

theorem mRoots_ne_sRoots1' {β : Fin Tag.E8.rank → ℤ} (h : β ∈ mRoots) : β ∉ sRoots1 := by
  intro hs
  exact (Finset.mem_filter.1 h).2.2 (Finset.mem_filter.1 hs).2.2

theorem exists_split_Q {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K) :
    ∃ s ∈ X1 K, ∃ w ∈ Qθ Tag.E8 K, q = s * w ∧
      ∀ ν, heisCoord Tag.E8 K w ν ≠ 0 → ν ∈ mRoots := by
  classical
  have hs := heisCoord_spec Tag.E8 K
  let f : (Fin Tag.E8.rank → ℤ) → K := fun ν =>
    if ν ∈ sRoots1 then heisCoord Tag.E8 K q ν else 0
  have hf : ∀ ν, ν ∉ Deg1 Tag.E8 → f ν = 0 := by
    intro ν hν
    simp only [f]
    rw [if_neg]
    intro hsr
    exact hν (mem_Deg1_E8.2 ⟨mem_rootFinset.1 (Finset.mem_filter.1 hsr).1,
      (Finset.mem_filter.1 hsr).2.1⟩)
  obtain ⟨s, hsQ, hsc⟩ := hs.surj f hf
  have hsX1 : s ∈ X1 K := by
    refine mem_X1_of_coord_M_zero K hsQ fun β' hβ' => ?_
    rw [hsc]
    simp only [f]
    rw [if_neg (mRoots_ne_sRoots1' hβ')]
  refine ⟨s, hsX1, s⁻¹ * q, mul_mem (inv_mem hsQ) hq, by group, fun ν hν => ?_⟩
  by_contra hnot
  apply hν
  rw [hs.mul _ (inv_mem hsQ) _ hq, heisCoord_inv hsQ, hsc]
  simp only [Pi.add_apply, Pi.neg_apply, f]
  by_cases hD : ν ∈ Deg1 Tag.E8
  · rcases Deg1_cases hD with h | h
    · exact absurd h hnot
    · rw [if_pos h]
      ring
  · rw [hs.support q hq ν hD, if_neg]
    · ring
    · intro hsr
      exact hD (mem_Deg1_E8.2 ⟨mem_rootFinset.1 (Finset.mem_filter.1 hsr).1,
        (Finset.mem_filter.1 hsr).2.1⟩)

theorem case_one {H B : Subgroup (ModGL Tag.E8 K)} (hBH : B ≤ H) (hBQ : B ≤ Qθ Tag.E8 K)
    (hnot : ¬ B ≤ XS K) : MPart K H := by
  obtain ⟨b, hb, hbX⟩ := SetLike.not_le_iff_exists.1 hnot
  refine ⟨b, hBH hb, hBQ hb, ?_⟩
  by_contra hne
  apply hbX
  refine X1_le_XS K (mem_X1_of_coord_M_zero K (hBQ hb) fun β hβ => ?_)
  by_contra h0
  exact hne ⟨β, hβ, h0⟩

theorem case_two {H : Subgroup (ModGL Tag.E8 K)} (hX : XS K ≤ H) {p : ModGL Tag.E8 K}
    (hp : p ∈ Pθ Tag.E8 K) (hB : conjSub p (Heis.Uneg Tag.E8 K) ≤ H)
    (hnot : ¬ conjSub p (Heis.Uneg Tag.E8 K) ≤ XS K) : MPart K H := by
  classical
  obtain ⟨q, hq, hpq⟩ := exists_conjSub_Pθ_Uneg Tag.E8 K hp
  rw [hpq] at hB hnot
  obtain ⟨s, hsX1, w, hwQ, rfl, hwM⟩ := exists_split_Q K hq
  have hsiH : s⁻¹ ∈ H := inv_mem (hX (X1_le_XS K hsX1))
  have hBw : conjSub w (Heis.Uneg Tag.E8 K) ≤ H := by
    have e : conjSub w (Heis.Uneg Tag.E8 K) =
        conjSub s⁻¹ (conjSub (s * w) (Heis.Uneg Tag.E8 K)) := by
      rw [← conjSub_mul, inv_mul_cancel_left]
    rw [e]
    exact conjSub_le_of_mem_of_le hsiH hB
  by_cases hw0 : ∃ ν, heisCoord Tag.E8 K w ν ≠ 0
  · exact case_two_core K hX hwQ hwM hw0 hBw
  · exfalso
    push Not at hw0
    have hwU : w ∈ Uθ Tag.E8 K := ((heisCoord_spec Tag.E8 K).eq_zero_iff w hwQ).1 (funext hw0)
    apply hnot
    exact conjSub_le_of_mem_of_le (X1_le_XS K (mul_mem hsX1 (Uθ_le_X1 K hwU)))
      ((Uneg_le_X1 K).trans (X1_le_XS K))

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
