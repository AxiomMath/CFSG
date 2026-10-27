module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.PGroup

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

set_option linter.unusedSectionVars false


variable (K : Type) [Field K] [Finite K]

theorem eq_zero_or_one_of_card_two (hK : Nat.card K = 2) (t : K) : t = 0 ∨ t = 1 := by
  classical
  haveI := Fintype.ofFinite K
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hcard : ({0, 1} : Finset K).card = 2 := Finset.card_pair zero_ne_one
  have hu : ({0, 1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, hc])
  have ht : t ∈ ({0, 1} : Finset K) := by rw [hu]; exact Finset.mem_univ t
  simpa using ht

theorem torusGroup_eq_bot_of_card_two (hK : Nat.card K = 2) : torusGroup Tag.E8 K = ⊥ := by
  refine eq_bot_iff.2 fun t ht => ?_
  have h := torus_pow_card_sub_one K ht
  rw [hK] at h
  simpa using h

theorem centralizer_XS_eq_one_of_card_two (hK : Nat.card K = 2) {c : ModGL Tag.E8 K}
    (hc1 : c ∈ Subgroup.centralizer (XS K : Set (ModGL Tag.E8 K)))
    (hcG : c ∈ adjointGroup Tag.E8 K) : c = 1 := by
  have hcX1 : ∀ x ∈ X1 K, c * x = x * c := fun x hx =>
    ((Subgroup.mem_centralizer_iff.1 hc1) x (X1_le_XS K hx)).symm
  have hT := centralizer_X1_le K hcG hcX1
  rw [torusGroup_eq_bot_of_card_two K hK, bot_sup_eq] at hT
  obtain ⟨ψ₁, ψ₂, h₁, h₂, hcomm, hr₁, hr₂⟩ := exists_splitFrame_E8' K
  have hcr : c ∈ ψ₂.range := by rw [hr₂]; exact hT
  obtain ⟨A, rfl⟩ := hcr
  have hAc : A ∈ Subgroup.center SL(5, K) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply h₂
    rw [map_mul, map_mul]
    have hB : ψ₂ B ∈ X2 K := by
      have : ψ₂ B ∈ ψ₂.range := ⟨B, rfl⟩
      rwa [hr₂] at this
    exact Subgroup.mem_centralizer_iff.1 hc1 (ψ₂ B) (X2_le_XS K hB)
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hAc
  have hr1 : r = 1 := by
    rcases eq_zero_or_one_of_card_two K hK r with h | h
    · exfalso
      rw [h] at hr
      simp at hr
    · exact h
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [← hrA, hr1, map_one]
    simp
  rw [hA1, map_one]

theorem frameNormalizerSolvable_E8_two (hK : Nat.card K = 2) :
    FrameNormalizerSolvable .E8 K (cosetRoots .E8 4 5) := by
  intro P hPG hPN hPX
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := exists_splitFrame_E8 K
  rw [← hrange] at hPN hPX
  refine isSolvable_of_le_normalizer_frame (isQuasisimple_SL (by norm_num))
    (isSolvable_out_SL (by norm_num)) hA hB hcomm (Gh := adjointGroup .E8 K)
    (hrange ▸ rootSpan_le_adjointGroup K _) (fun c hc d hd => ?_) hPG hPN hPX
  rw [hrange] at hc hd
  have hc1 := centralizer_XS_eq_one_of_card_two K hK hc.1 hc.2
  have hd1 := centralizer_XS_eq_one_of_card_two K hK hd.1 hd.2
  rw [hc1, hd1]
  exact Commute.one_left _

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
