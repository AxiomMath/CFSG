module

public import CFSG.ClassicalInvolution.Asc77.AscT7OC

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.Dichotomy QuadraticMap
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Finite F] [FiniteDimensional F V] {X : Type} [Group X] [Finite X]

theorem e_La_neg_one_sq (e : ↥(elementaryGroup Q) →* X) (fr : Frame Q) :
    e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ *
      e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ = 1 := by
  rw [← map_mul]
  have : (⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ *
      ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ : ↥(elementaryGroup Q)) = 1 :=
    Subtype.ext fr.La_neg_one_mul_self
  rw [this, map_one]

theorem La_neg_one_mem_layer (h5 : 5 ≤ Nat.card F) (fr : Frame Q) {A : V ≃ₗ[F] V}
    {S : Subgroup (V ≃ₗ[F] V)} (hS : CplxLayer Q A S)
    (hAK : ∀ B : SL(2, F), A * fr.swap.La B = fr.swap.La B * A) : fr.La (-1) ∈ S := by
  have hF4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨t, ht⟩
  have hSL : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect hF4
  have hperf : fr.swap.La.range ≤ ⁅fr.swap.La.range, fr.swap.La.range⁆ :=
    (Subgroup.isPerfect_iff.mp (Group.IsPerfect.range fr.swap.La)).symm.le
  have hle : fr.swap.La.range ≤ S := hS.perf _
    (by rintro _ ⟨B, rfl⟩; exact Frame.La_mem_orthogonalGroup fr.swap B)
    (fun g hg x => by
      obtain ⟨B, rfl⟩ := hg
      exact (congrArg (fun m : V ≃ₗ[F] V => m x) (hAK B)).symm) hperf
  rw [← Frame.La_swap_neg_one]
  exact hle ⟨-1, rfl⟩

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
