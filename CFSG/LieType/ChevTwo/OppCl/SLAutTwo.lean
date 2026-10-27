module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism

public section

namespace CFSG.LieType.ChevTwo.OppCl

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Two

variable (F : Type) [Field F] [Finite F] [CharP F 2]

noncomputable def psiTwo : StatedProj (StatedSL 2 F) ≃* SL(2, F) :=
  (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 F).trans
      (LinearCover.projectiveSLTwoEquivSL F))

theorem psiTwo_symm_apply (g : SL(2, F)) :
    (psiTwo F).symm g = QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
      (specialLinearGroupEquivStatedSL 2 F g) := by
  rfl


theorem exists_conj_two (α : MulAut (StatedProj (StatedSL 2 F))) :
    ∃ (A : GL (Fin 2) F) (σ : F ≃+* F), ∀ h : StatedSL 2 F, ∃ h' : StatedSL 2 F,
      ((h' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (A : Matrix (Fin 2) (Fin 2) F) * ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map σ *
          ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∧
      α (QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) h) =
        QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) h' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨e, -, he⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, he]
  obtain ⟨-, -, -, -, hex⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.even_SL2_full_automorphism_semilinear_model
      (F := F) e.pos hcard
  obtain ⟨⟨B, σ⟩, hp, -⟩ := hex (MulAut.congr (psiTwo F) α)
  refine ⟨SpecialLinearGroup.toGL B, σ, fun h => ?_⟩
  obtain ⟨ĥ, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective h
  refine ⟨specialLinearGroupEquivStatedSL 2 F
    (B * Matrix.SpecialLinearGroup.map σ.toRingHom ĥ * B⁻¹), ?_, ?_⟩
  · simp [specialLinearGroupEquivStatedSL_coe]
  · have h1 := hp ĥ
    calc α (QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
          (specialLinearGroupEquivStatedSL 2 F ĥ))
        = α ((psiTwo F).symm ĥ) := by rw [psiTwo_symm_apply]
      _ = (psiTwo F).symm (MulAut.congr (psiTwo F) α ĥ) := by simp [MulAut.congr_apply]
      _ = _ := by rw [h1, psiTwo_symm_apply]

end Two

end CFSG.LieType.ChevTwo.OppCl
