module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFiveModel
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.AGLEmbedding.OmegaMinusCent

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover CFSG.ClassicalGroups.Orthogonal
  QuadraticMap Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev MinusSpace (m : ℕ) : Type := (Fin (m - 1) ⊕ Fin (m - 1) → ZMod 2) × (Fin 2 → ZMod 2)

noncomputable abbrev minusForm (m : ℕ) : QuadraticForm (ZMod 2) (MinusSpace m) :=
  quadTail (m - 1) (minusTailForm (ZMod 2) 1 1)

theorem irreducible_minus : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide

theorem omegaMinusModel {L : Type} [Group L] {m : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOmegaMinusTwoIndex m d) (he : Nonempty (L ≃* CatGroup d)) :
    Nonempty (L ≃* elementaryGroup (minusForm m)) := by
  obtain ⟨e⟩ := he
  rcases d with ⟨i, hi⟩
  obtain ⟨q, hqp, hqe, hiq⟩ := hd
  simp only at hiq
  subst hiq
  have hmodel :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hi hqp e
  rw [hqp, hqe] at hmodel
  exact (exists_mulEquiv_zmod_of_lieModel
    (Or.inl ⟨by decide, hmodel⟩ : CFSG.Blueprint.LieModel L .POmegaMinus m 2 1)).2

theorem nondegenerate_minusForm (m : ℕ) : (polarBilin (minusForm m)).Nondegenerate :=
  nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm irreducible_minus)

theorem finrank_minusSpace {m : ℕ} (hm : 1 ≤ m) : finrank (ZMod 2) (MinusSpace m) = 2 * m := by
  change finrank (ZMod 2) ((Fin (m - 1) ⊕ Fin (m - 1) → ZMod 2) × (Fin 2 → ZMod 2)) = 2 * m
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem finrank_le_minusForm {m : ℕ} {T : Submodule (ZMod 2) (MinusSpace m)}
    (hT : ∀ y ∈ T, minusForm m y = 0) : finrank (ZMod 2) T ≤ m - 1 :=
  finrank_le_of_totSing_tail (anisotropic_minusTailForm irreducible_minus) hT

theorem exists_orth_hypPair {m : ℕ} (hm : 3 ≤ m) :
    ∃ P P' : HypPair (minusForm m), P.Orth P' := by
  refine ⟨hypPairT (m - 1) (minusTailForm (ZMod 2) 1 1) ⟨0, by omega⟩,
    hypPairT (m - 1) (minusTailForm (ZMod 2) 1 1) ⟨1, by omega⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [hypPairT, polar_hypVec_hypVec, Fin.ext_iff]

end CFSG.AGLEmbedding.OmegaMinusCent
