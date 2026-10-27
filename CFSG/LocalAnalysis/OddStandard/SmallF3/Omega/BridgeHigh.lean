module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeMat
public import CFSG.Blueprint.Catalog
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus nondegenerate_quadOdd
  nondegenerate_quadPlus nondegenerate_quadMinus_of_finite coe_quadOdd coe_quadPlus coe_quadMinus)

private theorem aux_statedOmega_mulEquiv_omegaProj {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 3) (ι → ZMod 3)) (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (ι → ZMod 3))
    (S : (ι → ZMod 3) → ZMod 3) (hS : ⇑Q = S) :
    Nonempty (StatedProj (StatedOmega S) ≃* omegaProj hQ) := by
  obtain ⟨e⟩ := nonempty_statedProj_statedOmega_mulEquiv_omegaProj Q hQ h2
  exact ⟨hS ▸ e⟩

private theorem aux_admissible_odd : StatedLieAdmissible .POmegaOdd 3 3 1 := by
  unfold StatedLieAdmissible; decide

private theorem aux_admissible_plus : StatedLieAdmissible .POmegaPlus 4 3 1 := by
  unfold StatedLieAdmissible; decide

private theorem aux_admissible_minus : StatedLieAdmissible .POmegaMinus 4 3 1 := by
  unfold StatedLieAdmissible; decide

private theorem aux_card_zmod_three : Nat.card (ZMod 3) = 3 ^ 1 := by simp

private theorem aux_irreducible : ∀ s : ZMod 3, s ^ 2 + 0 * s + 1 ≠ 0 := by decide

theorem isOmegaStar_of_lieModel_odd {X : Type} [Group X] (h : LieModel X .POmegaOdd 3 3 1) :
    IsOmegaStar X 7 1 := by
  have h' := LieModel.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0) h
  have hZ : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd 3 (ZMod 3))))
      .POmegaOdd 3 3 1 :=
    ⟨aux_admissible_odd, ZMod 3, inferInstance, inferInstance, aux_card_zmod_three,
      ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h' hZ
  obtain ⟨e₂⟩ := aux_statedOmega_mulEquiv_omegaProj (quadOdd 3 (ZMod 3))
    (nondegenerate_quadOdd 3 (ZMod 3))
    (by rw [Module.finrank_fintype_fun_eq_card]; decide)
    (StatedQuadOdd 3 (ZMod 3)) (coe_quadOdd 3 (ZMod 3))
  exact ⟨Fin 3 ⊕ Fin 3 ⊕ Unit → ZMod 3, inferInstance, inferInstance, inferInstance,
    quadOdd 3 (ZMod 3), nondegenerate_quadOdd 3 (ZMod 3),
    (by rw [Module.finrank_fintype_fun_eq_card]; decide),
    quadSign_quadOdd 3, ⟨e₁.trans e₂⟩⟩

theorem isOmegaStar_of_lieModel_plus {X : Type} [Group X] (h : LieModel X .POmegaPlus 4 3 1) :
    IsOmegaStar X 8 1 := by
  have h' := LieModel.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0) h
  have hZ : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 3))))
      .POmegaPlus 4 3 1 :=
    ⟨aux_admissible_plus, ZMod 3, inferInstance, inferInstance, aux_card_zmod_three,
      ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h' hZ
  obtain ⟨e₂⟩ := aux_statedOmega_mulEquiv_omegaProj (quadPlus 4 (ZMod 3))
    (nondegenerate_quadPlus 4 (ZMod 3))
    (by rw [Module.finrank_fintype_fun_eq_card]; decide)
    (StatedQuadPlus 4 (ZMod 3)) (coe_quadPlus 4 (ZMod 3))
  exact ⟨Fin 4 ⊕ Fin 4 → ZMod 3, inferInstance, inferInstance, inferInstance,
    quadPlus 4 (ZMod 3), nondegenerate_quadPlus 4 (ZMod 3),
    (by rw [Module.finrank_fintype_fun_eq_card]; decide),
    quadSign_quadPlus 4, ⟨e₁.trans e₂⟩⟩

theorem isOmegaStar_of_lieModel_minus {X : Type} [Group X] (h : LieModel X .POmegaMinus 4 3 1) :
    IsOmegaStar X 8 (-1) := by
  have h' := LieModel.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0) h
  have hQ : (quadMinus 4 (ZMod 3) 0 1).Nondegenerate :=
    nondegenerate_quadMinus_of_finite 4 (ZMod 3) aux_irreducible
  have hZ : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus 4 (ZMod 3) 0 1)))
      .POmegaMinus 4 3 1 :=
    ⟨aux_admissible_minus, ZMod 3, inferInstance, inferInstance, aux_card_zmod_three,
      0, 1, aux_irreducible, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h' hZ
  obtain ⟨e₂⟩ := aux_statedOmega_mulEquiv_omegaProj (quadMinus 4 (ZMod 3) 0 1) hQ
    (by rw [Module.finrank_fintype_fun_eq_card]; decide)
    (StatedQuadMinus 4 (ZMod 3) 0 1) (coe_quadMinus 4 (ZMod 3) 0 1)
  exact ⟨Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 3, inferInstance, inferInstance, inferInstance,
    quadMinus 4 (ZMod 3) 0 1, hQ,
    (by rw [Module.finrank_fintype_fun_eq_card]; decide),
    quadSign_quadMinus (m := 4) (by norm_num) aux_irreducible, ⟨e₁.trans e₂⟩⟩

theorem isOmegaStar_seven_iff {X : Type} [Group X] :
    IsOmegaStar X 7 1 ↔ LieModel X .POmegaOdd 3 3 1 := by
  refine ⟨?_, isOmegaStar_of_lieModel_odd⟩
  intro h
  refine Or.inl ⟨by simp [classicalTags], ?_⟩
  refine ⟨aux_admissible_odd, ZMod 3, inferInstance, inferInstance, aux_card_zmod_three, ?_⟩
  obtain ⟨e₁⟩ := h.nonempty_equiv (by norm_num : 2 ≤ 7)
    (nondegenerate_quadOdd 3 (ZMod 3))
    (by rw [Module.finrank_fintype_fun_eq_card]; decide) (quadSign_quadOdd 3)
  obtain ⟨e₂⟩ := aux_statedOmega_mulEquiv_omegaProj (quadOdd 3 (ZMod 3))
    (nondegenerate_quadOdd 3 (ZMod 3))
    (by rw [Module.finrank_fintype_fun_eq_card]; decide)
    (StatedQuadOdd 3 (ZMod 3)) (coe_quadOdd 3 (ZMod 3))
  exact ⟨e₁.trans e₂.symm⟩

theorem isOmegaStar_eight_plus_iff {X : Type} [Group X] :
    IsOmegaStar X 8 1 ↔ LieModel X .POmegaPlus 4 3 1 := by
  refine ⟨?_, isOmegaStar_of_lieModel_plus⟩
  intro h
  refine Or.inl ⟨by simp [classicalTags], ?_⟩
  refine ⟨aux_admissible_plus, ZMod 3, inferInstance, inferInstance, aux_card_zmod_three, ?_⟩
  obtain ⟨e₁⟩ := h.nonempty_equiv (by norm_num : 2 ≤ 8)
    (nondegenerate_quadPlus 4 (ZMod 3))
    (by rw [Module.finrank_fintype_fun_eq_card]; decide) (quadSign_quadPlus 4)
  obtain ⟨e₂⟩ := aux_statedOmega_mulEquiv_omegaProj (quadPlus 4 (ZMod 3))
    (nondegenerate_quadPlus 4 (ZMod 3))
    (by rw [Module.finrank_fintype_fun_eq_card]; decide)
    (StatedQuadPlus 4 (ZMod 3)) (coe_quadPlus 4 (ZMod 3))
  exact ⟨e₁.trans e₂.symm⟩

end CFSG.OddStandard.SmallF3.Omega