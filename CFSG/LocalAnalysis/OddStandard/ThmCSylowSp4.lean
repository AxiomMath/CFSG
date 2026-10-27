module

public import CFSG.LocalAnalysis.OddStandard.ThmCSylowSL2
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.OddStandard.ThmC.Sylow

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.OddStandard.ThmC.T
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem longBlock_eq_one_of_scalar (k : Fin 2) (A : SL(2, F))
    (h : ((longBlock F 2 k A : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) ∈
      StatedScalars (Fin 2 ⊕ Fin 2) F) : A = 1 := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, j ≠ k := by
    fin_cases k
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  have hmem : ¬ ((Sum.inl j : Fin 2 ⊕ Fin 2) ∈ coords k ∧
      (Sum.inl j : Fin 2 ⊕ Fin 2) ∈ coords k) := by
    rintro ⟨h1, -⟩
    rcases mem_coords.1 h1 with h | h
    · exact hj (Sum.inl_injective h)
    · exact absurd h Sum.inl_ne_inr
  have h1 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) F =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl j) (Sum.inl j)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at h1
  have h2 : ((longBlock F 2 k A : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) (Sum.inl j) (Sum.inl j) =
      1 := by
    have := blockMat_apply_of_not_mem k (A : Matrix (Fin 2) (Fin 2) F) hmem
    rw [← mat_apply, mat_longBlock]
    simpa using this
  rw [h2] at h1
  have hc1 : c = 1 := by
    apply Units.ext
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h1
  rw [hc1, map_one] at hc
  apply longBlock_injective k
  rw [map_one]
  exact Subtype.ext hc.symm

noncomputable def projSp4 (F : Type) [Field F] : StatedSp 2 F →* StatedProj (StatedSp 2 F) :=
  QuotientGroup.mk' _

theorem projSp4_comp_longBlock_injective (k : Fin 2) :
    Function.Injective ((projSp4 F).comp (longBlock F 2 k)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  apply longBlock_eq_one_of_scalar k A
  have h := (QuotientGroup.eq_one_iff _).1 hA
  exact Subgroup.mem_subgroupOf.1 h

theorem false_of_lieModel_psp {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : CFSG.Blueprint.LieModel K .PSp 2 p f) (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
    (by decide) h
  have hch : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
  have hc : ∀ A B : SL(2, F), Commute (longBlock F 2 0 A) (longBlock F 2 1 B) := fun A B =>
    commute_longBlock_longBlock (by decide : (0 : Fin 2) ≠ 1) A B
  exact not_isT_of_commuting_sl2 T hT hch hch
    ((e.symm.toMonoidHom.comp (projSp4 F)).comp (longBlock F 2 0))
    ((e.symm.toMonoidHom.comp (projSp4 F)).comp (longBlock F 2 1))
    (e.symm.injective.comp (projSp4_comp_longBlock_injective 0))
    (e.symm.injective.comp (projSp4_comp_longBlock_injective 1))
    (fun A B => ((hc A B).map (projSp4 F)).map e.symm.toMonoidHom)

end CFSG.OddStandard.ThmC.Sylow
