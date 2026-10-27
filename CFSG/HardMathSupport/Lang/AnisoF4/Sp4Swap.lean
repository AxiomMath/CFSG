module

public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Graph
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG.LieType.Steinberg CFSG.RankThree.PartTwo.KFacts
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.LieType.Universal.Symplectic.SpExtras
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem coe_inv_sl2Upper_of_char_two (t : F) [CharP F 2] :
    (((sl2Upper t)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Upper, Matrix.adjugate_fin_two, CharTwo.neg_eq]

theorem coe_inv_sl2Lower_of_char_two (t : F) :
    (((sl2Lower t)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Lower, Matrix.adjugate_fin_two, CharTwo.neg_eq]

theorem sp4Graph_longBlock_sl2Upper [Finite F] (t : F) :
    sp4Graph F (longBlock F 2 1 (sl2Upper t)) =
      shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Upper t) := by
  have hL : mat 2 F (longBlock F 2 1 (sl2Upper t)) =
      Matrix.transvection (Sum.inl 1) (Sum.inr 1) t := by
    rw [longBlock_sl2Upper, mat_elt_positiveLong]
  have hS := mat_shortBlock (K := F) (n := 2) (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Upper t)
  apply mat_injective
  rw [hS]
  rw [mat_apply, coe_sp4Graph]
  rw [← mat_apply, hL]
  rw [coe_inv_sl2Upper_of_char_two]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three,
      antiIdx_inl_zero, antiIdx_inl_one, antiIdx_inr_zero, antiIdx_inr_one, antiIdx_symm_zero,
      antiIdx_symm_one, antiIdx_symm_two, antiIdx_symm_three, Matrix.transvection,
      sl2Upper, Sp.blockMat]

theorem sp4Graph_longBlock_sl2Lower [Finite F] (t : F) :
    sp4Graph F (longBlock F 2 1 (sl2Lower t)) =
      shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Lower t) := by
  have hL : mat 2 F (longBlock F 2 1 (sl2Lower t)) =
      Matrix.transvection (Sum.inr 1) (Sum.inl 1) t := by
    rw [longBlock_sl2Lower, mat_elt_negativeLong]
  have hS := mat_shortBlock (K := F) (n := 2) (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Lower t)
  apply mat_injective
  rw [hS]
  rw [mat_apply, coe_sp4Graph]
  rw [← mat_apply, hL]
  rw [coe_inv_sl2Lower_of_char_two]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three,
      antiIdx_inl_zero, antiIdx_inl_one, antiIdx_inr_zero, antiIdx_inr_one, antiIdx_symm_zero,
      antiIdx_symm_one, antiIdx_symm_two, antiIdx_symm_three, Matrix.transvection,
      sl2Lower, Sp.blockMat]

theorem sp4Graph_shortBlock_sl2Upper [Finite F] (t : F) :
    sp4Graph F (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Upper t)) =
      longBlock F 2 1 (sl2Upper (t ^ 2)) := by
  have hL : mat 2 F (longBlock F 2 1 (sl2Upper (t ^ 2))) =
      Matrix.transvection (Sum.inl 1) (Sum.inr 1) (t ^ 2) := by
    rw [longBlock_sl2Upper, mat_elt_positiveLong]
  have hS := mat_shortBlock (K := F) (n := 2) (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Upper t)
  apply mat_injective
  rw [hL]
  rw [mat_apply, coe_sp4Graph]
  rw [← mat_apply, hS]
  rw [coe_inv_sl2Upper_of_char_two]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three,
      antiIdx_inl_zero, antiIdx_inl_one, antiIdx_inr_zero, antiIdx_inr_one, antiIdx_symm_zero,
      antiIdx_symm_one, antiIdx_symm_two, antiIdx_symm_three, Matrix.transvection,
      sl2Upper, Sp.blockMat, pow_two, CharTwo.add_self_eq_zero]

theorem sp4Graph_shortBlock_sl2Lower [Finite F] (t : F) :
    sp4Graph F (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Lower t)) =
      longBlock F 2 1 (sl2Lower (t ^ 2)) := by
  have hL : mat 2 F (longBlock F 2 1 (sl2Lower (t ^ 2))) =
      Matrix.transvection (Sum.inr 1) (Sum.inl 1) (t ^ 2) := by
    rw [longBlock_sl2Lower, mat_elt_negativeLong]
  have hS := mat_shortBlock (K := F) (n := 2) (zero_ne_one : (0 : Fin 2) ≠ 1) (sl2Lower t)
  apply mat_injective
  rw [hL]
  rw [mat_apply, coe_sp4Graph]
  rw [← mat_apply, hS]
  rw [coe_inv_sl2Lower_of_char_two]
  ext p q
  rcases p with i | i <;> rcases q with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three,
      antiIdx_inl_zero, antiIdx_inl_one, antiIdx_inr_zero, antiIdx_inr_one, antiIdx_symm_zero,
      antiIdx_symm_one, antiIdx_symm_two, antiIdx_symm_three, Matrix.transvection,
      sl2Lower, Sp.blockMat, pow_two, CharTwo.add_self_eq_zero]

section Ranges

variable [Finite F]

theorem card_range_of_injective_sl2 {G : Type*} [Group G] (φ : SL(2, F) →* G)
    (h : Function.Injective φ) : Nat.card φ.range = Nat.card SL(2, F) :=
  (Nat.card_congr (MonoidHom.ofInjective h).toEquiv).symm

theorem map_range_le_of_gens {G H : Type*} [Group G] [Group H] (φ : SL(2, F) →* G) (ψ : G →* H)
    (T : Subgroup H)
    (hu : ∀ t, ψ (φ (sl2Upper t)) ∈ T) (hl : ∀ t, ψ (φ (sl2Lower t)) ∈ T) :
    φ.range.map ψ ≤ T := by
  rw [MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_le_iff_le_comap]
  intro A _
  have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
      T.comap (ψ.comp φ) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hu c
    · exact hl c
  exact hle (Sp.mem_closure_sl2 A)

theorem map_sp4Graph_longBlock_range :
    (longBlock F 2 1).range.map (sp4Graph F).toMonoidHom =
      (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range := by
  have hle : (longBlock F 2 1).range.map (sp4Graph F).toMonoidHom ≤
      (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range := by
    refine map_range_le_of_gens _ _ _ (fun t => ?_) (fun t => ?_)
    · exact ⟨sl2Upper t, (sp4Graph_longBlock_sl2Upper t).symm⟩
    · exact ⟨sl2Lower t, (sp4Graph_longBlock_sl2Lower t).symm⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (sp4Graph F).injective,
    card_range_of_injective_sl2 _ (longBlock_injective (K := F) (n := 2) 1),
    card_range_of_injective_sl2 _ (shortBlock_injective (K := F) (zero_ne_one : (0 : Fin 2) ≠ 1))]

theorem map_sp4Graph_shortBlock_range :
    (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (sp4Graph F).toMonoidHom =
      (longBlock F 2 1).range := by
  have hle : (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map (sp4Graph F).toMonoidHom ≤
      (longBlock F 2 1).range := by
    refine map_range_le_of_gens _ _ _ (fun t => ?_) (fun t => ?_)
    · exact ⟨sl2Upper (t ^ 2), (sp4Graph_shortBlock_sl2Upper t).symm⟩
    · exact ⟨sl2Lower (t ^ 2), (sp4Graph_shortBlock_sl2Lower t).symm⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (sp4Graph F).injective,
    card_range_of_injective_sl2 _ (longBlock_injective (K := F) (n := 2) 1),
    card_range_of_injective_sl2 _ (shortBlock_injective (K := F) (zero_ne_one : (0 : Fin 2) ≠ 1))]

end Ranges

section Swap

variable [Finite F]

theorem map_conj_inv_conj {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    (H.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, ⟨x, hx, by simp [mul_assoc]⟩, by simp [mul_assoc]⟩

theorem symplecticBlockStandardPair_swap {X : Type} [Group X] {W U V : Subgroup X}
    (h : SymplecticBlockStandardPair F W U V) : SymplecticBlockStandardPair F W V U := by
  obtain ⟨θ, c, hrange, hker, -, -, hU, hV⟩ := h
  have hθ : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, ← le_bot_iff]
    exact hker.trans (center_statedSp_eq_bot (F := F)).le
  let γe : MulAut (StatedSp 2 F) :=
    (MulAut.conj c).trans ((sp4Graph F).trans (MulAut.conj c⁻¹))
  set γ : StatedSp 2 F →* StatedSp 2 F := γe.toMonoidHom with hγ
  have hγinj : Function.Injective γ := γe.injective
  have hγsurj : Function.Surjective γ := γe.surjective
  have hmapγ : ∀ H : Subgroup (StatedSp 2 F),
      H.map γ = ((H.map (MulAut.conj c).toMonoidHom).map (sp4Graph F).toMonoidHom).map
        (MulAut.conj c⁻¹).toMonoidHom := by
    intro H
    simp only [hγ, Subgroup.map_map]
    rfl
  refine ⟨θ.comp γ, c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hγsurj, Subgroup.map_top, hrange]
  · rw [(MonoidHom.ker_eq_bot_iff (θ.comp γ)).mpr (hθ.comp hγinj)]
    exact bot_le
  · exact hθ.comp (hγinj.comp ((MulAut.conj c⁻¹).injective.comp
      (longBlock_injective (K := F) (n := 2) 1)))
  · exact hθ.comp (hγinj.comp ((MulAut.conj c⁻¹).injective.comp
      (shortBlock_injective (K := F) (zero_ne_one : (0 : Fin 2) ≠ 1))))
  · rw [← Subgroup.map_map, hmapγ, map_conj_inv_conj, map_sp4Graph_longBlock_range, hV]
  · rw [← Subgroup.map_map, hmapγ, map_conj_inv_conj, map_sp4Graph_shortBlock_range, hU]

end Swap

end CFSG.HardMathSupport.Lang.AnisoF4
