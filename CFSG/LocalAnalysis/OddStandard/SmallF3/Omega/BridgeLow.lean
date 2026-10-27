module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCent
import CFSG.Blueprint.SourceClassicalTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal.Spin
open Classical

private lemma neg_one_pow_three : ((-1 : ℤˣ) ^ 3) = -1 := by decide

private lemma one_ne_neg_one_units : (1 : ℤˣ) ≠ -1 := by decide

theorem isOmegaStar_of_lieModel_psp {X : Type} [Group X] (h : LieModel X .PSp 2 3 1) :
    IsOmegaStar X 5 1 := by
  let Q : QuadraticForm (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 3) := quadOdd 2 (ZMod 3)
  have hQ : Q.Nondegenerate := nondegenerate_quadOdd 2 (ZMod 3)
  have hdim : Module.finrank (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 3) = 5 := by simp
  have hs : quadSign Q = 1 := quadSign_quadOdd 2
  have hπ : piOrth Q ∉ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim]
    exact fun hmem => (by decide : ¬ Even (5 : ℕ)) hmem.1
  have hZ : Nat.card (Subgroup.center (omegaGroup hQ)) =
      if piOrth Q ∈ omegaGroup hQ then 2 else 1 := by
    rw [if_neg hπ]
    exact natCard_center_omegaGroup_five hQ hdim
  obtain ⟨e₂⟩ := nonempty_quotient_center_omegaGroup_mulEquiv hQ (by rw [hdim]; norm_num) hZ
  obtain ⟨e₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (t := .PSp) (n := 2) (p := 3) (f := 1)
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num)
      (lieModel_quotient_center_omegaGroup_five hQ hdim))
  exact ⟨Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 3, inferInstance, inferInstance, inferInstance,
    Q, hQ, hdim, hs, ⟨e₁.trans e₂⟩⟩

theorem isOmegaStar_of_lieModel_psl {X : Type} [Group X] (h : LieModel X .PSL 4 3 1) :
    IsOmegaStar X 6 1 := by
  let Q : QuadraticForm (ZMod 3) (Fin 3 ⊕ Fin 3 → ZMod 3) := quadPlus 3 (ZMod 3)
  have hQ : Q.Nondegenerate := nondegenerate_quadPlus 3 (ZMod 3)
  have hdim : Module.finrank (ZMod 3) (Fin 3 ⊕ Fin 3 → ZMod 3) = 6 := by simp
  have hs : quadSign Q = 1 := quadSign_quadPlus 3
  have hπ : piOrth Q ∉ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim]
    intro hmem
    rw [hs] at hmem
    have h6 : (6 / 2 : ℕ) = 3 := by norm_num
    rw [h6, neg_one_pow_three] at hmem
    exact one_ne_neg_one_units hmem.2
  have hZ : Nat.card (Subgroup.center (omegaGroup hQ)) =
      if piOrth Q ∈ omegaGroup hQ then 2 else 1 := by
    rw [if_neg hπ]
    exact natCard_center_omegaGroup_six_plus hQ hdim hs
  obtain ⟨e₂⟩ := nonempty_quotient_center_omegaGroup_mulEquiv hQ (by rw [hdim]; norm_num) hZ
  obtain ⟨e₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (t := .PSL) (n := 4) (p := 3) (f := 1)
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num)
      (lieModel_quotient_center_omegaGroup_six_plus hQ hdim hs))
  exact ⟨Fin 3 ⊕ Fin 3 → ZMod 3, inferInstance, inferInstance, inferInstance,
    Q, hQ, hdim, hs, ⟨e₁.trans e₂⟩⟩

theorem isOmegaStar_of_lieModel_psu {X : Type} [Group X] (h : LieModel X .PSU 4 3 1) :
    IsOmegaStar X 6 (-1) := by
  let Q : QuadraticForm (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3) := quadMinus 3 (ZMod 3) 0 1
  have hirr : ∀ s : ZMod 3, s ^ 2 + 0 * s + 1 ≠ 0 := by decide
  have hQ : Q.Nondegenerate := nondegenerate_quadMinus_of_finite 3 (ZMod 3) hirr
  have hdim : Module.finrank (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3) = 6 := by simp
  have hs : quadSign Q = -1 :=
    quadSign_quadMinus (m := 3) (b := 0) (c := 1) (by norm_num) hirr
  have hπ : piOrth Q ∈ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim]
    refine ⟨by decide, ?_⟩
    rw [hs]
    have h6 : (6 / 2 : ℕ) = 3 := by norm_num
    rw [h6]
    exact neg_one_pow_three.symm
  have hZ : Nat.card (Subgroup.center (omegaGroup hQ)) =
      if piOrth Q ∈ omegaGroup hQ then 2 else 1 := by
    rw [if_pos hπ]
    exact natCard_center_omegaGroup_six_minus hQ hdim hs
  obtain ⟨e₂⟩ := nonempty_quotient_center_omegaGroup_mulEquiv hQ (by rw [hdim]; norm_num) hZ
  obtain ⟨e₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (t := .PSU) (n := 4) (p := 3) (f := 1)
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num)
      (lieModel_quotient_center_omegaGroup_six_minus hQ hdim hs))
  exact ⟨Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3, inferInstance, inferInstance, inferInstance,
    Q, hQ, hdim, hs, ⟨e₁.trans e₂⟩⟩

theorem isOmegaStar_five_iff {X : Type} [Group X] :
    IsOmegaStar X 5 1 ↔ LieModel X .PSp 2 3 1 := by
  refine ⟨fun hX => ?_, fun h => isOmegaStar_of_lieModel_psp h⟩
  let Q : QuadraticForm (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 3) := quadOdd 2 (ZMod 3)
  have hQ : Q.Nondegenerate := nondegenerate_quadOdd 2 (ZMod 3)
  have hdim : Module.finrank (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 3) = 5 := by simp
  have hs : quadSign Q = 1 := quadSign_quadOdd 2
  have hπ : piOrth Q ∉ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim]
    exact fun hmem => (by decide : ¬ Even (5 : ℕ)) hmem.1
  have hZ : Nat.card (Subgroup.center (omegaGroup hQ)) =
      if piOrth Q ∈ omegaGroup hQ then 2 else 1 := by
    rw [if_neg hπ]
    exact natCard_center_omegaGroup_five hQ hdim
  obtain ⟨e₂⟩ := nonempty_quotient_center_omegaGroup_mulEquiv hQ (by rw [hdim]; norm_num) hZ
  obtain ⟨e⟩ := IsOmegaStar.nonempty_equiv hX (by norm_num : 2 ≤ 5) hQ hdim hs
  exact LieModel.of_mulEquiv (e.trans e₂.symm).symm
    (lieModel_quotient_center_omegaGroup_five hQ hdim)

theorem isOmegaStar_six_plus_iff {X : Type} [Group X] :
    IsOmegaStar X 6 1 ↔ LieModel X .PSL 4 3 1 := by
  refine ⟨fun hX => ?_, fun h => isOmegaStar_of_lieModel_psl h⟩
  let Q : QuadraticForm (ZMod 3) (Fin 3 ⊕ Fin 3 → ZMod 3) := quadPlus 3 (ZMod 3)
  have hQ : Q.Nondegenerate := nondegenerate_quadPlus 3 (ZMod 3)
  have hdim : Module.finrank (ZMod 3) (Fin 3 ⊕ Fin 3 → ZMod 3) = 6 := by simp
  have hs : quadSign Q = 1 := quadSign_quadPlus 3
  have hπ : piOrth Q ∉ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim]
    intro hmem
    rw [hs] at hmem
    have h6 : (6 / 2 : ℕ) = 3 := by norm_num
    rw [h6, neg_one_pow_three] at hmem
    exact one_ne_neg_one_units hmem.2
  have hZ : Nat.card (Subgroup.center (omegaGroup hQ)) =
      if piOrth Q ∈ omegaGroup hQ then 2 else 1 := by
    rw [if_neg hπ]
    exact natCard_center_omegaGroup_six_plus hQ hdim hs
  obtain ⟨e₂⟩ := nonempty_quotient_center_omegaGroup_mulEquiv hQ (by rw [hdim]; norm_num) hZ
  obtain ⟨e⟩ := IsOmegaStar.nonempty_equiv hX (by norm_num : 2 ≤ 6) hQ hdim hs
  exact LieModel.of_mulEquiv (e.trans e₂.symm).symm
    (lieModel_quotient_center_omegaGroup_six_plus hQ hdim hs)

theorem isOmegaStar_six_minus_iff {X : Type} [Group X] :
    IsOmegaStar X 6 (-1) ↔ LieModel X .PSU 4 3 1 := by
  refine ⟨fun hX => ?_, fun h => isOmegaStar_of_lieModel_psu h⟩
  let Q : QuadraticForm (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3) := quadMinus 3 (ZMod 3) 0 1
  have hirr : ∀ s : ZMod 3, s ^ 2 + 0 * s + 1 ≠ 0 := by decide
  have hQ : Q.Nondegenerate := nondegenerate_quadMinus_of_finite 3 (ZMod 3) hirr
  have hdim : Module.finrank (ZMod 3) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3) = 6 := by simp
  have hs : quadSign Q = -1 :=
    quadSign_quadMinus (m := 3) (b := 0) (c := 1) (by norm_num) hirr
  have hπ : piOrth Q ∈ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim]
    refine ⟨by decide, ?_⟩
    rw [hs]
    have h6 : (6 / 2 : ℕ) = 3 := by norm_num
    rw [h6]
    exact neg_one_pow_three.symm
  have hZ : Nat.card (Subgroup.center (omegaGroup hQ)) =
      if piOrth Q ∈ omegaGroup hQ then 2 else 1 := by
    rw [if_pos hπ]
    exact natCard_center_omegaGroup_six_minus hQ hdim hs
  obtain ⟨e₂⟩ := nonempty_quotient_center_omegaGroup_mulEquiv hQ (by rw [hdim]; norm_num) hZ
  obtain ⟨e⟩ := IsOmegaStar.nonempty_equiv hX (by norm_num : 2 ≤ 6) hQ hdim hs
  exact LieModel.of_mulEquiv (e.trans e₂.symm).symm
    (lieModel_quotient_center_omegaGroup_six_minus hQ hdim hs)

end CFSG.OddStandard.SmallF3.Omega
