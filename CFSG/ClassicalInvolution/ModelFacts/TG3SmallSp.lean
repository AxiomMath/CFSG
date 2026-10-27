module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Small
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSp
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSpGen
public import CFSG.ClassicalInvolution.ModelFacts.TG3F3
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic Module
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.RankThree.Classical (spForm spForm_apply spEnd)
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul)
open scoped MatrixGroups Matrix

local notation "𝔽₃" => GaloisField 3 1

section Struct

variable {n : ℕ}

theorem sp_twin_gen (hn : 2 ≤ n) {R₁ R₂ : Subgroup (StatedSp n 𝔽₃)} (e₁ : R₁ ≃* SL(2, 𝔽₃))
    (e₂ : R₂ ≃* SL(2, 𝔽₃)) (h₁ : IsLongRootSp2 R₁ (sl2Inv e₁))
    (h₂ : IsLongRootSp2 R₂ (sl2Inv e₂)) (hR : R₁ ≠ R₂)
    (hc : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center (StatedSp n 𝔽₃)) :
    Commutes R₁ R₂ ∧ sl2Inv e₁ ∉ Subgroup.center (StatedSp n 𝔽₃) ∧
      sl2Inv e₂ ∉ Subgroup.center (StatedSp n 𝔽₃) ∧
      ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₁ = sl2Inv e₁ → r₂ * r₂ = sl2Inv e₂ →
        Subgroup.centralizer ({sl2Inv e₁} : Set (StatedSp n 𝔽₃)) ⊔
          Subgroup.centralizer ({r₁ * r₂} : Set (StatedSp n 𝔽₃)) = ⊤ := by
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hsq₁ := sl2Inv_mul_self hodd e₁
  have hsq₂ := sl2Inv_mul_self hodd e₂
  have hζ2 : (sl2Inv e₂ * (sl2Inv e₁)⁻¹) * (sl2Inv e₂ * (sl2Inv e₁)⁻¹) = 1 :=
    mul_self_eq_one_of_mem_center (by omega) hc
  have hζ1 : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ≠ 1 := by
    intro h
    apply hR
    have : sl2Inv e₂ = sl2Inv e₁ := mul_inv_eq_one.mp h
    rw [h₁.eq_longRootGroup h2, h₂.eq_longRootGroup h2, this]
  have hneg := mulVec_eq_neg_of_mem_center (by omega) hc hζ1 hζ2
  have hi : sl2Inv e₂ = (sl2Inv e₂ * (sl2Inv e₁)⁻¹) * sl2Inv e₁ := by group
  have hmat : ∀ v, mat n 𝔽₃ (sl2Inv e₂) *ᵥ v = -(mat n 𝔽₃ (sl2Inv e₁) *ᵥ v) := fun v => by
    conv_lhs => rw [hi, map_mul, ← Matrix.mulVec_mulVec, hneg]
  have hmin : minusSpace (sl2Inv e₂) = fixSpace (sl2Inv e₁) := by
    ext v
    rw [mem_minusSpace, mem_fixSpace, hmat]
    exact neg_inj
  have hP₁ := h₁.isHyperbolicPlane h2
  have hP₂ := h₂.isHyperbolicPlane h2
  have hd₁ := (isHyperbolicPlane_iff.mp hP₁).1
  have hd₂ := (isHyperbolicPlane_iff.mp hP₂).1
  have hndP₁ := (isHyperbolicPlane_iff.mp hP₁).2
  have hndP₂ := (isHyperbolicPlane_iff.mp hP₂).2
  have hcomm : Commutes R₁ R₂ := by
    have hne : minusSpace (sl2Inv e₁) ≠ minusSpace (sl2Inv e₂) := by
      intro h
      apply hR
      rw [h₁.eq_planeGroup h2, h₂.eq_planeGroup h2, h]
    rw [h₁.eq_planeGroup h2, h₂.eq_planeGroup h2]
    refine (commutes_planeGroup_iff h2 hP₁ hP₂ hne).mpr fun u hu v hv => ?_
    have hv' : v ∈ fixSpace (sl2Inv e₁) := hmin ▸ hv
    have h0 := (h₁.mem_fixSpace_iff h2).mp hv' u hu
    rw [form_antisymm v u, h0, neg_zero]
  have hnc₁ : sl2Inv e₁ ∉ Subgroup.center (StatedSp n 𝔽₃) := by
    intro hz
    have hall := mulVec_eq_neg_of_mem_center (by omega) hz (sl2Inv_ne_one hodd e₁) hsq₁
    have htop : minusSpace (sl2Inv e₁) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      exact hall v
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin] at hd₁
    omega
  have hnc₂ : sl2Inv e₂ ∉ Subgroup.center (StatedSp n 𝔽₃) := by
    intro hz
    have hall := mulVec_eq_neg_of_mem_center (by omega) hz (sl2Inv_ne_one hodd e₂) hsq₂
    have htop : minusSpace (sl2Inv e₂) = ⊤ := by
      rw [eq_top_iff]
      intro v _
      exact hall v
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin] at hd₂
    omega
  refine ⟨hcomm, hnc₁, hnc₂, fun r₁ hr₁ r₂ hr₂ hr₁sq hr₂sq => ?_⟩
  have hi₁R : sl2Inv e₁ ∈ R₁ := sl2Inv_mem e₁
  have hr₁i : sl2Inv e₁ * r₁ = r₁ * sl2Inv e₁ := sl2Inv_commute e₁ hr₁
  have hr₂i : sl2Inv e₁ * r₂ = r₂ * sl2Inv e₁ := hcomm _ hi₁R r₂ hr₂
  have hiJ : sl2Inv e₁ * (r₁ * r₂) = (r₁ * r₂) * sl2Inv e₁ := by
    calc sl2Inv e₁ * (r₁ * r₂) = (sl2Inv e₁ * r₁) * r₂ := by group
      _ = (r₁ * sl2Inv e₁) * r₂ := by rw [hr₁i]
      _ = r₁ * (sl2Inv e₁ * r₂) := by group
      _ = r₁ * (r₂ * sl2Inv e₁) := by rw [hr₂i]
      _ = (r₁ * r₂) * sl2Inv e₁ := by group
  have hJJ : (r₁ * r₂) * (r₁ * r₂) = sl2Inv e₁ * sl2Inv e₂ := by
    calc (r₁ * r₂) * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ := by group
      _ = r₁ * (r₁ * r₂) * r₂ := by rw [← hcomm r₁ hr₁ r₂ hr₂]
      _ = (r₁ * r₁) * (r₂ * r₂) := by group
      _ = sl2Inv e₁ * sl2Inv e₂ := by rw [hr₁sq, hr₂sq]
  have hJ : ∀ v, spEnd (r₁ * r₂) (spEnd (r₁ * r₂) v) = -v := by
    intro v
    rw [← Module.End.mul_apply, ← spEnd_mul, hJJ, spEnd_mul, Module.End.mul_apply]
    change (mat n 𝔽₃ (sl2Inv e₁)) *ᵥ ((mat n 𝔽₃ (sl2Inv e₂)) *ᵥ v) = -v
    rw [hmat, Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← map_mul, hsq₁, map_one,
      Matrix.one_mulVec]
  rw [hmin] at hd₂ hndP₂
  have hnd₁ : ∀ v ∈ minusSpace (sl2Inv e₁), (∀ u ∈ minusSpace (sl2Inv e₁),
      spForm n 𝔽₃ v u = 0) → v = 0 := fun v hv h => hndP₁ v hv fun u hu => by
    have h0 := h u hu
    rw [spForm_apply] at h0
    exact h0
  have hnd₂ : ∀ v ∈ fixSpace (sl2Inv e₁), (∀ u ∈ fixSpace (sl2Inv e₁),
      spForm n 𝔽₃ v u = 0) → v = 0 := fun v hv h => hndP₂ v hv fun u hu => by
    have h0 := h u hu
    rw [spForm_apply] at h0
    exact h0
  exact sp_gen h2 mul_self_ne_neg_one_three exists_sq_add_sq_three (sl2Inv e₁) (r₁ * r₂) hsq₁
    hiJ hJ (minusSpace (sl2Inv e₁)) (fixSpace (sl2Inv e₁)) (fun v => by rw [mem_minusSpace]; rfl)
    (fun v => by rw [mem_fixSpace]; rfl) hd₁ hd₂ hnd₁ hnd₂

end Struct

section Model


theorem isLongRootSp2_sl2Inv {n : ℕ} (hadm : StatedLieAdmissible .PSp n 3 1)
    {R : Subgroup (StatedSp n 𝔽₃)}
    (hR : R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n 3 1 Fact.out).D)
    (e : R ≃* SL(2, 𝔽₃)) : IsLongRootSp2 R (sl2Inv e) := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  obtain ⟨i, hi⟩ := (fund_iff_isLongRootSp2 hadm h2 R).mp hR
  have hie : i = sl2Inv e :=
    eq_sl2Inv_of_orderOf_eq_two odd_natCard_galoisField_three e
      ((hi.isClassicalSL2 h2).mem) ((hi.isClassicalSL2 h2).orderOf_eq_two)
  rw [← hie]
  exact hi

theorem compGen3Twin_psp_two (hadm : StatedLieAdmissible .PSp 2 3 1) :
    CompGen3Twin (compModel 3 1 .PSp 2) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hfin : Finite (compModel 3 1 .PSp 2).G :=
    finite_modelUniv (t := .PSp) hp2 Nat.prime_three trivial hadm
  have : Finite (StatedSp 2 𝔽₃) := hfin
  refine compGen3Twin_small_of_gen₂ (G := StatedSp 2 𝔽₃)
    (fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Fact.out).D) ?_ ?_ ?_
  · intro R hR
    exact nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 (t := .PSp) trivial hadm
      (by decide) (by decide) hR
  · intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne hc
    obtain ⟨hcomm, hnc₁, hnc₂, -⟩ := sp_twin_gen (by norm_num) e₁ e₂
      (isLongRootSp2_sl2Inv hadm hR₁ e₁) (isLongRootSp2_sl2Inv hadm hR₂ e₂) hne hc
    exact ⟨hcomm, hnc₁, hnc₂⟩
  · intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne hc r₁ hr₁ r₂ hr₂ hsq₁ hsq₂
    obtain ⟨-, -, -, hgen⟩ := sp_twin_gen (by norm_num) e₁ e₂
      (isLongRootSp2_sl2Inv hadm hR₁ e₁) (isLongRootSp2_sl2Inv hadm hR₂ e₂) hne hc
    exact hgen r₁ hr₁ r₂ hr₂ hsq₁ hsq₂

end Model

end CFSG.ClassicalInvolution.ModelFacts.TG3
