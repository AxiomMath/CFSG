module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenInr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
open CFSG.LocalAnalysis.ComponentInitial

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_k4iv_polar_isSimilitude_neg {ρ : V ≃ₗ[ZMod 3] V} (hρ : IsSimilitude Q ρ (-1)) (x y : V) :
    Q.polarBilin (ρ x) (ρ y) = - Q.polarBilin x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar, QuadraticMap.polar, ← ρ.map_add, hρ (x + y), hρ x, hρ y]
  simp only [Units.val_neg, Units.val_one, neg_mul, neg_neg]
  ring

theorem ff_k4iv_simConj_reflOf {ρ : V ≃ₗ[ZMod 3] V} (hρ : IsSimilitude Q ρ (-1))
    (u : V) (hu : Q u ≠ 0) :
    simConj hρ (reflOf Q u hu) =
      reflOf Q (ρ u) (by rw [hρ u]; exact mul_ne_zero (by decide) hu) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [coe_simConj, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    coe_reflOf_apply, coe_reflOf_apply]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]
  congr 1
  rw [hρ u]
  have hadj := ff_k4iv_polar_isSimilitude_neg (Q := Q) hρ u (ρ.symm x)
  rw [LinearEquiv.apply_symm_apply] at hadj
  simp only [← QuadraticMap.polarBilin_apply_apply]
  rw [hadj]
  congr 1
  field_simp
  rw [show ((-1 : (ZMod 3)ˣ) : ZMod 3) = -1 by norm_num]
  ring

theorem ff_k4iv_reflOf_comm {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (huv : Q.polarBilin u v = 0) :
    reflOf Q u hu * reflOf Q v hv = reflOf Q v hv * reflOf Q u hu := by
  have hru : ((reflOf Q v hv : OGroup Q) : V ≃ₗ[ZMod 3] V) u = u := by
    rw [coe_reflOf_apply, QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply, huv,
      zero_div, zero_smul, sub_zero]
  have h := mul_reflOf_mul_inv (reflOf Q v hv) u hu
  have h' : reflOf Q v hv * reflOf Q u hu * (reflOf Q v hv)⁻¹ = reflOf Q u hu := by
    simpa [hru] using h
  have h2 : reflOf Q v hv * reflOf Q u hu = reflOf Q u hu * reflOf Q v hv := by
    calc reflOf Q v hv * reflOf Q u hu
        = reflOf Q v hv * reflOf Q u hu * ((reflOf Q v hv)⁻¹ * reflOf Q v hv) := by group
      _ = (reflOf Q v hv * reflOf Q u hu * (reflOf Q v hv)⁻¹) * reflOf Q v hv := by group
      _ = reflOf Q u hu * reflOf Q v hv := by rw [h']
  exact h2.symm

theorem ff_aux_pair_facts (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    ∃ u₁ u₂ : V, Q u₁ = 1 ∧ Q u₂ = 1 ∧
      Q.polarBilin u₁ u₂ = 0 ∧ Q.polarBilin u₁ ((ρ : V ≃ₗ[ZMod 3] V) u₁) = 0 ∧
      Q.polarBilin u₂ ((ρ : V ≃ₗ[ZMod 3] V) u₂) = 0 ∧
      Q.polarBilin u₁ ((ρ : V ≃ₗ[ZMod 3] V) u₂) = 0 ∧
      Q.polarBilin u₂ ((ρ : V ≃ₗ[ZMod 3] V) u₁) = 0 := by
  haveI : Fact (¬ IsSquare (-1 : ZMod 3)) := ⟨by decide⟩
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 3) (by rw [hdim]; norm_num)
  let T : Module.End (ZMod 3) V := ((ρ : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V)
  have hns : ¬ IsSquare (-1 : ZMod 3) := by decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hd : (-1 : ZMod 3) ≠ 0 := by decide
  have hsquare : T ^ 2 = algebraMap (ZMod 3) (Module.End (ZMod 3) V) (-1) := ff_aux_hsquare hρρ
  have hadj : ∀ x y, Q.polarBilin (T x) y = Q.polarBilin x (T y) := ff_aux_hadj hρ hρρ
  have hQp : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  letI : Field (scalarAlgebra T) := scalarField T (-1) hns hsquare
  letI : Module (scalarAlgebra T) V := evaluationModule T
  haveI : IsScalarTower (ZMod 3) (scalarAlgebra T) V := evaluationScalarTower T
  haveI : Module.Finite (ZMod 3) (scalarAlgebra T) := scalarAlgebra_finite T (-1) hns hsquare
  haveI : Finite (scalarAlgebra T) := Module.finite_of_finite (ZMod 3)
  have hfin := scalar_square_actual_finite_dimension (K := ZMod 3) (V := V) T (-1) hns hsquare
  haveI : Module.Finite (scalarAlgebra T) V := hfin.1
  haveI : CharP (scalarAlgebra T) 3 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 3) (scalarAlgebra T)).injective 3
  let QE : QuadraticForm (scalarAlgebra T) V :=
    actualPositiveQuadratic Q T (-1) hd hns hsquare hadj
  let BE : LinearMap.BilinForm (scalarAlgebra T) V :=
    actualPositiveBilinear Q.polarBilin T (-1) hd hns hsquare hadj
  obtain ⟨-, -, hBE, hQEnd, -, -, -, -, -, -⟩ :=
    positive_nonsquare_centralizer_structure Q hQp T (-1) hd hns hsquare h2 hadj
  have hdimK : Module.finrank (scalarAlgebra T) V = 3 := by rw [hfin.2.2, hdim]
  have hcard : Nat.card (scalarAlgebra T) = 3 ^ 2 := by
    rw [scalarAlgebra_card T (-1) hns hsquare, Nat.card_zmod]
  have hodd : Nat.card (scalarAlgebra T) % 2 = 1 := by rw [hcard]; decide
  have h2K : (2 : scalarAlgebra T) ≠ 0 := by
    intro hc
    exact absurd ((CharP.cast_eq_zero_iff (scalarAlgebra T) 3 2).mp hc) (by decide)
  obtain ⟨u₁, u₂, hq₁, hq₂, horth⟩ := exists_orthonormal_pair QE hQEnd hdimK h2K hodd
  let σ : scalarAlgebra T ≃ₐ[ZMod 3] scalarAlgebra T := conjugation T (-1) hns hsquare
  let tr : scalarAlgebra T → scalarAlgebra T := fun y => y + σ y
  have htr_add : ∀ a b, tr (a + b) = tr a + tr b := by
    intro a b; simp only [tr, map_add]; ring
  have htr_algebraMap : ∀ a : ZMod 3, tr (algebraMap (ZMod 3) (scalarAlgebra T) a) =
      2 * algebraMap (ZMod 3) (scalarAlgebra T) a := by
    intro a
    simp only [tr, σ]
    rw [AlgEquiv.commutes]
    ring
  have htr_gen : tr (generator T) = 0 := by
    simp only [tr, σ]
    rw [conjugation_generator]
    ring
  have htr_mul_gen : ∀ a : ZMod 3,
      tr (algebraMap (ZMod 3) (scalarAlgebra T) a * generator T) = 0 := by
    intro a
    simp only [tr, map_mul]
    rw [AlgEquiv.commutes, conjugation_generator]
    ring
  have htrBE : ∀ x y, tr (BE x y) =
      2 * algebraMap (ZMod 3) (scalarAlgebra T) (Q.polarBilin x y) := by
    intro x y
    rw [actualPositiveBilinear_formula]
    have h1 := htr_add (algebraMap (ZMod 3) (scalarAlgebra T) (Q.polarBilin x y))
      (algebraMap (ZMod 3) (scalarAlgebra T) ((-1)⁻¹ * Q.polarBilin (T x) y) * generator T)
    rw [h1, htr_algebraMap, htr_mul_gen, add_zero]
  have hinj : Function.Injective (algebraMap (ZMod 3) (scalarAlgebra T)) :=
    (algebraMap (ZMod 3) (scalarAlgebra T)).injective
  have hZ3 : ∀ x : ZMod 3, x = 2 * 2 • x := by decide
  have h2eq : (2 : scalarAlgebra T) = algebraMap (ZMod 3) (scalarAlgebra T) 2 :=
    (map_natCast (algebraMap (ZMod 3) (scalarAlgebra T)) 2).symm
  have hthree : (3 : scalarAlgebra T) = 0 := CharP.cast_eq_zero (scalarAlgebra T) 3
  have h4 : (4 : scalarAlgebra T) = 1 := by
    rw [show (4 : scalarAlgebra T) = 3 + 1 by norm_num, hthree, zero_add]
  have h22 : (2 : scalarAlgebra T) * 2 = 1 := by
    rw [show (2 : scalarAlgebra T) * 2 = 4 by norm_num, h4]
  have htr2 : tr (2 : scalarAlgebra T) = 1 := by
    rw [h2eq, htr_algebraMap, ← h2eq, h22]
  have hBEeq : BE = QE.polarBilin := hBE.symm
  have hBEorth : BE u₁ u₂ = 0 := by
    unfold BE
    rw [← hBE]
    exact horth
  have hBEorth_sym : BE u₂ u₁ = 0 := by
    unfold BE
    rw [← hBE, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact horth
  have hBE₁ : BE u₁ u₁ = 2 := by
    unfold BE
    rw [← hBE, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hq₁]
    simp
  have hBE₂ : BE u₂ u₂ = 2 := by
    unfold BE
    rw [← hBE, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hq₂]
    simp
  have hB_tr : ∀ x y, algebraMap (ZMod 3) (scalarAlgebra T) (Q.polarBilin x y) =
      2 * tr (BE x y) := by
    intro x y
    rw [htrBE x y, ← mul_assoc, h22, one_mul]
  have hQ₁ : Q u₁ = 1 := by
    have h := htrBE u₁ u₁
    rw [hBE₁, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, htr2] at h
    apply hinj
    rw [show algebraMap (ZMod 3) (scalarAlgebra T) (Q u₁) =
        2 * algebraMap (ZMod 3) (scalarAlgebra T) (2 • Q u₁) by
      rw [h2eq, ← map_mul]
      congr 1
      exact hZ3 (Q u₁)]
    rw [← h]
    simp
  have hQ₂ : Q u₂ = 1 := by
    have h := htrBE u₂ u₂
    rw [hBE₂, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, htr2] at h
    apply hinj
    rw [show algebraMap (ZMod 3) (scalarAlgebra T) (Q u₂) =
        2 * algebraMap (ZMod 3) (scalarAlgebra T) (2 • Q u₂) by
      rw [h2eq, ← map_mul]
      congr 1
      exact hZ3 (Q u₂)]
    rw [← h]
    simp
  have hB01 : Q.polarBilin u₁ u₂ = 0 := by
    apply hinj
    rw [hB_tr, hBEorth]
    simp [tr]
  have hB02 : Q.polarBilin u₁ ((ρ : V ≃ₗ[ZMod 3] V) u₂) = 0 := by
    have hgen : ((ρ : V ≃ₗ[ZMod 3] V) u₂) = (generator T) • u₂ := by
      rw [evaluation_generator_smul]; rfl
    apply hinj
    rw [hB_tr, hgen]
    rw [show BE u₁ ((generator T) • u₂) = (generator T) * BE u₁ u₂ by
      rw [map_smul]; rfl]
    rw [hBEorth]
    simp [tr]
  have hB03 : Q.polarBilin u₂ ((ρ : V ≃ₗ[ZMod 3] V) u₁) = 0 := by
    have hgen : ((ρ : V ≃ₗ[ZMod 3] V) u₁) = (generator T) • u₁ := by
      rw [evaluation_generator_smul]; rfl
    apply hinj
    rw [hB_tr, hgen]
    rw [show BE u₂ ((generator T) • u₁) = (generator T) * BE u₂ u₁ by
      rw [map_smul]; rfl]
    rw [hBEorth_sym]
    simp [tr]
  have hB04 : Q.polarBilin u₁ ((ρ : V ≃ₗ[ZMod 3] V) u₁) = 0 := by
    have hgen : ((ρ : V ≃ₗ[ZMod 3] V) u₁) = (generator T) • u₁ := by
      rw [evaluation_generator_smul]; rfl
    apply hinj
    rw [hB_tr, hgen]
    rw [show BE u₁ ((generator T) • u₁) = (generator T) * BE u₁ u₁ by
      rw [map_smul]; rfl]
    rw [hBE₁]
    rw [show (generator T) * (2 : scalarAlgebra T) =
        algebraMap (ZMod 3) (scalarAlgebra T) 2 * generator T by rw [h2eq]; ring]
    rw [htr_mul_gen, mul_zero]
    simp
  have hB05 : Q.polarBilin u₂ ((ρ : V ≃ₗ[ZMod 3] V) u₂) = 0 := by
    have hgen : ((ρ : V ≃ₗ[ZMod 3] V) u₂) = (generator T) • u₂ := by
      rw [evaluation_generator_smul]; rfl
    apply hinj
    rw [hB_tr, hgen]
    rw [show BE u₂ ((generator T) • u₂) = (generator T) * BE u₂ u₂ by
      rw [map_smul]; rfl]
    rw [hBE₂]
    rw [show (generator T) * (2 : scalarAlgebra T) =
        algebraMap (ZMod 3) (scalarAlgebra T) 2 * generator T by rw [h2eq]; ring]
    rw [htr_mul_gen, mul_zero]
    simp
  exact ⟨u₁, u₂, hQ₁, hQ₂, hB01, hB04, hB05, hB02, hB03⟩

end CFSG.OddStandard.SmallF3.Omega
