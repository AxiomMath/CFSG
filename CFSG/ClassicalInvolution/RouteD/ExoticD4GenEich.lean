module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Planes
public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.ClassicalInvolution.SmallOrth.PlusFour
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ClassicalInvolution.SmallOrth.Layer
import CFSG.ClassicalInvolution.SmallOrth.PlusFourModel
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Matrix

open Matrix

variable {F : Type} [Field F]

theorem exists_vecMulVec_of_det_eq_zero {Z : Matrix (Fin 2) (Fin 2) F} (hZ : Z ≠ 0)
    (hd : Z.det = 0) :
    ∃ p q : Fin 2 → F, p ≠ 0 ∧ q ≠ 0 ∧ Z = Matrix.vecMulVec p q := by
  rw [Matrix.det_fin_two] at hd
  by_cases h00 : Z 0 0 = 0
  · by_cases h01 : Z 0 1 = 0
    · have h1 : Z 1 0 ≠ 0 ∨ Z 1 1 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hZ
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h00, h01, hcon.1, hcon.2]
      refine ⟨![0, 1], ![Z 1 0, Z 1 1], ?_, ?_, ?_⟩
      · intro h
        have := congrFun h 1
        simp at this
      · intro h
        have h10 := congrFun h 0
        have h11 := congrFun h 1
        simp at h10 h11
        rcases h1 with h | h
        · exact h h10
        · exact h h11
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, h00, h01]
    · have h10 : Z 1 0 = 0 := by
        rw [h00, zero_mul, zero_sub, neg_eq_zero] at hd
        exact (mul_eq_zero.mp hd).resolve_left h01
      refine ⟨![1, Z 1 1 / Z 0 1], ![0, Z 0 1], ?_, ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · intro h
        have := congrFun h 1
        simp at this
        exact h01 this
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, h00, h10]
        field_simp
  · refine ⟨![1, Z 1 0 / Z 0 0], ![Z 0 0, Z 0 1], ?_, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · intro h
      have := congrFun h 0
      simp at this
      exact h00 this
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply]
      · field_simp
      · field_simp
        linear_combination hd

theorem exists_sl2_mulVec_single_zero (u : Fin 2 → F) (hu : u ≠ 0) :
    ∃ s : SL(2, F), (s : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single 0 1 = u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := fun h1 => hu (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![u 0, -(u 1)⁻¹; u 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec_eq_of_ne_zero (u w : Fin 2 → F) (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ s : SL(2, F), (s : Matrix (Fin 2) (Fin 2) F) *ᵥ u = w := by
  obtain ⟨a, ha⟩ := exists_sl2_mulVec_single_zero u hu
  obtain ⟨b, hb⟩ := exists_sl2_mulVec_single_zero w hw
  refine ⟨b * a⁻¹, ?_⟩
  have h1 : ((b * a⁻¹ * a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (b : Matrix (Fin 2) (Fin 2) F) := by rw [inv_mul_cancel_right]
  rw [← ha, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, h1, hb]

theorem exists_sl2_mul_sigma_eq {Z Z' : Matrix (Fin 2) (Fin 2) F} (hZ : Z ≠ 0) (hd : Z.det = 0)
    (hZ' : Z' ≠ 0) (hd' : Z'.det = 0) :
    ∃ A B : SL(2, F), (A : Matrix (Fin 2) (Fin 2) F) * Z *
      sigmaLin (B : Matrix (Fin 2) (Fin 2) F) = Z' := by
  obtain ⟨p, q, hp, hq, rfl⟩ := exists_vecMulVec_of_det_eq_zero hZ hd
  obtain ⟨p', q', hp', hq', rfl⟩ := exists_vecMulVec_of_det_eq_zero hZ' hd'
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_eq_of_ne_zero p p' hp hp'
  obtain ⟨C, hC⟩ := exists_sl2_mulVec_eq_of_ne_zero q q' hq hq'
  refine ⟨A, ⟨sigmaLin (C : Matrix (Fin 2) (Fin 2) F)ᵀ, ?_⟩, ?_⟩
  · rw [det_sigmaLin, Matrix.det_transpose]
    exact C.2
  · show (A : Matrix (Fin 2) (Fin 2) F) * Matrix.vecMulVec p q *
      sigmaLin (sigmaLin (C : Matrix (Fin 2) (Fin 2) F)ᵀ) = _
    rw [sigmaLin_sigmaLin, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
      hA, hC]

end Matrix

section Frames

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem eichler_swap' {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    eichler Q u w = eichler Q w (-u) :=
  CFSG.ClassicalGroups.Orthogonal.Small.eichler_swap hu hw huw

@[expose] noncomputable def omegaGrp (fr : OFrame Q) : Subgroup (V ≃ₗ[F] V) :=
  fr.La.range ⊔ fr.swap.La.range

theorem La_mem_omegaGrp (fr : OFrame Q) (A : SL(2, F)) : fr.La A ∈ omegaGrp fr :=
  Subgroup.mem_sup_left ⟨A, rfl⟩

theorem swapLa_mem_omegaGrp (fr : OFrame Q) (A : SL(2, F)) : fr.swap.La A ∈ omegaGrp fr :=
  Subgroup.mem_sup_right ⟨A, rfl⟩

theorem omegaGrp_le_orthogonalGroup (fr : OFrame Q) :
    omegaGrp fr ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    exact fr.La_mem_orthogonalGroup A
  · rintro _ ⟨A, rfl⟩
    exact fr.swap.La_mem_orthogonalGroup A

theorem swapLa_incl' (fr : OFrame Q) (A : SL(2, F)) (Y : Matrix (Fin 2) (Fin 2) F) :
    fr.swap.La A (fr.incl Y) = fr.incl (Y * sigmaLin (A : Matrix (Fin 2) (Fin 2) F)) := by
  rw [Frame.La_swap_apply, Frame.embLin_apply, Frame.coords_incl, ← map_add]
  simp only [LinearMap.mulRight_apply]
  congr 1
  abel

theorem mul_apply_incl (fr : OFrame Q) (A B : SL(2, F)) (Z : Matrix (Fin 2) (Fin 2) F) :
    (fr.La A * fr.swap.La B) (fr.incl Z) =
      fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * Z * sigmaLin (B : Matrix (Fin 2) (Fin 2) F)) := by
  rw [LinearEquiv.mul_apply, swapLa_incl', Frame.La_apply_incl, Matrix.mul_assoc]

theorem e₁_eq_incl' (fr : OFrame Q) : fr.e₁ = fr.incl !![1, 0; 0, 0] := by
  simp [Frame.incl_apply]

theorem e₁_ne_zero (fr : OFrame Q) : fr.e₁ ≠ 0 := by
  intro h
  have := fr.polar_e₁_f₁
  rw [h, polar_zero_left] at this
  exact zero_ne_one this

theorem exists_mul_apply_eq (fr : OFrame Q) {u u' : V} (hu : u ∈ fr.span) (hu' : u' ∈ fr.span)
    (hu0 : u ≠ 0) (hu0' : u' ≠ 0) (hQ : Q u = 0) (hQ' : Q u' = 0) :
    ∃ A B : SL(2, F), (fr.La A * fr.swap.La B : V ≃ₗ[F] V) u = u' := by
  have hZ : fr.coords u ≠ 0 := fun h => hu0 (by rw [fr.mem_span_iff.mp hu, h, map_zero])
  have hZ' : fr.coords u' ≠ 0 := fun h => hu0' (by rw [fr.mem_span_iff.mp hu', h, map_zero])
  have hd : (fr.coords u).det = 0 := by
    rw [← fr.Q_incl, ← fr.mem_span_iff.mp hu]
    exact hQ
  have hd' : (fr.coords u').det = 0 := by
    rw [← fr.Q_incl, ← fr.mem_span_iff.mp hu']
    exact hQ'
  obtain ⟨A, B, h⟩ := exists_sl2_mul_sigma_eq hZ hd hZ' hd'
  refine ⟨A, B, ?_⟩
  rw [fr.mem_span_iff.mp hu, mul_apply_incl, h]
  exact (fr.mem_span_iff.mp hu').symm

theorem eichler_e₁_smul_e₂_mem (fr : OFrame Q) (c : F) :
    eichler Q fr.e₁ (c • fr.e₂) ∈ omegaGrp fr := by
  have h1 : Q (c • fr.e₂) = 0 := by rw [map_smul_eq_sq, fr.Q_e₂, mul_zero]
  have h2 : polar Q fr.e₁ (c • fr.e₂) = 0 := by
    rw [polar_smul_right_eq, fr.polar_e₁_e₂, mul_zero]
  rw [eichler_swap' fr.Q_e₁ h1 h2, eichler_smul_left, smul_neg, ← neg_smul,
    ← Frame.La_transvection_zero_one]
  exact La_mem_omegaGrp fr _

theorem eichler_e₁_smul_f₂_mem (fr : OFrame Q) (c : F) :
    eichler Q fr.e₁ (c • fr.f₂) ∈ omegaGrp fr := by
  have h1 : Q (c • fr.f₂) = 0 := by rw [map_smul_eq_sq, fr.Q_f₂, mul_zero]
  have h2 : polar Q fr.e₁ (c • fr.f₂) = 0 := by
    rw [polar_smul_right_eq, fr.polar_e₁_f₂, mul_zero]
  rw [eichler_swap' fr.Q_e₁ h1 h2, eichler_smul_left, smul_neg, ← neg_smul]
  have := Frame.La_transvection_zero_one fr.swap (-c)
  exact this ▸ swapLa_mem_omegaGrp fr _

theorem eichler_mem_omegaGrp (fr : OFrame Q) {u w : V} (hu : u ∈ fr.span) (hw : w ∈ fr.span)
    (hQ : Q u = 0) (hp : polar Q u w = 0) : eichler Q u w ∈ omegaGrp fr := by
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact Subgroup.one_mem _
  obtain ⟨A, B, hg⟩ := exists_mul_apply_eq fr hu (Frame.e₁_mem_span fr) hu0 (e₁_ne_zero fr) hQ
    fr.Q_e₁
  set g : V ≃ₗ[F] V := fr.La A * fr.swap.La B with hgdef
  have hgΩ : g ∈ omegaGrp fr :=
    Subgroup.mul_mem _ (La_mem_omegaGrp fr A) (swapLa_mem_omegaGrp fr B)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := omegaGrp_le_orthogonalGroup fr hgΩ
  have key : eichler Q u w = g⁻¹ * eichler Q fr.e₁ (g w) * g := by
    have h := eichler_conj hgO u w
    rw [hg] at h
    rw [← h]
    group
  rw [key]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgΩ) ?_) hgΩ
  have hgw : g w = fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * fr.coords w *
      sigmaLin (B : Matrix (Fin 2) (Fin 2) F)) := by
    conv_lhs => rw [fr.mem_span_iff.mp hw]
    exact mul_apply_incl fr A B _
  set M : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) * fr.coords w *
    sigmaLin (B : Matrix (Fin 2) (Fin 2) F) with hMdef
  have hp1 : polar Q fr.e₁ (g w) = 0 := by
    rw [← hg, polar_map_of_mem hgO]
    exact hp
  have hM11 : M 1 1 = 0 := by
    rw [hgw, Frame.polar_incl_right, e₁_eq_incl', Frame.coords_incl] at hp1
    simpa using hp1
  rw [hgw]
  have hinc : fr.incl M = ((-M 0 1) • fr.e₂ + M 1 0 • fr.f₂) + M 0 0 • fr.e₁ := by
    rw [Frame.incl_apply, hM11]
    simp only [zero_smul, add_zero]
    abel
  have hp2 : polar Q fr.e₁ ((-M 0 1) • fr.e₂) = 0 := by
    rw [polar_smul_right_eq, fr.polar_e₁_e₂, mul_zero]
  have hp3 : polar Q fr.e₁ (M 1 0 • fr.f₂) = 0 := by
    rw [polar_smul_right_eq, fr.polar_e₁_f₂, mul_zero]
  rw [hinc, eichler_add_smul_self fr.Q_e₁, ← eichler_mul hp2 hp3]
  exact Subgroup.mul_mem _ (eichler_e₁_smul_e₂_mem fr _) (eichler_e₁_smul_f₂_mem fr _)

end Frames

end CFSG.ClassicalInvolution.RouteD.Exotic
