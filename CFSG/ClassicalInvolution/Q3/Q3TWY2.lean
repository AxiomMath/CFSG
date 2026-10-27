module

public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.Q3.Q3TY14
public import CFSG.ClassicalInvolution.RouteD.TWEB3PTwin
public import CFSG.ClassicalInvolution.RouteD.TWEB3PLift
public import CFSG.ClassicalInvolution.Q3.Q3VF4Row
public import CFSG.ClassicalInvolution.RouteD.TWEB4Rec
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Asc77.T7H CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD.TWE.B4 CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TY
open CFSG.ClassicalInvolution.RouteD.TWE.B3 (exists_spin_twin_pair_three)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Twin

theorem exists_twin_inv_three3
    {R R' : Subgroup (spinGroup (quadOdd 3 𝔽₃))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 𝔽₃))
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 𝔽₃)) (hne : R ≠ R')
    {x x' a a' : spinGroup (quadOdd 3 𝔽₃)} (hx : x ∈ R)
    (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x')
    (hx'1 : x' ≠ 1) (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadOdd 3 𝔽₃)))
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup (quadOdd 3 𝔽₃)))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup (quadOdd 3 𝔽₃))) :
    ∃ (FM : OFrame (quadOdd 3 𝔽₃))
      (g' J₁ : (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃] (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃)),
      R.map (spinAction (quadOdd 3 𝔽₃)) = FM.La.range ∧
      R'.map (spinAction (quadOdd 3 𝔽₃)) = FM.swap.La.range ∧
      g' = spinAction (quadOdd 3 𝔽₃) (a * a') ∧
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 𝔽₃) ∧ g' * g' = 1 ∧
      (∀ y, (∀ w ∈ FM.span, polar (quadOdd 3 𝔽₃) y w = 0) → g' y = y) ∧
      Module.finrank 𝔽₃ (negSpace g') = 2 ∧ negSpace g' ≤ FM.span ∧
      J₁ = spinAction (quadOdd 3 𝔽₃) a ∧
      J₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 𝔽₃) ∧
      (∀ y ∈ FM.span, J₁ y ∈ FM.span) ∧ (∀ y ∈ FM.span, J₁ (J₁ y) = -y) ∧
      (∀ y, g' (J₁ y) = J₁ (g' y)) := by
  classical
  have hn3 : 3 ≤ 3 := le_refl 3
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 := ⟨Nat.prime_three, le_rfl, hn3, by norm_num⟩
  have cq := centralQuot3_odd (m := 3) hn3
  have : Group.IsPerfect (spinGroup (quadOdd 3 𝔽₃)) :=
    isPerfect_spinGroup_quadOdd two_ne_zero_gf3 hn3
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hdimV : Module.finrank 𝔽₃ (Fin 3 ⊕ Fin 3 ⊕ Unit → 𝔽₃) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have hY := yData3_odd hn3 hadm
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ := exists_twin_frame3 odd_gf3
    (range_spinAction_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3) (by omega)
    (fun F₁ F₂ h => ModelFacts.TG3.hproj_odd F₁ F₂ h) (cq.map_inj hR hR') (cq.map_mem R hR)
    (cq.map_mem R' hR') (hY.central R hR) (hY.central R' hR') hne hx hcx hx1 hx' hcx' hx'1 hsame
    ha ha' hsq hsq'
  have hθu : spinAction (quadOdd 3 𝔽₃) (a * a') = twinInv F₁ A A' := by
    rw [map_mul, hθa, hθa']
    rfl
  have hdet : LinearEquiv.det (twinInv F₁ A A') = 1 := by
    rw [← hθu]
    exact det_spinAction_eq_one _
  have hii : twinInv F₁ A A' * twinInv F₁ A A' = 1 :=
    LinearEquiv.ext fun v => twinInv_twinInv F₁ hAA hA'A' v
  have hAA' : A * A = -1 := Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using hAA)
  refine ⟨F₁, twinInv F₁ A A', F₁.La A, hF₁, hF₁', hθu.symm, twinInv_mem_orthogonalGroup F₁ A A',
    hii, ?_, finrank_minusSp_twinInv h2 F₁ hAA hA'A' hdet, ?_, hθa.symm,
    F₁.La_mem_orthogonalGroup A, fun y hy => ?_, ?_, ?_⟩
  · intro y hy
    exact twinInv_perp F₁ A A' ((Frame.mem_perp_iff_forall_incl F₁).mpr fun Y => hy _ ⟨Y, rfl⟩)
  · intro y hy
    have : y ∈ eigIn (twinInv F₁ A A') (-1) F₁.span := by
      rw [← minusSp_twinInv_eq h2 F₁]
      exact hy
    exact (mem_eigIn_iff.mp this).1
  · obtain ⟨X, rfl⟩ := hy
    rw [Frame.La_apply_incl]
    exact ⟨_, rfl⟩
  · intro y hy
    have h1 : F₁.La A (F₁.La A y) = F₁.La (-1) y := by
      rw [← LinearEquiv.mul_apply, ← map_mul, hAA']
    rw [h1]
    have hy' : y ∈ negSpace (F₁.La (-1)) := by rw [negSpace_La_neg_one h2]; exact hy
    exact mem_negSpace_iff'.mp hy'
  · intro y
    show F₁.La A (F₁.swap.La A' (F₁.La A y)) = F₁.La A (F₁.La A (F₁.swap.La A' y))
    have := LinearEquiv.congr_fun (F₁.La_comm_La_swap A A') y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
    rw [← this]

end Twin

end CFSG.ClassicalInvolution.Q3.Q3TWY
