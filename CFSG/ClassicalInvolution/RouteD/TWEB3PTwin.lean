module

public import CFSG.ClassicalInvolution.RouteD.TWEB4Twin
public import CFSG.ClassicalInvolution.RouteD.TWEB4V
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Asc77.T7H CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD.TWE.B4
open CFSG.ClassicalInvolution.RouteD.Exotic (fundCorr_odd)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

structure SpinCtx7 (t : StatedLieTag) {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    (Q : QuadraticForm F (ι → F)) (D : UniversalRootDatum (spinGroup Q)) : Prop where
  hodd : Odd (Nat.card F)
  hQ : (polarBilin Q).Nondegenerate
  hrange : (spinAction Q).range = elementaryGroup Q
  perfect : Group.IsPerfect (spinGroup Q)
  hZ : CenterScalar Q
  hV : Module.finrank F (ι → F) = 7
  hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False
  hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q
  hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆
  hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1

section Ctx

variable {p e : ℕ} [Fact p.Prime]


theorem spinCtx_odd_three (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaOdd 3 p e) :
    SpinCtx7 .POmegaOdd (quadOdd 3 (GaloisField p e)) (oddDatum 3 (GaloisField p e)) := by
  have hn3 : 3 ≤ 3 := le_refl 3
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := 3) (e := e) trivial hadm
    (by omega)
  have hnc := CFSG.ClassicalInvolution.Asc77.fund_noncentral_modelUniv (p := p) (e := e)
    (t := .POmegaOdd) (n := 3) trivial hadm (by simp)
  have hc := fundCorr_odd hp2 hq hadm
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  exact ⟨hodd, nondegenerate_polarBilin_quadOdd 3 _ h2, range_spinAction_quadOdd h2 hn3, this,
    centerScalar_quadOdd h2 hn3, hdim, fun F₁ F₂ h => by
      have := CFSG.ClassicalInvolution.Asc77.finrank_eq_eight_of_proj hodd F₁ F₂ h
      omega, hc.1, hperf, hnc⟩

end Ctx

section Twin

variable {p f : ℕ} [Fact p.Prime]


theorem exists_twin_inv_three (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R R' : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 (GaloisField p f))) (hne : R ≠ R')
    {x x' a a' : spinGroup (quadOdd 3 (GaloisField p f))} (hx : x ∈ R)
    (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x')
    (hx'1 : x' ≠ 1) (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadOdd 3 (GaloisField p f))))
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup (quadOdd 3 (GaloisField p f))))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup (quadOdd 3 (GaloisField p f)))) :
    ∃ (FM : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame (quadOdd 3 (GaloisField p f)))
      (g' J₁ : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)),
      R.map (spinAction (quadOdd 3 (GaloisField p f))) = FM.La.range ∧
      R'.map (spinAction (quadOdd 3 (GaloisField p f))) = FM.swap.La.range ∧
      g' = spinAction (quadOdd 3 (GaloisField p f)) (a * a') ∧
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)) ∧ g' * g' = 1 ∧
      (∀ y, (∀ w ∈ FM.span, polar (quadOdd 3 (GaloisField p f)) y w = 0) → g' y = y) ∧
      Module.finrank (GaloisField p f) (negSpace g') = 2 ∧ negSpace g' ≤ FM.span ∧
      J₁ = spinAction (quadOdd 3 (GaloisField p f)) a ∧
      J₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)) ∧
      (∀ y ∈ FM.span, J₁ y ∈ FM.span) ∧ (∀ y ∈ FM.span, J₁ (J₁ y) = -y) ∧
      (∀ y, g' (J₁ y) = J₁ (g' y)) := by
  classical
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 3 p f := ⟨Fact.out, hf1, by norm_num, hp2⟩
  have ctx := spinCtx_odd_three hp2 hq hadm
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p f))) := ctx.perfect
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hdimV : Module.finrank (GaloisField p f) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) = 7 :=
    ctx.hV
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ := exists_twin_frame ctx.hodd
    ctx.hrange ctx.hZ (by omega) ctx.hproj (ctx.hperf R hR) (ctx.hperf R' hR') (ctx.hcorr R hR)
    (ctx.hcorr R' hR') (ctx.hnc R hR) (ctx.hnc R' hR') hne hx hcx hx1 hx' hcx' hx'1 hsame ha ha'
    hsq hsq'
  have hθu : spinAction (quadOdd 3 (GaloisField p f)) (a * a') = twinInv F₁ A A' := by
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

end CFSG.ClassicalInvolution.RouteD.TWE.B3
