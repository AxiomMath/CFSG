module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinCtx
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7HS2
public import CFSG.ClassicalInvolution.Asc77.AscT7HS1
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Asc77.T7H
open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]


theorem exists_twin_inv_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {R R' : Subgroup (spinGroup (quadOdd 4 (GaloisField p f)))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 (GaloisField p f)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 (GaloisField p f))) (hne : R ≠ R')
    {x x' a a' : spinGroup (quadOdd 4 (GaloisField p f))} (hx : x ∈ R)
    (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x')
    (hx'1 : x' ≠ 1) (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadOdd 4 (GaloisField p f))))
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup (quadOdd 4 (GaloisField p f))))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup (quadOdd 4 (GaloisField p f)))) :
    ∃ (FM : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame (quadOdd 4 (GaloisField p f)))
      (g' : (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f)),
      R.map (spinAction (quadOdd 4 (GaloisField p f))) = FM.La.range ∧
      R'.map (spinAction (quadOdd 4 (GaloisField p f))) = FM.swap.La.range ∧
      g' = spinAction (quadOdd 4 (GaloisField p f)) (a * a') ∧
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 4 (GaloisField p f)) ∧ g' * g' = 1 ∧
      (∀ y, (∀ w ∈ FM.span, polar (quadOdd 4 (GaloisField p f)) y w = 0) → g' y = y) ∧
      Module.finrank (GaloisField p f) (negSpace g') = 2 ∧ negSpace g' ≤ FM.span := by
  classical
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨Fact.out, hf1, by norm_num, hp2⟩
  have ctx := spinCtx_odd hp2 hq (n := 4) (by norm_num) hadm
  have : Group.IsPerfect (spinGroup (quadOdd 4 (GaloisField p f))) := ctx.perfect
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hdimV : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f) = 9 := by
    rw [finrank_odd]
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ := exists_twin_frame ctx.hodd
    ctx.hrange ctx.hZ (by omega) ctx.hproj (ctx.hperf R hR) (ctx.hperf R' hR') (ctx.hcorr R hR)
    (ctx.hcorr R' hR') (ctx.hnc R hR) (ctx.hnc R' hR') hne hx hcx hx1 hx' hcx' hx'1 hsame ha ha'
    hsq hsq'
  have hθu : spinAction (quadOdd 4 (GaloisField p f)) (a * a') = twinInv F₁ A A' := by
    rw [map_mul, hθa, hθa']
    rfl
  have hdet : LinearEquiv.det (twinInv F₁ A A') = 1 := by
    rw [← hθu]
    exact det_spinAction_eq_one _
  have hii : twinInv F₁ A A' * twinInv F₁ A A' = 1 :=
    LinearEquiv.ext fun v => twinInv_twinInv F₁ hAA hA'A' v
  refine ⟨F₁, twinInv F₁ A A', hF₁, hF₁', hθu.symm, twinInv_mem_orthogonalGroup F₁ A A', hii,
    ?_, finrank_minusSp_twinInv h2 F₁ hAA hA'A' hdet, ?_⟩
  · intro y hy
    exact twinInv_perp F₁ A A' ((Frame.mem_perp_iff_forall_incl F₁).mpr fun Y => hy _ ⟨Y, rfl⟩)
  · intro y hy
    have : y ∈ eigIn (twinInv F₁ A A') (-1) F₁.span := by
      rw [← minusSp_twinInv_eq h2 F₁]
      exact hy
    exact (mem_eigIn_iff.mp this).1

end CFSG.ClassicalInvolution.RouteD.TWE.B4
