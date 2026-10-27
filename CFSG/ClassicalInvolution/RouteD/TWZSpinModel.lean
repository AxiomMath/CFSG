module

public import CFSG.ClassicalInvolution.RouteD.TWZSpinB
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthWitt
public import CFSG.ClassicalInvolution.Asc77.AscIHHelp
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Asc77.AscIHThm2
public import CFSG.ClassicalInvolution.Asc77.AscIHWitness

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Models.Transfer (CenterScalar)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "GFund" => CFSG.ClassicalInvolution.Generic.fundamentalSubgroups

section Statement

@[expose] def SqTrichotomyOn (t : StatedLieTag) (M : LieUniversal) : Prop :=
  ∀ (X : Type) [Group X] (θ : M.K →* X), Function.Surjective θ → θ.ker ≤ Subgroup.center M.K →
    ∀ (R R' R₂ : Subgroup M.K), R ∈ GFund t M.D →
      R' ∈ GFund t M.D → R₂ ∈ GFund t M.D → R ≠ R' →
      ∀ (x x' x₂ : M.K), x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        θ x = θ x' → x₂ ∈ R₂ → x₂ * x₂ = 1 → x₂ ≠ 1 →
        ∀ α : MulAut X, α * α * (α * α) = 1 → (∀ r ∈ R, α (θ r) = θ r) →
          (∀ r ∈ R', α (θ r) = θ r) → (∀ r ∈ R₂, α (θ r) = θ r) →
          α * α = 1 ∨ α * α = MulAut.conj (θ x) ∨
            ∃ g : M.K,
              (∀ r ∈ R₂, (α * α) (θ x₂ * θ (g * r * g⁻¹) * (θ x₂)⁻¹) = θ (g * r * g⁻¹)) ∧
                ∃ r ∈ R₂, (α * α) (θ (g * r * g⁻¹)) ≠ θ (g * r * g⁻¹)

end Statement

section Transport

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem sqTrichotomyOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hno : ∀ F₀ F₁ : OFrame Q, F₁.span ≤ F₀.perp → False)
    (hlift : ∀ (H : Type) [Group H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSim Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ GFund t D, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ GFund t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ GFund t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    SqTrichotomyOn t ⟨spinGroup Q, D⟩ := by
  intro X _ θ hθs hθk R R' R₂ hR hR' hR₂ hne x x' x₂ hx hx2 hx1 hx' hx'2 hx'1 hxx' hx₂ hx₂2 hx₂1
    α hα4 hαR hαR' hαR₂
  have hinj : ∀ {S : Subgroup (spinGroup Q)}, S ∈ GFund t D →
      ∀ r ∈ S, spinAction Q r = 1 → r = 1 := fun {S} hS =>
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center (ker_spinAction_le_center Q)
      fun r hr hcen => hnc S hS r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  exact spin_sq_trichotomy hodd h5 hQ hrange hZ hV hproj hno hθs hθk (hlift X θ hθk) (hperf R hR)
    (hperf R' hR') (hcorr R hR) (hcorr R' hR') (hinj hR) (hinj hR') hne hx hx2 hx1 hx' hx'2 hx'1
    hxx' (hperf R₂ hR₂) (hcorr R₂ hR₂) (hinj hR₂) hx₂ hx₂2 hx₂1 α hα4 hαR hαR' hαR₂

end Transport

section Models

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Models.Transfer

set_option linter.unusedSectionVars false

variable {p e : ℕ} [Fact p.Prime]


theorem sqTrichotomy_odd3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaOdd 3 p e) :
    SqTrichotomyOn .POmegaOdd
      (CFSG.ClassicalInvolution.Generic.modelUniv .POmegaOdd 3 p e Fact.out) := by
  have hn3 : 3 ≤ 3 := le_rfl
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := 3) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := 3) trivial hadm
    (by simp)
  show SqTrichotomyOn .POmegaOdd ⟨spinGroup (quadOdd 3 (GaloisField p e)),
    oddDatum 3 (GaloisField p e)⟩
  refine sqTrichotomyOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadOdd 3 _ h2) (range_spinAction_quadOdd h2 hn3)
    (centerScalar_quadOdd h2 hn3) (by omega) (fun F₁ F₂ h => ?_) (fun F₀ F₁ h => ?_)
    (fun H _ ψ hψ => liftSim_quadOdd hp2 hn3 he ψ hψ) _ (fundCorr_odd hp2 hq hadm).1 hperf hnc
  · have := finrank_eq_eight_of_proj hodd F₁ F₂ h
    omega
  · have h1 := Submodule.finrank_mono h
    have h3 := finrank_perp_add_four F₀
    rw [Frame.finrank_span] at h1
    omega

theorem sqTrichotomy_minus4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p e) :
    SqTrichotomyOn .POmegaMinus
      (CFSG.ClassicalInvolution.Generic.modelUniv .POmegaMinus 4 p e Fact.out) := by
  have hn4 : 4 ≤ 4 := le_rfl
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := 4) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := 4) trivial
    hadm (by simp)
  show SqTrichotomyOn .POmegaMinus ⟨spinGroup (quadMinus 4 (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum 4 (minusCoeffs_irr p e)⟩
  exact sqTrichotomyOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega)
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h)
    (fun F₀ F₁ h => false_of_orth_quadMinus_four h2 (minusCoeffs_irr p e) h4 F₀ F₁ h)
    (fun H _ ψ hψ => liftSim_quadMinus hp2 hn4 he ψ hψ) _ (fundCorr_minus hp2 hq hadm).1
    hperf hnc

end Models

end CFSG.ClassicalInvolution.RouteD.TWZ
