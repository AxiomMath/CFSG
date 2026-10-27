module

public import CFSG.ClassicalInvolution.Asc77.WP3SCVOrthB
public import CFSG.ClassicalInvolution.Asc77.WP3SCVSigma
public import CFSG.ClassicalInvolution.Asc77.WP3SCVSp4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinModel
import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
import CFSG.ClassicalInvolution.Asc77.AscE189Orth
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
public import CFSG.ClassicalInvolution.RouteD.MultiStarStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.SCV

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalGroups.Orthogonal
  QuadraticMap CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal.Small CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)

section Model

variable {p : ℕ} [Fact p.Prime]

@[expose] def SmallSigmaOn (t : StatedLieTag) (M : LieUniversal) : Prop :=
  ∀ {H : Type} [Group H] (ψ : M.K →* H), ψ.ker ≤ Subgroup.center M.K →
    ∀ {R R' : Subgroup M.K}, R ∈ Generic.fundamentalSubgroups t M.D →
      R' ∈ Generic.fundamentalSubgroups t M.D → R ≠ R' → Commutes R R' →
      ∀ {x x' : M.K}, x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        x * x' ∈ Subgroup.center M.K →
        ∀ v : ↥(inducedAutOn ψ.range), v * v = 1 →
          (∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v) →
            ∀ s ∈ R', v * innerHom ψ s = innerHom ψ s * v

section Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)}

theorem smallSigmaOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 3 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hperpOK : ∀ fr : Frame Q, 3 ≤ Module.finrank F fr.perp ∧
      ∀ P P' : HypPair (Q.restrict fr.perp), ¬ P.Orth P')
    (hlift : ∀ (H : Type) [Group H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSim Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ Generic.fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ Generic.fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ Generic.fundamentalSubgroups t D, ∀ r ∈ R,
      r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    SmallSigmaOn t ⟨spinGroup Q, D⟩ := by
  intro H _ ψ hker R R' hR hR' hne hcomm x x' hxR hx2 hx1 hx'R' hx'2 hx'1 hc v hv2 hvR
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R hR r hr (Orth15.mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R' hR' r hr (Orth15.mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hxx : x' * x⁻¹ ∈ Subgroup.center (spinGroup Q) := by
    have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [h1, ← hcomm x hxR x' hx'R']
    exact hc
  exact sigma_spin hodd h5 hQ hrange hZ hV hproj hperpOK (hperf R hR) (hperf R' hR')
    (hcorr R hR) (hcorr R' hR') hinj hinj' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hxx hker
    (hlift H ψ hker) v hv2 hvR

end Transport

section Instances

theorem smallSigma_pomegaOdd3 (e : ℕ) : SmallSigma p .POmegaOdd 3 e := by
  intro hp2 hq hadm
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
  show SmallSigmaOn .POmegaOdd ⟨spinGroup (quadOdd 3 (GaloisField p e)),
    oddDatum 3 (GaloisField p e)⟩
  refine smallSigmaOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadOdd 3 _ h2) (range_spinAction_quadOdd h2 hn3)
    (centerScalar_quadOdd h2 hn3) (by omega) (fun F₁ F₂ h => ?_) (fun fr => ?_)
    (fun H _ ψ hψ => liftSim_quadOdd hp2 hn3 he ψ hψ) _ (fundCorr_odd hp2 hq hadm).1 hperf hnc
  · have := finrank_eq_eight_of_proj hodd F₁ F₂ h
    omega
  · have h4 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    refine ⟨by omega, fun P P' hP => ?_⟩
    have := four_le_finrank_of_orth hP
    omega

theorem smallSigma_pomegaMinus4 (e : ℕ) : SmallSigma p .POmegaMinus 4 e := by
  intro hp2 hq hadm
  have hn4 : 4 ≤ 4 := le_rfl
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, h4q⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
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
  show SmallSigmaOn .POmegaMinus ⟨spinGroup (quadMinus 4 (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum 4 (minusCoeffs_irr p e)⟩
  refine smallSigmaOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega)
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h) (fun fr => ?_)
    (fun H _ ψ hψ => liftSim_quadMinus hp2 hn4 he ψ hψ) _ (fundCorr_minus hp2 hq hadm).1
    hperf hnc
  have h4 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
  refine ⟨by omega, fun P P' hP => ?_⟩
  obtain ⟨F₂, hF₂⟩ := exists_frame_le_of_orth hP
  exact false_of_orth_quadMinus_four h2 (minusCoeffs_irr p e) h4q fr F₂ hF₂

theorem smallSigmaFacts_proved : SmallSigmaFacts p :=
  fun e => ⟨smallSigma_psp2 e, smallSigma_pomegaOdd3 e, smallSigma_pomegaMinus4 e⟩

end Instances

end Model

end CFSG.ClassicalInvolution.Asc77.SCV
