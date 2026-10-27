module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinSpin
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinModel
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
import CFSG.ClassicalInvolution.Asc77.AscE189Orth
import CFSG.ClassicalInvolution.Asc77.AscIHHelp
import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthWitt
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
public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.AscE189Model
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)

section Proj

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem span_le_perp_of_proj (h2 : (2 : F) ≠ 0) (F₁ F₂ : Frame Q)
    (h : F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1)) : F₂.span ≤ F₁.perp := by
  intro x hx
  rw [Frame.mem_perp_iff_fix F₁ h2]
  have h1 : F₂.La (-1) x = -x := La_neg_one_of_mem_span F₂ hx
  rw [h, LinearEquiv.mul_apply, LinearEquiv.neg_apply] at h1
  exact neg_inj.mp h1

theorem finrank_eq_eight_of_proj [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (F₁ F₂ : Frame Q) (h : F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1)) :
    Module.finrank F V = 8 := by
  have h1 := finrank_negSpace_of_isFundamental hodd (IsFundamental.of_frame F₂)
  rw [h, negSpace_neg_mul] at h1
  have h2 := finrank_negSpace_add_finrank_posSpace hodd (IsFundamental.of_frame F₁)
  rw [finrank_negSpace_of_isFundamental hodd (IsFundamental.of_frame F₁), h1] at h2
  omega

end Proj

section Transport

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

omit [DecidableEq ι] in
theorem twinInnerAlphaOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    TwinInnerAlphaOn t ⟨spinGroup Q, D⟩ := by
  intro H _ _ ψ R R' x x' hpair u hun hu hu2 hu1 huz
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R hpair.mem r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R' hpair.mem' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  exact alphaOf_spin_twin_pair hodd h5 hQ hrange hZ hV hproj (hperf R hpair.mem)
    (hperf R' hpair.mem') (hcorr R hpair.mem) (hcorr R' hpair.mem') hinj hinj' hpair.ne
    hpair.comm hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 ψ hpair.ker
    hpair.same hu hun hu2 hu1 huz

theorem twinOuterAlphaOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hlift : ∀ (H : Type) [Group H] [Finite H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSim Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    TwinOuterAlphaOn t ⟨spinGroup Q, D⟩ := by
  intro H _ _ ψ R R' x x' hpair v hvR hvR' hy2 hy1 hyz
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R hpair.mem r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R' hpair.mem' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  exact alphaOf_spin_twin_pair_outer hodd h5 hQ hrange hZ hV hproj (hperf R hpair.mem)
    (hperf R' hpair.mem') (hcorr R hpair.mem) (hcorr R' hpair.mem') hinj hinj' hpair.ne
    hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 hpair.ker
    (hlift H ψ hpair.ker) hpair.same v hvR hvR' hy2 hy1 hyz

end Transport

section Families

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

variable {p e : ℕ} [Fact p.Prime]

theorem five_le_card_galoisField (hq : 5 ≤ p ^ e) : 5 ≤ Nat.card (GaloisField p e) := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p e he]
  exact hq

theorem fund_noncentral_modelUniv {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hnA1 : ¬ (t = .PSL ∧ n = 2)) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, ∀ r ∈ R,
      r ∈ Subgroup.center (modelUniv t n p e Fact.out).K → r = 1 := by
  intro R hR r hr hcen
  refine CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic p t n e hfund hadm hnA1 R hR
    r hr fun y => ?_
  have h := Subgroup.mem_center_iff.mp hcen y
  have : r * y * r⁻¹ * y⁻¹ = 1 := by
    rw [← h]
    group
  rw [this]
  exact one_mem _

theorem liftSim_quadOdd (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) (he : 1 ≤ e) {H : Type} [Group H]
    (ψ : spinGroup (quadOdd n (GaloisField p e)) →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadOdd n (GaloisField p e)))) :
    LiftSim (quadOdd n (GaloisField p e)) ψ := by
  intro σ
  obtain ⟨α, hα, A, φ, μ, hsim, hmat⟩ := spinOdd_exists_lift_similarity (F := GaloisField p e)
    (p := p) (f := e) hp2 hn he (GaloisField.card p e (by omega)) ψ.rangeRestrict
    (MonoidHom.rangeRestrict_surjective ψ) (by rwa [MonoidHom.ker_rangeRestrict]) σ
  exact ⟨α, hα, A, φ, μ, hsim, hmat⟩

theorem liftSim_quadPlus (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n) (he : 1 ≤ e) {H : Type} [Group H]
    (ψ : spinGroup (quadPlus n (GaloisField p e)) →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n (GaloisField p e)))) :
    LiftSim (quadPlus n (GaloisField p e)) ψ := by
  intro σ
  obtain ⟨α, hα, A, φ, μ, hsim, hmat⟩ := spinPlus_exists_lift_similarity (F := GaloisField p e)
    (p := p) (f := e) hp2 hn he (GaloisField.card p e (by omega)) ψ.rangeRestrict
    (MonoidHom.rangeRestrict_surjective ψ) (by rwa [MonoidHom.ker_rangeRestrict]) σ
  exact ⟨α, hα, A, φ, μ, hsim, hmat⟩

theorem liftSim_quadMinus (hp2 : p ≠ 2) {n : ℕ} (hn : 4 ≤ n) (he : 1 ≤ e) {H : Type} [Group H]
    (ψ : spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2) →* H)
    (hψ : ψ.ker ≤ Subgroup.center
      (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2))) :
    LiftSim (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2) ψ := by
  intro σ
  obtain ⟨α, hα, A, φ, μ, hsim, hmat⟩ := spinMinus_exists_lift_similarity (F := GaloisField p e)
    (p := p) (f := e) hp2 hn he (GaloisField.card p e (by omega)) (minusCoeffs_irr p e)
    ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
    (by rwa [MonoidHom.ker_rangeRestrict]) σ
  exact ⟨α, hα, A, φ, μ, hsim, hmat⟩

theorem twinInnerAlpha_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p e) : TwinInnerAlpha p e .POmegaOdd n := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p e) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have : Group.IsPerfect (spinGroup (quadOdd n (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := n) trivial hadm
    (by simp)
  show TwinInnerAlphaOn .POmegaOdd ⟨spinGroup (quadOdd n (GaloisField p e)),
    oddDatum n (GaloisField p e)⟩
  refine twinInnerAlphaOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadOdd n _ h2) (range_spinAction_quadOdd h2 hn3)
    (centerScalar_quadOdd h2 hn3) (by omega) (fun F₁ F₂ h => ?_) _
    (fundCorr_odd hp2 hq hadm).1 hperf hnc
  have := finrank_eq_eight_of_proj hodd F₁ F₂ h
  omega

theorem twinOuterAlpha_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p e) : TwinOuterAlpha p e .POmegaOdd n := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p e) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have : Group.IsPerfect (spinGroup (quadOdd n (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := n) trivial hadm
    (by simp)
  show TwinOuterAlphaOn .POmegaOdd ⟨spinGroup (quadOdd n (GaloisField p e)),
    oddDatum n (GaloisField p e)⟩
  refine twinOuterAlphaOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadOdd n _ h2) (range_spinAction_quadOdd h2 hn3)
    (centerScalar_quadOdd h2 hn3) (by omega) (fun F₁ F₂ h => ?_)
    (fun H _ _ ψ hψ => liftSim_quadOdd hp2 hn3 he ψ hψ) _ (fundCorr_odd hp2 hq hadm).1 hperf hnc
  have := finrank_eq_eight_of_proj hodd F₁ F₂ h
  omega

theorem twinInnerAlpha_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p e) (hn5 : 5 ≤ n) :
    TwinInnerAlpha p e .POmegaPlus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have : Group.IsPerfect (spinGroup (quadPlus n (GaloisField p e))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaPlus) (n := n) trivial hadm
    (by simp)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p e)),
      plusDatum n (GaloisField p e) hn3⟩ →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, R ≤ ⁅R, R⁆) →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) →
        TwinInnerAlphaOn .POmegaPlus M := by
    intro M hM hperf hnc
    subst hM
    refine twinInnerAlphaOn_of_spin hodd (five_le_card_galoisField hq)
      (nondegenerate_polarBilin_quadPlus n _) (range_spinAction_quadPlus hn3)
      (centerScalar_quadPlus hn3) (by omega) (fun F₁ F₂ h => ?_) _
      (fundCorr_plus hp2 hq hn4).1 hperf hnc
    have := finrank_eq_eight_of_proj hodd F₁ F₂ h
    omega
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3) hperf hnc

theorem twinOuterAlpha_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p e) (hn5 : 5 ≤ n) :
    TwinOuterAlpha p e .POmegaPlus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have : Group.IsPerfect (spinGroup (quadPlus n (GaloisField p e))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaPlus) (n := n) trivial hadm
    (by simp)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p e)),
      plusDatum n (GaloisField p e) hn3⟩ →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, R ≤ ⁅R, R⁆) →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) →
        TwinOuterAlphaOn .POmegaPlus M := by
    intro M hM hperf hnc
    subst hM
    refine twinOuterAlphaOn_of_spin hodd (five_le_card_galoisField hq)
      (nondegenerate_polarBilin_quadPlus n _) (range_spinAction_quadPlus hn3)
      (centerScalar_quadPlus hn3) (by omega) (fun F₁ F₂ h => ?_)
      (fun H _ _ ψ hψ => liftSim_quadPlus hp2 hn5 he ψ hψ) _
      (fundCorr_plus hp2 hq hn4).1 hperf hnc
    have := finrank_eq_eight_of_proj hodd F₁ F₂ h
    omega
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3) hperf hnc

theorem hproj_quadMinus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ} (hn4 : 4 ≤ n)
    (F₁ F₂ : Frame (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2))
    (h : F₂.La (-1) = LinearEquiv.neg (GaloisField p e) * F₁.La (-1)) : False := by
  obtain ⟨hodd, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  by_cases hn : n = 4
  · subst hn
    exact false_of_orth_quadMinus_four h2 (minusCoeffs_irr p e) h4 F₁ F₂
      (span_le_perp_of_proj h2 F₁ F₂ h)
  · have := finrank_eq_eight_of_proj hodd F₁ F₂ h
    omega

theorem twinInnerAlpha_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) : TwinInnerAlpha p e .POmegaMinus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have : Group.IsPerfect (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := n) trivial
    hadm (by simp)
  show TwinInnerAlphaOn .POmegaMinus ⟨spinGroup (quadMinus n (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum n (minusCoeffs_irr p e)⟩
  exact twinInnerAlphaOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega)
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h) _ (fundCorr_minus hp2 hq hadm).1 hperf hnc

theorem twinOuterAlpha_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) : TwinOuterAlpha p e .POmegaMinus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have : Group.IsPerfect (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := n) trivial
    hadm (by simp)
  show TwinOuterAlphaOn .POmegaMinus ⟨spinGroup (quadMinus n (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum n (minusCoeffs_irr p e)⟩
  exact twinOuterAlphaOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega)
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h)
    (fun H _ _ ψ hψ => liftSim_quadMinus hp2 hn4 he ψ hψ) _ (fundCorr_minus hp2 hq hadm).1
    hperf hnc

end Families

end CFSG.ClassicalInvolution.Asc77
