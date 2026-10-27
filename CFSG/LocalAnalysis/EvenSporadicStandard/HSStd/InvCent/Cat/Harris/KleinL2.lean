module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.KleinBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearAction
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallClass
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearFaithfulness
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallInner
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearConjugacy
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieQuat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofGLS3Split
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.DiagonalLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpChainBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharOdd
public import CFSG.Open.StandardDefs
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.Walter.JRFacts
public import Certificates.Certificate10027
public import Certificates.Certificate10095
public import Certificates.Certificate10095Base
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10104
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate1016Base
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2130
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate9201
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallInner4
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut pslFieldAut)
open CFSG.ComponentClassification.CatalogueBLinearSemilinear

local notation "PSL₂" => Matrix.ProjectiveSpecialLinearGroup (Fin 2)

section Basic

variable {K : Type} [Field K] [Finite K]

theorem pslFieldAut_mul_inner (σ : K ≃+* K) (A : GL (Fin 2) K) :
    pslFieldAut (Fin 2) K σ * innerDiagonalAction 2 K A =
      innerDiagonalAction 2 K (glFieldAut (Fin 2) K σ A) * pslFieldAut (Fin 2) K σ := by
  have h := semilinearAction_mul 2 K 1 A σ 1
  simpa [semilinearAction] using h

theorem ringEquiv_mul_comm_of_frob {τ : K ≃+* K} (hτ : ∀ x, τ x = x ^ 9) (ρ : K ≃+* K) :
    τ * ρ = ρ * τ := by
  refine RingEquiv.ext fun x => ?_
  rw [RingAut.mul_apply, RingAut.mul_apply, hτ, hτ, map_pow]

theorem exists_scalar_of_commute (hpar : 4 ≤ Nat.card K) {τ ρ : K ≃+* K} (hτρ : τ * ρ = ρ * τ)
    (A : GL (Fin 2) K)
    (h : semilinearAction 2 K A ρ * pslFieldAut (Fin 2) K τ =
      pslFieldAut (Fin 2) K τ * semilinearAction 2 K A ρ) :
    ∃ c : Kˣ, glFieldAut (Fin 2) K τ A = A * GeneralLinearGroup.scalar (Fin 2) c := by
  have hcomm : pslFieldAut (Fin 2) K ρ * pslFieldAut (Fin 2) K τ =
      pslFieldAut (Fin 2) K τ * pslFieldAut (Fin 2) K ρ := by
    rw [← map_mul, ← map_mul, hτρ.symm]
  have h1 := pslFieldAut_mul_inner τ A
  have h2 : (innerDiagonalAction 2 K A * pslFieldAut (Fin 2) K τ) *
        pslFieldAut (Fin 2) K ρ =
      (innerDiagonalAction 2 K (glFieldAut (Fin 2) K τ A) * pslFieldAut (Fin 2) K τ) *
        pslFieldAut (Fin 2) K ρ := by
    calc (innerDiagonalAction 2 K A * pslFieldAut (Fin 2) K τ) * pslFieldAut (Fin 2) K ρ
        = innerDiagonalAction 2 K A *
            (pslFieldAut (Fin 2) K τ * pslFieldAut (Fin 2) K ρ) := by rw [mul_assoc]
      _ = innerDiagonalAction 2 K A *
            (pslFieldAut (Fin 2) K ρ * pslFieldAut (Fin 2) K τ) := by rw [hcomm]
      _ = semilinearAction 2 K A ρ * pslFieldAut (Fin 2) K τ := by
            simp only [semilinearAction, mul_assoc]
      _ = pslFieldAut (Fin 2) K τ * semilinearAction 2 K A ρ := h
      _ = (pslFieldAut (Fin 2) K τ * innerDiagonalAction 2 K A) *
            pslFieldAut (Fin 2) K ρ := by
            simp only [semilinearAction, mul_assoc]
      _ = _ := by rw [h1]
  have h3 := mul_right_cancel (mul_right_cancel h2)
  have h4 : innerDiagonalAction 2 K (A⁻¹ * glFieldAut (Fin 2) K τ A) = 1 := by
    rw [map_mul, map_inv, ← h3, inv_mul_cancel]
  have h5 : semilinearAction 2 K (A⁻¹ * glFieldAut (Fin 2) K τ A) 1 = 1 := by
    rw [semilinearAction_one_field]
    exact h4
  obtain ⟨-, c, hc⟩ := (semilinearAction_eq_one_iff 2 K le_rfl (Or.inr hpar) _ 1).1 h5
  exact ⟨c, by rw [hc]; group⟩

theorem frob_mul_self (hK : Nat.card K = 81) {τ : K ≃+* K} (hτ : ∀ x, τ x = x ^ 9) :
    τ * τ = 1 := by
  have hK' : Nat.card K = 3 ^ 4 := by rw [hK]; norm_num
  have := PSLSmall.frobenius_sq_eq_one hK' (by decide) (τ := τ) (fun x => by rw [hτ x]; norm_num)
  rwa [sq] at this

theorem ringChar_ne_two_of_card (hK : Nat.card K = 81) : ringChar K ≠ 2 :=
  CFSG.ComponentClassification.CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K
    (by rw [hK]; decide)

theorem glFieldAut_scalar (σ : K ≃+* K) (c : Kˣ) :
    glFieldAut (Fin 2) K σ (GeneralLinearGroup.scalar (Fin 2) c) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map σ.toMonoidHom c) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv_scalar (Fin 2) σ c

theorem isSquare_det_of_glFieldAut (hK : Nat.card K = 81) {τ : K ≃+* K}
    (hτ : ∀ x, τ x = x ^ 9) {A : GL (Fin 2) K} {c : Kˣ}
    (h : glFieldAut (Fin 2) K τ A = A * GeneralLinearGroup.scalar (Fin 2) c) :
    IsSquare (GeneralLinearGroup.det A) := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 81 := by rw [← Nat.card_eq_fintype_card, hK]
  have hττ := frob_mul_self hK hτ
  have hτu : ∀ u : Kˣ, Units.map τ.toMonoidHom u = u ^ 9 := fun u =>
    Units.ext (by simp [hτ])
  have hc : c * Units.map τ.toMonoidHom c = 1 := by
    have h2 : glFieldAut (Fin 2) K τ (glFieldAut (Fin 2) K τ A) = A := by
      have := congrArg (fun e : K ≃+* K => glFieldAut (Fin 2) K e A) hττ
      simpa using this
    have h3 := congrArg (glFieldAut (Fin 2) K τ) h
    rw [h2, map_mul, h, glFieldAut_scalar] at h3
    have h4 : GeneralLinearGroup.scalar (Fin 2) c *
        GeneralLinearGroup.scalar (Fin 2) (Units.map τ.toMonoidHom c) = 1 :=
      mul_left_cancel (a := A) (by rw [← mul_assoc, ← h3, mul_one])
    rw [← map_mul] at h4
    have h5 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) h4
    exact Units.ext (by simpa [Matrix.scalar_apply] using h5)
  have hd : GeneralLinearGroup.det A ^ 8 = c ^ 2 := by
    have h6 := congrArg GeneralLinearGroup.det h
    rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin] at h6
    have h7 : GeneralLinearGroup.det (glFieldAut (Fin 2) K τ A) =
        Units.map τ.toMonoidHom (GeneralLinearGroup.det A) :=
      GeneralLinearGroup.map_det τ.toRingHom A
    rw [h7, hτu] at h6
    exact mul_left_cancel (a := GeneralLinearGroup.det A) (by rw [← pow_succ', h6])
  rw [FiniteField.unit_isSquare_iff (ringChar_ne_two_of_card hK), hcard]
  calc GeneralLinearGroup.det A ^ (81 / 2) = (GeneralLinearGroup.det A ^ 8) ^ 5 := by
        rw [← pow_mul]
    _ = c * c ^ 9 := by rw [hd, ← pow_mul, ← pow_succ']
    _ = 1 := by rw [← hτu c, hc]

theorem conj_mk_eq_innerDiagonalAction {n : ℕ} (g : SpecialLinearGroup (Fin n) K) :
    MulAut.conj (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin n) K) =
      innerDiagonalAction n K (SpecialLinearGroup.toGL g) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : (innerDiagonalAction n K (SpecialLinearGroup.toGL g))
      (QuotientGroup.mk k : ProjectiveSpecialLinearGroup (Fin n) K) =
        QuotientGroup.mk (slConjugation n K (SpecialLinearGroup.toGL g) k) :=
    innerDiagonalAction_mk n K _ k
  rw [h1]
  change (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin n) K) * (QuotientGroup.mk k) *
    (QuotientGroup.mk g)⁻¹ = _
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation]
  simp

theorem innerDiagonalAction_mem_range_of_isSquare_det {A : GL (Fin 2) K}
    (hA : IsSquare (GeneralLinearGroup.det A)) :
    innerDiagonalAction 2 K A ∈ (MulAut.conj : PSL₂ K →* MulAut (PSL₂ K)).range := by
  obtain ⟨r, hr⟩ := hA
  have hdet : GeneralLinearGroup.det (A * GeneralLinearGroup.scalar (Fin 2) r⁻¹) = 1 := by
    rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, hr]
    group
  have hdet' : ((A * GeneralLinearGroup.scalar (Fin 2) r⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hdet
    simpa using this
  let g : SpecialLinearGroup (Fin 2) K :=
    ⟨((A * GeneralLinearGroup.scalar (Fin 2) r⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
      hdet'⟩
  have hg : SpecialLinearGroup.toGL g = A * GeneralLinearGroup.scalar (Fin 2) r⁻¹ := by
    ext1
    rfl
  refine ⟨QuotientGroup.mk g, ?_⟩
  rw [conj_mk_eq_innerDiagonalAction, hg, map_mul, innerDiagonalAction_scalar, mul_one]

theorem eq_one_of_pslFieldAut_mem_range (hpar : 4 ≤ Nat.card K) {κ : K ≃+* K}
    (h : pslFieldAut (Fin 2) K κ ∈ (MulAut.conj : PSL₂ K →* MulAut (PSL₂ K)).range) :
    κ = 1 := by
  obtain ⟨B, hB⟩ := PSLSmall.exists_innerDiagonal_of_mem_range h
  have h1 : semilinearAction 2 K B⁻¹ κ = 1 := by
    simp only [semilinearAction, map_inv, ← hB, inv_mul_cancel]
  exact ((semilinearAction_eq_one_iff 2 K le_rfl (Or.inr hpar) B⁻¹ κ).1 h1).1

theorem eq_frob_of_involution (hK : Nat.card K = 81) {ρ : K ≃+* K} (hρ1 : ρ ≠ 1)
    (hρ2 : ρ * ρ = 1) : ∀ x : K, ρ x = x ^ 9 := by
  have hsq : semilinearAction 2 K 1 ρ ^ 2 = 1 := by
    have h1 : semilinearAction 2 K 1 ρ = pslFieldAut (Fin 2) K ρ := by simp [semilinearAction]
    rw [h1, sq, ← map_mul, hρ2, map_one]
  obtain ⟨-, hfrob, -⟩ := odd_linear_field_involution_conjugacy 2 K 3 4 Nat.prime_three
    (by decide) (by norm_num) (by rw [hK]; norm_num) le_rfl (Or.inr (by rw [hK]; norm_num))
    1 ρ hρ1 hsq
  intro x
  rw [hfrob x]
  norm_num

theorem inner_part_of_commute (hK : Nat.card K = 81) {τ : K ≃+* K} (hτ : ∀ x, τ x = x ^ 9)
    {A : GL (Fin 2) K} {ρ : K ≃+* K}
    (h : semilinearAction 2 K A ρ * pslFieldAut (Fin 2) K τ =
      pslFieldAut (Fin 2) K τ * semilinearAction 2 K A ρ) :
    innerDiagonalAction 2 K A ∈ (MulAut.conj : PSL₂ K →* MulAut (PSL₂ K)).range := by
  obtain ⟨c, hc⟩ := exists_scalar_of_commute (by rw [hK]; norm_num)
    (ringEquiv_mul_comm_of_frob hτ ρ) A h
  exact innerDiagonalAction_mem_range_of_isSquare_det (isSquare_det_of_glFieldAut hK hτ hc)

theorem not_outerKlein_pslFieldAut (hK : Nat.card K = 81) {τ : K ≃+* K}
    (hτ : ∀ x, τ x = x ^ 9) : ¬ OuterKlein (pslFieldAut (Fin 2) K τ) := by
  rintro ⟨α, β, hαF, hβF, hα2, hβ2, -, hα, hβ, hαβ⟩
  set I : Subgroup (MulAut (PSL₂ K)) :=
    (MulAut.conj : PSL₂ K →* MulAut (PSL₂ K)).range with hI
  haveI hIn : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.innerNormal (PSL₂ K)
  obtain ⟨A, ρ, rfl⟩ := CFSG.ComponentClassification.CatLeafProof.psl_two_normal_form α
  obtain ⟨B, ρ', rfl⟩ := CFSG.ComponentClassification.CatLeafProof.psl_two_normal_form β
  have hiA := inner_part_of_commute hK hτ hαF
  have hiB := inner_part_of_commute hK hτ hβF
  have hpar : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have key : ∀ (C : GL (Fin 2) K) (κ : K ≃+* K), innerDiagonalAction 2 K C ∈ I →
      semilinearAction 2 K C κ * semilinearAction 2 K C κ ∈ I → κ * κ = 1 := by
    intro C κ hiC hsq
    have e : pslFieldAut (Fin 2) K κ * pslFieldAut (Fin 2) K κ =
        (innerDiagonalAction 2 K C * (pslFieldAut (Fin 2) K κ * innerDiagonalAction 2 K C *
          (pslFieldAut (Fin 2) K κ)⁻¹))⁻¹ *
          (semilinearAction 2 K C κ * semilinearAction 2 K C κ) := by
      simp only [semilinearAction]
      group
    have hmem : pslFieldAut (Fin 2) K κ * pslFieldAut (Fin 2) K κ ∈ I := by
      rw [e]
      exact I.mul_mem (I.inv_mem (I.mul_mem hiC (hIn.conj_mem _ hiC _))) hsq
    rw [← map_mul] at hmem
    exact eq_one_of_pslFieldAut_mem_range hpar hmem
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    apply hα
    rw [semilinearAction_one_field]
    exact hiA
  have hρ'1 : ρ' ≠ 1 := by
    rintro rfl
    apply hβ
    rw [semilinearAction_one_field]
    exact hiB
  have hρ2 : ρ * ρ = 1 := key A ρ hiA hα2
  have hρ'2 : ρ' * ρ' = 1 := key B ρ' hiB hβ2
  have hfr := eq_frob_of_involution hK hρ1 hρ2
  have hfr' := eq_frob_of_involution hK hρ'1 hρ'2
  have hρρ : ρ' = ρ := RingEquiv.ext fun x => by rw [hfr x, hfr' x]
  apply hαβ
  rw [hρρ]
  have e : semilinearAction 2 K A ρ * semilinearAction 2 K B ρ =
      innerDiagonalAction 2 K A * (pslFieldAut (Fin 2) K ρ * innerDiagonalAction 2 K B *
        (pslFieldAut (Fin 2) K ρ)⁻¹) * (pslFieldAut (Fin 2) K ρ * pslFieldAut (Fin 2) K ρ) := by
    simp only [semilinearAction]
    group
  rw [e, ← map_mul, hρ2, map_one, mul_one]
  exact I.mul_mem hiA (hIn.conj_mem _ hiB _)

@[expose] def KleinStmt {S : Type} [Group S] (σ : MulAut S) : Prop :=
  ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D → ¬ OuterKlein σ

theorem KleinStmt.of_eq {S : Type} [Group S] {σ τ : MulAut S} (h : σ = τ) (hτ : KleinStmt τ) :
    KleinStmt σ := by
  subst h
  exact hτ

theorem kleinStmt_inner (hK : Nat.card K = 81) {A : GL (Fin 2) K}
    (hσ : orderOf (innerDiagonalAction 2 K A) = 2) : KleinStmt (innerDiagonalAction 2 K A) :=
  fun _ hD => (PSLSmall.inner_two_false (by rw [hK]; norm_num)
    (Ring.two_ne_zero (ringChar_ne_two_of_card hK)) hσ hD).elim

theorem kleinStmt_psl_two (hK : Nat.card K = 81) (σ : MulAut (PSL₂ K)) (hσ : orderOf σ = 2) :
    KleinStmt σ := by
  by_cases hin : σ ∈ (MulAut.conj : PSL₂ K →* MulAut (PSL₂ K)).range
  · obtain ⟨B, hB⟩ := PSLSmall.exists_innerDiagonal_of_mem_range hin
    exact KleinStmt.of_eq hB (kleinStmt_inner hK (hB ▸ hσ))
  · obtain ⟨A, τ, hAτ⟩ := CFSG.ComponentClassification.CatLeafProof.psl_two_normal_form σ
    by_cases hτ : τ = 1
    · have h1 : σ = innerDiagonalAction 2 K A := by
        rw [hAτ, hτ, semilinearAction_one_field]
      exact KleinStmt.of_eq h1 (kleinStmt_inner hK (h1 ▸ hσ))
    · have hsq0 : σ ^ 2 = 1 := by
        have := pow_orderOf_eq_one σ
        rwa [hσ] at this
      have hsq : semilinearAction 2 K A τ ^ 2 = 1 := by rw [← hAτ]; exact hsq0
      have hK' : Nat.card K = 3 ^ 4 := by rw [hK]; norm_num
      obtain ⟨-, hτc, H, hα⟩ := odd_linear_field_involution_conjugacy 2 K 3 4 Nat.prime_three
        (by decide) (by norm_num) hK' le_rfl (Or.inr (by rw [hK]; norm_num)) A τ hτ hsq
      have hτ9 : ∀ x, τ x = x ^ 9 := fun x => by rw [hτc x]; norm_num
      have hc : MulAut.congr (innerDiagonalAction 2 K H) (pslFieldAut (Fin 2) K τ) = σ :=
        (MulEquiv.ext fun _ => rfl : MulAut.congr (innerDiagonalAction 2 K H)
          (pslFieldAut (Fin 2) K τ) = _).trans (hα.symm.trans hAτ.symm)
      intro D _ hk
      refine not_outerKlein_pslFieldAut hK hτ9 ?_
      have h2 := outerKlein_congr (innerDiagonalAction 2 K H).symm hk
      rw [← hc] at h2
      have h3 : MulAut.congr (innerDiagonalAction 2 K H).symm
          (MulAut.congr (innerDiagonalAction 2 K H) (pslFieldAut (Fin 2) K τ)) =
            pslFieldAut (Fin 2) K τ := by
        ext x
        simp [MulAut.congr_apply]
      rwa [h3] at h2
end Basic

theorem harrisKleinFree_of_concrete_a6 {t : StatedLieTag} {n p f : ℕ}
    (H : ∀ (S : Type) [Group S] [Finite S], LieModel S t n p f →
      ∃ (X : Type) (_ : Group X) (_ : S ≃* X), ∀ σ : MulAut X, orderOf σ = 2 → KleinStmt σ) :
    HarrisKleinFree t n p f := by
  intro S _ _ hm σ hσ D hD hk
  obtain ⟨X, _, e, hX⟩ := H S hm
  exact hX (MulAut.congr e σ) ((orderOf_congr e σ).trans hσ) _ (a6Hyp_congr e σ D hD)
    (outerKlein_congr e hk)

theorem harrisKleinFree_PSL_two_three_four : HarrisKleinFree .PSL 2 3 4 := by
  refine harrisKleinFree_of_concrete_a6 fun S _ _ hm => ?_
  have hadm : StatedLieAdmissible .PSL 2 3 4 :=
    ⟨Nat.prime_three, by norm_num, by norm_num, by decide, by decide⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hK81 : Nat.card K = 81 := by rw [hK]; norm_num
  exact ⟨PSL₂ K, inferInstance, e, fun σ hσ => kleinStmt_psl_two hK81 σ hσ⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
