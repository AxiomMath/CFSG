module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutPsl2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutPsp4
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutDiag
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutField
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerLift
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.Blueprint Subgroup CFSG.Assembly.LowTwoRank CFSG.GH74.GLS
  CFSG.GH74.Generic.BProg
open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Certified


theorem psp4_outer_involution_noShape {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {Y : Type} [Group Y] [Finite Y] (hY : LieModel Y .PSp 2 p f) (α : MulAut Y)
    (hα : α * α = 1) (hout : α ∉ (MulAut.conj : Y →* MulAut Y).range) (L : Subgroup Y)
    (hL : IsCompIn (fixSub α) L) :
    ¬ ∃ Z : Subgroup ↥L, Z ≤ center ↥L ∧ Odd (Nat.card ↥Z) ∧ ∃ _ : Z.Normal,
      QShapeNS (↥L ⧸ Z) := by
  rintro ⟨Z, hZc, -, hZn, hsh⟩
  obtain ⟨-, -, K, _, _, hK, ⟨ψ⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hY
  have hchar : ringChar K ≠ 2 := CFSG.GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hK
  have hβ2 : MulAut.congr ψ α * MulAut.congr ψ α = 1 := by rw [← map_mul, hα, map_one]
  have hα1 : α ≠ 1 := fun h => hout ⟨1, by rw [map_one, h]⟩
  have hβ1 : MulAut.congr ψ α ≠ 1 := fun h =>
    hα1 ((MulAut.congr ψ).injective (by rw [h, map_one]))
  obtain ⟨A, σ, hAσ, hσ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 (MulAut.congr ψ α) hβ2 hβ1
  have hKc : IsComponent (L.subgroupOf (fixSub α)) := hL.2
  have hKc' := LocalCores.isComponent_map_mulEquiv (fixedSubgroupCongrEquiv ψ α) hKc
  let eL := (Subgroup.subgroupOfEquivOfLe hL.1).symm.trans
    ((L.subgroupOf (fixSub α)).equivMapOfInjective
      (fixedSubgroupCongrEquiv ψ α).toMonoidHom (fixedSubgroupCongrEquiv ψ α).injective)
  by_cases hσ : σ = 1
  ·
    obtain rfl : σ = 1 := hσ
    rw [map_one, mul_one] at hAσ
    have hord : orderOf (conjAut 2 K A) = 2 := by
      rw [← hAσ]
      exact orderOf_eq_prime (by rw [pow_two]; exact hβ2) hβ1
    have hfix := congrArg CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup hAσ
    have hpsl : Psl2CQ p ↥L := Psl2CQ.of_mulEquiv eL
      (psl2CQ_of_component_equiv (MulEquiv.subgroupCongr hfix)
        (fun M hM => psl2CQ_inner_psp hp hp2 hK hf A hord hM) hKc')
    obtain ⟨j, -, hj⟩ := hpsl
    refine not_qShapeNS_of_central_hom_psl2 hp hp2
      (QuotientGroup.map Z (center ↥L) (MonoidHom.id ↥L) hZc) ?_ hj hsh
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have hl : l ∈ center ↥L := (QuotientGroup.eq_one_iff l).1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hl g]
  ·
    obtain ⟨e, -, hmodel⟩ := psp4_field_component_model hp hp2 hf hK A σ hAσ hσ2 hσ d hd hKc'
    have hmodelL : LieModel ↥L .PSp 2 p e := LieType.CurtisTits.lieModel_of_mulEquiv eL.symm hmodel
    obtain ⟨-, -, F', _, _, hF', ⟨ε⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hmodelL
    have hodd' : Odd (Nat.card F') := by
      rw [hF']
      exact (hp.odd_of_ne_two hp2).pow
    have hZbot : Z = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      apply ε.injective
      rw [map_one]
      refine psp4_centerless hodd' (ε z) fun g' => ?_
      have := congrArg ε (Subgroup.mem_center_iff.1 (hZc hz) (ε.symm g'))
      simpa using this
    have hmodelZ : LieModel (↥L ⧸ Z) .PSp 2 p e :=
      LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot).symm hmodelL
    exact not_qShapeNS_of_psp4 hp hp2 hmodelZ hsh

end Certified

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
