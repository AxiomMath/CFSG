module

public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import Certificates.Certificate13603
public import Certificates.Certificate63001
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import Certificates.Certificate8026Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.GLTheoremA
  CFSG.StandardType CFSG.LieType.Chevalley

section E7Certificates

theorem exists_mulEquiv_adjointGroup_E7_of_hasLabel {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hK : Rk2IsLabel K lab) (ht : lab.tag = .E7)
    (hZ : Subgroup.center K = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ lab.n ∧
      Nonempty (K ≃* adjointGroup .E7 F) := by
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 lab.n :=
    lieModel_of_markedModel_E7 ht hM
  obtain ⟨-, F, hField, hFinite, hCard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E7 ∈ chevalleyExceptionalTags)
  letI : Field F := hField
  letI : Finite F := hFinite
  let χ : AdjointQuotient .E7 F ≃* adjointGroup .E7 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .E7) (K := F))).trans
      QuotientGroup.quotientBot
  let eK : K ≃* K ⧸ Subgroup.center K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot |>.symm
  exact ⟨F, hField, hFinite, hCard, ⟨eK.trans (φ.trans χ)⟩⟩

end E7Certificates

section E8Certificates

theorem exists_mulEquiv_adjointGroup_of_isLabel_E8 {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hlab : HasLabel K (fun l : GLALabel => l = lab)) (htag : lab.tag = .E8)
    (hZ : Subgroup.center K = ⊥) :
    Nonempty (K ≃* ↥(adjointGroup Tag.E8 (GaloisField 2 lab.n))) := by
  have hK : Rk2IsLabel K lab := hlab
  obtain ⟨-, hlam, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have hn1 : 1 ≤ lab.n := hlam.1
  let e0 : (K ⧸ Subgroup.center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hM' : MarkedModel lab K := MarkedModel.of_mulEquiv e0 hM
  have hL : LieModel K .E8 0 2 lab.n := lieModel_of_markedModel_E8 htag hM'
  have hCEM : ChevalleyExceptionalModel K .E8 2 lab.n :=
    hL.chevalleyExceptionalModel (by decide)
  obtain ⟨F, hF, hFin, hcard, ⟨iso⟩⟩ := hCEM.2
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (GaloisField 2 lab.n) := Fintype.ofFinite _
  have hGFcard : Nat.card (GaloisField 2 lab.n) = 2 ^ lab.n :=
    GaloisField.card 2 lab.n (by omega)
  let φ : F ≃+* GaloisField 2 lab.n := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hGFcard, hcard])
  let eAQ : AdjointQuotient Tag.E8 F ≃* ↥(adjointGroup Tag.E8 F) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := Tag.E8) (K := F))).trans
      QuotientGroup.quotientBot
  exact ⟨iso.trans (eAQ.trans (CFSG.TauCetiBridge.adjointGroupCongr φ))⟩

end E8Certificates

end CFSG.LocalAnalysis.GLTheoremA.Y10F
