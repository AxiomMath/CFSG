module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.D4G2All
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutTorus
public import CFSG.HardMathSupport.Lang.Triality.OrbitCounts
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Lang.Triality CFSG.RankThree.PartTwo.KFacts

section

variable {K : Type} [Field K] [Finite K]

theorem fixSubfieldRestrict_toRingHom_eq_id (σ : K ≃+* K) :
    (fixSubfieldRestrict σ σ).toRingHom = RingHom.id (fixSubfield σ) :=
  RingHom.ext fun c => Subtype.ext (by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_fixSubfieldRestrict]
    exact c.2)

end

section

variable
  {K : Type} [Field K] [Finite K]

def trialityFieldImageEquivRoot (σ : K ≃+* K) :
    ↥(trialityFieldImage σ σ) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ))) :=
  (Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype)
    (baseChangeGL_injective _)).symm.trans
    (MulEquiv.subgroupCongr (by rw [fixSubfieldRestrict_toRingHom_eq_id]))

def trialityFieldImageEquivG2 (σ : K ≃+* K) (hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ)) :
    ↥(trialityFieldImage σ σ) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
  (trialityFieldImageEquivRoot σ).trans
    ((MulEquiv.subgroupCongr (d4_twistedFixedGroup_id_eq_graphFixedRootGroup (K := fixSubfield σ))).symm.trans
      (d4FixedG2EquivAll (fixSubfield σ) hk3))

end

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
