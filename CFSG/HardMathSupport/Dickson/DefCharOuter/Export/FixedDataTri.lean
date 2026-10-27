module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.FixedData
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriThree
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriClassA

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
  CFSG.HardMathSupport.Lang.Triality
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux


section Classes

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem fixedData3_classA :
    FixedData3 (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  haveI := finite_graphFixedRootGroup_D4 σ
  obtain ⟨hchev, hdvd, h27⟩ := ExcTriClassA.chevFacts_fixSubgroup_fieldActor_D4 Nat.prime_three
    (by norm_num) hf hK σ hσ
  have hs := isSimpleGroup_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ
  have hnab := nonabelian_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ
  exact FixedData3.ofSimpleNormal (SimpleNormalData.ofSimple hs hnab hchev hdvd) (h27 rfl)

theorem fixedData3_classB {c : K} (hc : σ c = c) (hc0 : c ≠ 0) :
    FixedData3 (fixSubgroup (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
      fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  haveI := finite_graphFixedRootGroup_D4 σ
  exact FixedData3.ofNoComponent (exc_noComponent_classB hf hK σ hσ hc hc0)
    (glaPPrimeCoreOf_fixSubgroup_conj_mul_fieldActor hf hK σ hσ hc hc0)

theorem fixedData3_trialityD4_three
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ3 : β ^ 3 = 1)
    (hout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    FixedData3 (fixSubgroup β) := by
  classical
  haveI := finite_graphFixedRootGroup_D4 σ
  exact three_of_classes_gen hf hK σ hσ (fun γ => FixedData3 (fixSubgroup γ))
    (fun ε _ h => FixedData3.of_conj_aut ε h) (fun _ h => FixedData3.of_inv h)
    (fixedData3_classA hf hK σ hσ) (fun hc hc0 => fixedData3_classB hf hK σ hσ hc hc0) β hβ3 hout

end Classes

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
