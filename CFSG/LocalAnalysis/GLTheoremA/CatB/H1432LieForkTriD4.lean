module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriThree
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkBase
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTriClassA
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.G2Class
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Setup
public import CFSG.HardMathSupport.Dickson.I271.ChevPBal
public import CFSG.HardMathSupport.Dickson.I271.I202Full
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.LieType.SteinbergBRBlockParabolicDInf
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
  (isSimpleGroup_fixSubgroup_fieldActor_D4 nonabelian_fixSubgroup_fieldActor_D4)


private theorem outerSubThree_fieldActor_triD4 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) :
    OuterSubThree .trialityD4 0 f (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.finite_graphFixedRootGroup_D4 σ
  have hk : Nat.card (fixSubfield σ) = 3 ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hZ : Subgroup.center (adjointGroup Tag.G2 (fixSubfield σ)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hm : LieModel ↥(adjointGroup Tag.G2 (fixSubfield σ)) .G2 0 3 f :=
    Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_three, hf, rfl, Nat.le_self_pow (by omega) 3⟩,
      fixSubfield σ, inferInstance, inferInstance, hk,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm⟩⟩)
  refine outerSubThree_of_fixed_equiv _ (MulEquiv.refl _)
    (isSimpleGroup_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ)
    (nonabelian_fixSubgroup_fieldActor_D4 3 f Nat.prime_three (by norm_num) K hK σ hσ) ?_
  exact outerLayerThree_congr
    (ExcTriClassA.fixSubgroupFieldActorEquivG2 Nat.prime_three (by norm_num) hf hK σ hσ).symm
    (Or.inl ⟨.G2, 0, f, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)), hm⟩)

theorem outerSubThree_triD4_graphFixed {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K 3] (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
    (β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ3 : β ^ 3 = 1)
    (hout : β ∉ inner ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    OuterSubThree .trialityD4 0 f (fixSubgroup β) := by
  classical
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.finite_graphFixedRootGroup_D4 σ
  exact three_of_classes_gen hf hK σ hσ (fun γ => OuterSubThree .trialityD4 0 f (fixSubgroup γ))
    (fun ε γ h => outerSubThree_of_conj ε γ h) (fun γ h => (outerSubThree_inv_iff γ).1 h)
    (outerSubThree_fieldActor_triD4 hf hK σ hσ)
    (fun hc hc0 A hA => (exc_noComponent_classB hf hK σ hσ hc hc0 A hA).elim) β hβ3 hout

theorem lieOuterThreeAt_triD4 :
    LieOuterThreeAt CFSG.HardMathSupport.Dickson.Sec6.I923.FamTriD4 := by
  intro P _ _ t n f hadm hF hm ψ hψ3 hψ
  have ht : t = .trialityD4 := hF
  subst ht
  obtain ⟨rfl, hexc⟩ : n = 0 ∧ ChevalleyExceptionalModel P .trialityD4 3 f := by
    rcases hm with ⟨hcl, -⟩ | ⟨hn, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
    · exact absurd hcl (by decide)
    · exact ⟨hn, hexc⟩
    · exact absurd hree (by decide)
    · exact absurd h (by decide)
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨K, _, _, σ₀, hK, hσ₀, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_graphFixedRootGroup_of_twisted_prime
      Nat.prime_three hf hexc.2
  let σ : K ≃+* K :=
    RingEquiv.ofBijective σ₀ ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  have hσ : ∀ c, σ c = c ^ (3 ^ f) := hσ₀
  have hK3 : Nat.card K = (3 ^ f) ^ 3 := hK
  let E : P ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e.symm
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.finite_graphFixedRootGroup_D4 σ
  haveI : CharP K 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three (by omega) (by rw [hK3, ← pow_mul, mul_comm] : Nat.card K = 3 ^ (3 * f))
  refine outerSubThree_congr E ?_
  have hφ3 : MulAut.congr E ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hφ : MulAut.congr E ψ ∉ inner ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rintro ⟨c, hc⟩
    refine hψ ⟨E.symm c, (MulAut.congr E).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
    exact hc
  exact outerSubThree_triD4_graphFixed hf hK3 σ hσ _ hφ3 hφ

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
