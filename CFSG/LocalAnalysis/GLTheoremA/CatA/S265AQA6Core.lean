module

public import CFSG.Open.StatedDefs
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalSpEight
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerLift
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartTwo.KFacts.K71Sp48Index
import CFSG.SignalizerFunctorTheorem.CatalogBridge.MinimalSz
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2
import CFSG.Adapters.Certificate43Check
import CFSG.Adapters.RankTwoModelTransports
import CFSG.Walter.PSL2Facts.Even
import CFSG.CGT.PushingUpLit.CGT6.SixFour
import CFSG.CGT.PushingUpLit.CGT6.SixSixteen
import CFSG.CGT.PushingUpLit.Glue.ClassXBasic
import CFSG.CGT.PushingUpLit.Glue.RadicalSylow
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.ClassicalInvolution.ModelFacts.OddCover
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
import CFSG.ClassicalInvolution.Models.LinearFrames
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryFrames
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TwistedRankE6
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LieType.SeitzGeneration.ExcVacuousTits
import CFSG.LieType.SeitzGeneration.Hyper
import CFSG.LieType.SeitzGeneration.HyperBridge
import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.A3Structure314Defs
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.C2PushThree
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F918H5
import CFSG.Quasithin.Background.FFC4Tr2
import CFSG.Quasithin.Background.GoldschmidtS146RBend1
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S14610Q1
import CFSG.Quasithin.EmptyFaithful.S14610Top
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S146zYFacts
import CFSG.Quasithin.EmptyFaithful.S146zYRes
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.S153E59A
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.A7NatMain
import CFSG.Quasithin.H13.NQCoreP134Main
import CFSG.Quasithin.Recognition.ModelBridges
import CFSG.Quasithin.Vol2.Ch10SecB4
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
import CFSG.Quasithin.Vol2.Ch1Chief
import CFSG.Quasithin.Vol2.Ch1EightFourChar2
import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
import CFSG.RankThree.PartOne.K133H.G2Plane
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.RF4.FinalSec66
import CFSG.RankThree.PartOne.S11d.OutEsix
import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import Certificates.Certificate9530

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  (symplectic_prime_subfield_fixed_group_and_full_centralizer_odd)
open scoped MatrixGroups

private theorem spFourEight_false_of_fix_proj {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) {Eb : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hcomm : ∀ a ∈ Eb, ∀ c ∈ Eb, a * c = c * a) (hE3 : ∀ c ∈ Eb, c ^ 3 = 1)
    (h9 : 9 ≤ Nat.card Eb) {J : Subgroup (StatedProj (StatedSp 2 K))} (hJ : ⁅J, J⁆ = J)
    (hJ1 : J ≠ ⊥) (hfix : ∀ c ∈ Eb, ∀ y ∈ J, c y = y) : False := by
  classical
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  haveI : CharP K 2 := CFSG.HardMathSupport.Dickson.Bal207.charP_two_of_card_eight hK8
  have hF4 : 4 ≤ Nat.card K := by rw [hK8]; norm_num
  have hinj := CFSG.RankThree.PartOne.KCSpFull.spConj_injective Nat.prime_two (by norm_num) hK
    le_rfl (fun h => by omega)
  let ψ : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
    MulEquiv.ofBijective (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K)
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by norm_num : 1 ≤ 3) hK
  obtain ⟨-, -, -, -, -, hOut, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
      (by norm_num : 1 ≤ 3) hFr hord hzp
  obtain ⟨γ, hγ1, hγE⟩ : ∃ γ : StatedProj (StatedSp 2 K), γ ≠ 1 ∧ MulAut.conj γ ∈ Eb := by
    by_contra hno
    push Not at hno
    haveI : Finite (Outer (StatedProj (StatedSp 2 K))) :=
      Nat.finite_of_card_ne_zero (by rw [hOut]; norm_num)
    have hf : Function.Injective
        ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (StatedProj (StatedSp 2 K)))).comp Eb.subtype) := by
      rw [injective_iff_map_eq_one]
      intro c hc
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
      obtain ⟨g, hg⟩ := hc
      by_cases hg1 : g = 1
      · exact Subtype.ext (by rw [Subgroup.coe_one, ← Subgroup.coe_subtype, ← hg, hg1, map_one])
      · exact absurd (by rw [hg]; exact c.2) (hno g hg1)
    have h6 := Nat.card_le_card_of_injective _ hf
    rw [hOut] at h6
    omega
  have hγ3 : γ ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact hE3 _ hγE)
  have hJC : J ≤ Subgroup.centralizer {γ} := fun y hy => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix _ hγE y hy
    rw [MulAut.conj_apply] at h
    calc y * γ = γ * y * γ⁻¹ * γ := by rw [h]
      _ = γ * y := by group
  obtain ⟨eL⟩ :=
    CFSG.RankThree.PartTwo.KFacts.nonempty_perfectResidual_centralizer_mulEquiv_sl2_of_pow_three
      hF4 ψ hγ3 hγ1
  set L := CFSG.inSubgroup CFSG.perfectResidual (Subgroup.centralizer {γ}) with hL
  have hJL : J ≤ L :=
    CFSG.RankThree.PartOne.EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect hJC
      (Subgroup.isPerfect_iff.2 hJ)
  have hLJ : L ≤ J := by
    haveI := CFSG.Adapters.certificate43_holds
    let _ : Fintype K := Fintype.ofFinite K
    let _ : Fintype (GaloisField 2 3) := Fintype.ofFinite _
    have hcard : Fintype.card K = Fintype.card (GaloisField 2 3) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK8,
        GaloisField.card 2 3 (by norm_num)]
      norm_num
    have hmin := CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_of_ne_top_of_mulEquiv
      ((eL.trans (CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
        (FiniteField.ringEquivOfCardEq hcard))).trans
        (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 3)).symm)
      (CFSG.SignalizerFunctorTheorem.CatalogBridge.proper_subgroup_solvable_psl2_even
        Nat.prime_three ⟨1, rfl⟩)
    have hJ'perf : ⁅J.subgroupOf L, J.subgroupOf L⁆ = J.subgroupOf L := by
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJL, hJ]
    have hJ'1 : J.subgroupOf L ≠ ⊥ := fun h => hJ1 (by
      rw [← Subgroup.map_subgroupOf_eq_of_le hJL, h, Subgroup.map_bot])
    exact Subgroup.subgroupOf_eq_top.1
      (CFSG.SignalizerFunctorTheorem.CatalogBridge.eq_top_of_isPerfect_of_ne_bot hmin hJ'perf hJ'1)
  have hE₀C : Eb.comap MulAut.conj ≤ Subgroup.centralizer {γ} := fun g hg => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm _ (Subgroup.mem_comap.1 hg) _ hγE
  have hE₀3 : ∀ y ∈ Eb.comap MulAut.conj, y ^ 3 = 1 := fun y hy =>
    hinj (by rw [map_pow, map_one]; exact hE3 _ (Subgroup.mem_comap.1 hy))
  have hle3 := CFSG.RankThree.PartTwo.KFacts.card_le_three_mul_card_inf_perfectResidual hF4 ψ
    hγ3 hγ1 hE₀C hE₀3
  rw [← hL] at hle3
  have hbot : Eb.comap MulAut.conj ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgE, hgL⟩ := Subgroup.mem_inf.1 hg
    have hgc : ∀ l : ↥L, (⟨g, hgL⟩ : ↥L) * l = l * ⟨g, hgL⟩ := fun l => Subtype.ext (by
      have h := hfix _ (Subgroup.mem_comap.1 hgE) l (hLJ l.2)
      rw [MulAut.conj_apply] at h
      show g * (l : StatedProj (StatedSp 2 K)) = l * g
      calc g * (l : StatedProj (StatedSp 2 K)) = g * l * g⁻¹ * g := by group
        _ = l * g := by rw [h])
    have hz : eL ⟨g, hgL⟩ ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨l, rfl⟩ := eL.surjective s
      rw [← map_mul, ← map_mul, hgc l]
    rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.mem_bot] at hz
    have h1 : (⟨g, hgL⟩ : ↥L) = 1 := eL.injective (by rw [hz, map_one])
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  rw [hbot, Subgroup.card_bot, mul_one] at hle3
  have hSL : Nat.card SL(2, K) = 504 := by
    let _ : Fintype K := Fintype.ofFinite K
    rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hK8]
    rfl
  have hinn : ∀ θ ∈ Eb,
      θ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) := by
    intro θ hθ
    by_contra hout
    obtain ⟨σ, h, hσ, hθh⟩ :=
      CFSG.HardMathSupport.Dickson.Bal207.outer_conj_fieldAut_eight le_rfl hK8 (hE3 θ hθ) hout
    obtain ⟨-, -, -, -, -, hfixpt, -, -, hS6, -⟩ :=
      symplectic_prime_subfield_fixed_group_and_full_centralizer_odd
        (K := K) Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) (by norm_num) le_rfl
        hK σ hσ
    obtain ⟨-, -, h720⟩ := hS6 ⟨rfl, by norm_num⟩
    have hmap : L.map (h⁻¹).toMonoidHom ≤
        CFSG.RankThree.CASymplecticSubfield.subfieldFixedGroup K 2 σ := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hfixpt]
      have h1 := hfix θ hθ y (hLJ hy)
      rw [hθh, MulAut.mul_apply, MulAut.mul_apply] at h1
      exact h.injective (h1.trans (MulAut.apply_inv_self _ h y).symm)
    have hdvd := Subgroup.card_dvd_of_le hmap
    rw [Subgroup.card_map_of_injective (h⁻¹).injective, h720, Nat.card_congr eL.toEquiv,
      hSL] at hdvd
    exact absurd hdvd (by norm_num)
  have heq : Eb = (Eb.comap MulAut.conj).map MulAut.conj := by
    refine le_antisymm (fun c hc => ?_) (Subgroup.map_comap_le _ _)
    obtain ⟨g, rfl⟩ := hinn c hc
    exact ⟨g, hc, rfl⟩
  have hcardE := Subgroup.card_map_of_injective (K := Eb.comap MulAut.conj) hinj
  rw [← heq] at hcardE
  omega

theorem spFourEight_false_of_fix {M : Type} [Group M] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) (e : M ≃* StatedProj (StatedSp 2 K)) {Eb : Subgroup (MulAut M)}
    (hcomm : ∀ a ∈ Eb, ∀ c ∈ Eb, a * c = c * a) (hE3 : ∀ c ∈ Eb, c ^ 3 = 1)
    (h9 : 9 ≤ Nat.card Eb) {J : Subgroup M} (hJ : ⁅J, J⁆ = J) (hJ1 : J ≠ ⊥)
    (hfix : ∀ c ∈ Eb, ∀ y ∈ J, c y = y) : False := by
  refine spFourEight_false_of_fix_proj hK (Eb := Eb.map (MulAut.congr e).toMonoidHom)
    ?_ ?_ ?_ (J := J.map e.toMonoidHom) ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha c hc]
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, hE3 c hc, map_one]
  · rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective]
  · rw [← Subgroup.map_commutator, hJ]
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨y, hy, rfl⟩
    show (MulAut.congr e c) (e y) = e y
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hfix c hc y hy]

end CFSG.LocalAnalysis.GLTheoremA.S265

end
