module

public import CFSG.LargeExtraspecial.S8CBFMain
public import CFSG.LieType.Chevalley.RootLocalComponentFree
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LieType.Chevalley.TrialityCover
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.CosetTableShort
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
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
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate3085Base
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8026Base
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

local notation "ν" n:max => (⟨n, by decide⟩ : Fin TwistTag.D4.tag.rank)

theorem d4_root_support_check : ∀ l ∈ TwistTag.D4.tag.artifactRoots, 2 ≤ l.sum →
    l.getD 2 0 ≠ 0 ∧ (l.getD 0 0 ≠ 0 ∨ l.getD 1 0 ≠ 0 ∨ l.getD 3 0 ≠ 0) := by
  decide

theorem d4_root_support_of_two_le_height
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α) (h2 : 2 ≤ height α) :
    α (ν 2) ≠ 0 ∧ (α (ν 0) ≠ 0 ∨ α (ν 1) ≠ 0 ∨ α (ν 3) ≠ 0) := by
  have h := d4_root_support_check _ (isRoot_iff_mem_artifactRoots.1 hα)
    (by rw [List.sum_ofFn]; exact h2)
  have e : ∀ (i : ℕ) (hi : i < TwistTag.D4.tag.rank), (List.ofFn α).getD i 0 = α ⟨i, hi⟩ :=
    fun i hi => by rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  rwa [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)] at h

theorem commutator_le_of_le {G : Type*} [Group G] {X H : Subgroup G} (hXH : X ≤ H) :
    ⁅X, X⁆ ≤ H := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (hXH ha) (hXH hb)) (inv_mem (hXH ha))) (inv_mem (hXH hb))

theorem heightSeries_two_le_parabolicRadical
    (K : Type*) [Field K]
    {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    heightSeries TwistTag.D4.tag K 2 ≤
      parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) := by
  refine rootSpan_mono fun α hα => ⟨⟨hα.1, hα.2.1⟩, fun hP => ?_⟩
  obtain ⟨h2, hout⟩ := d4_root_support_of_two_le_height hα.1 hα.2.2
  have hsupp : ∀ i ∉ TwistTag.D4.orbitUnion J, α i = 0 := hP.1.2
  obtain ⟨a, ha⟩ : ∃ a, a ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩ := by
    decide
  rcases hcases a with rfl | rfl
  · refine hout.elim (fun h => h (hsupp _ ?_)) (Or.elim · (fun h => h (hsupp _ ?_))
      (fun h => h (hsupp _ ?_))) <;>
    · rw [mem_orbitUnion_iff_orbitIndex]
      exact ha
  · exact h2 (hsupp _ (by rw [mem_orbitUnion_iff_orbitIndex]; exact ha))

theorem commutator_graphFixedPosUnipotent_le
    (K : Type) [Field K]
    (σ : K →+* K) {J : Set (Fin TwistTag.D4.foldedTag.rank)} (hJ : J ≠ Set.univ) :
    ⁅graphFixedPosUnipotent TwistTag.D4 K σ, graphFixedPosUnipotent TwistTag.D4 K σ⁆ ≤
      graphFixedParabolicRadical TwistTag.D4 K σ J := by
  refine le_inf ?_ (commutator_le_of_le (graphFixedPosUnipotent_le TwistTag.D4 K σ))
  calc ⁅graphFixedPosUnipotent TwistTag.D4 K σ, graphFixedPosUnipotent TwistTag.D4 K σ⁆
      ≤ ⁅posUnipotent TwistTag.D4.tag K, posUnipotent TwistTag.D4.tag K⁆ :=
        commutator_mono inf_le_left inf_le_left
    _ = ⁅heightSeries TwistTag.D4.tag K 1, heightSeries TwistTag.D4.tag K 1⁆ := by
        rw [heightSeries_one]
    _ ≤ heightSeries TwistTag.D4.tag K (1 + 1) := commutator_heightSeries_le K 1 1
    _ ≤ parabolicRadical TwistTag.D4.tag K (TwistTag.D4.orbitUnion J) :=
        heightSeries_two_le_parabolicRadical K hJ

theorem commutator_le_graphFixedParabolicRadical
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.D4.order = 1) {J : Set (Fin TwistTag.D4.foldedTag.rank)}
    (hJ : J ≠ Set.univ) {X : Subgroup (ModGL TwistTag.D4.tag K)}
    (hXP : X ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom J) (hX2 : IsPGroup 2 X) :
    ⁅X, X⁆ ≤ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  set D : RootWeightDatum K := .fixed TwistTag.D4 σ hσ with hD
  set P := graphFixedParabolic TwistTag.D4 K σ.toRingHom J with hPdef
  set U₀ := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom with hU₀
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hUP : U₀ ≤ P := graphFixedPosUnipotent_le_graphFixedRootBorel.trans
    (graphFixedRootBorel_le_graphFixedParabolic _ _ _ J)
  have hPC : P ≤ C := graphFixedParabolic_le _ _ _ J
  obtain ⟨S, hS⟩ := D.exists_sylow_eq_unipotent 2
  have hodd : ¬ 2 ∣ (U₀.subgroupOf P).index := by
    have h1 : ¬ 2 ∣ (U₀.subgroupOf C).index := by
      have h := S.not_dvd_index
      rw [hS] at h
      exact h
    intro h2
    apply h1
    have e := relIndex_mul_relIndex U₀ P C hUP hPC
    change (U₀.subgroupOf P).index * (P.subgroupOf C).index = (U₀.subgroupOf C).index at e
    rw [← e]
    exact dvd_mul_of_dvd_left h2 _
  obtain ⟨y, hyP, hy⟩ := exists_conj_le_of_not_dvd_index hXP hX2 hodd
  have hyc : ∀ x ∈ X, y * x * y⁻¹ ∈ U₀ := fun x hx => hy ⟨x, hx, rfl⟩
  rw [commutator_le]
  intro a ha b hb
  have hab : y * ⁅a, b⁆ * y⁻¹ ∈ graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J := by
    have e : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact commutator_graphFixedPosUnipotent_le K σ.toRingHom hJ
      (commutator_mem_commutator (hyc a ha) (hyc b hb))
  have h : y⁻¹ * (y * ⁅a, b⁆ * y⁻¹) * y⁻¹⁻¹ ∈
      graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J :=
    D.conj_mem_radical J (show y⁻¹ ∈ D.parabolic J from inv_mem hyP) hab
  have e : y⁻¹ * (y * ⁅a, b⁆ * y⁻¹) * y⁻¹⁻¹ = ⁅a, b⁆ := by group
  rwa [e] at h

theorem exists_centralizer_le_graphFixedParabolic
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.D4.order = 1) {s : ModGL TwistTag.D4.tag K}
    (hsC : s ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hs : orderOf s = 2) :
    ∃ g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      ∃ J : Set (Fin TwistTag.D4.foldedTag.rank), J ≠ Set.univ ∧
        ∀ x ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ centralizer ({s} : Set _),
          g⁻¹ * x * g ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hQC : zpowers s ≤ C := zpowers_le.2 hsC
  have hQp : IsPGroup 2 (zpowers s) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hs, pow_one]
  have hQ : zpowers s ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hs
    exact absurd hs (by norm_num)
  obtain ⟨M, -, -, -, F, -, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    RootWeightDatum.root_p_subgroup_optimal_parabolic_containment
      (RootWeightDatum.fixed TwistTag.D4 σ hσ : RootWeightDatum K) 2 (zpowers s) hQC hQp hQ
  obtain ⟨hJ, -, hN, hset, -⟩ := hdom g hg l hl hl1 hgl
  obtain ⟨g', rfl⟩ : ∃ g' : ModGL TwistTag.D4.tag K, g' = g := ⟨g, rfl⟩
  set J : Set (Fin TwistTag.D4.foldedTag.rank) :=
    (RootWeightDatum.fixed TwistTag.D4 σ hσ : RootWeightDatum K).face l
  change {x : ModGL TwistTag.D4.tag K | x ∈ C ∧
      ∀ c : ℝ, (F c).map (x : Module.End K (RootModule TwistTag.D4.tag K)) = F c} =
    ((graphFixedParabolic TwistTag.D4 K σ.toRingHom J).map (MulAut.conj g').toMonoidHom :
      Set (ModGL TwistTag.D4.tag K)) at hset
  refine ⟨g', hg, J, hJ, fun x hx => ?_⟩
  obtain ⟨hxC, hxs⟩ := mem_inf.1 hx
  have hxN : x ∈ normalizer (zpowers s : Set (ModGL TwistTag.D4.tag K)) := by
    have hc : centralizer ((zpowers s : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) = centralizer ({s} : Set (ModGL TwistTag.D4.tag K)) := by
      rw [zpowers_eq_closure, centralizer_closure]
    exact centralizer_le_normalizer _ (hc ▸ hxs)
  have hmem := (Set.ext_iff.1 hset x).1 ⟨hxC, hN x (mem_inf.2 ⟨hxC, hxN⟩)⟩
  rw [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hmem
  exact hmem

theorem relNormalTwoDatum_graphFixedRootGroup_D4
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.D4.order = 1) {s : ModGL TwistTag.D4.tag K}
    (hsC : s ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hs : orderOf s = 2) :
    RelNormalTwoDatum (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, J, hJ, hCP⟩ := exists_centralizer_le_graphFixedParabolic σ hσ hsC hs
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set Q₀ := graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom J with hQ₀
  set D : RootWeightDatum K := .fixed TwistTag.D4 σ hσ with hD
  have hQ₀2 : IsPGroup 2 Q₀ := D.isPGroup_radical 2 J
  refine ⟨Q₀.map (MulAut.conj g).toMonoidHom ⊓ (C ⊓ centralizer ({s} : Set _)), inf_le_right,
    fun c hc q hq => mem_inf.2 ⟨?_, mul_mem (mul_mem hc (mem_inf.1 hq).2) (inv_mem hc)⟩,
    (hQ₀2.map _).to_inf_left, fun P hP hP2 => le_inf ?_ (commutator_le_of_le hP)⟩
  · obtain ⟨q₀, hq₀, hq₀q⟩ := (mem_inf.1 hq).1
    have hq₀q' : g * q₀ * g⁻¹ = q := hq₀q
    have h1 : (g⁻¹ * c * g) * q₀ * (g⁻¹ * c * g)⁻¹ ∈ Q₀ :=
      D.conj_mem_radical J (show g⁻¹ * c * g ∈ D.parabolic J from hCP c hc) hq₀
    refine ⟨_, h1, ?_⟩
    rw [← hq₀q', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · have hP' : P.map (MulAut.conj g⁻¹).toMonoidHom ≤
        graphFixedParabolic TwistTag.D4 K σ.toRingHom J := by
      rintro _ ⟨x, hx, rfl⟩
      have h := hCP x (hP hx)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact h
    have h1 := commutator_le_graphFixedParabolicRadical σ hσ hJ hP' (hP2.map _)
    have h2 := map_mono (f := (MulAut.conj g).toMonoidHom) h1
    rw [map_commutator, map_map] at h2
    have hid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rwa [hid, map_id] at h2

theorem normalTwoDatum_graphFixedRootGroup_D4
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.D4.order = 1) {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : orderOf s = 2) : NormalTwoDatum s :=
  normalTwoDatum_of_rel (relNormalTwoDatum_graphFixedRootGroup_D4 σ hσ s.2
    (by rw [orderOf_coe, hs]))

theorem corBSectResidual :
    CorBSectResidual := by
  intro Y _ _ ⟨f, h⟩
  have hce : ChevalleyExceptionalModel Y .trialityD4 2 f := by
    rcases h with ⟨hcl, -⟩ | ⟨-, -, hce⟩ | ⟨-, hree, -⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact hce
    · exact absurd hree (by decide)
    · exact absurd hsz (by decide)
  obtain ⟨⟨-, hf, -⟩, hU⟩ := hce
  obtain ⟨K, _, _, _, σ, hσ, -, -, -, ⟨e⟩⟩ := TrialityCover.triality_model hf hU
  refine invCentSectAbelianSylow_of_normalTwoDatum fun y hy => NormalTwoDatum.of_mulEquiv e ?_
  exact normalTwoDatum_graphFixedRootGroup_D4 σ hσ (by rw [MulEquiv.orderOf_eq, hy])

end CFSG.LargeExtraspecial.S8
