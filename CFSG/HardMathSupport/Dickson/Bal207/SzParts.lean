module

public import CFSG.HardMathSupport.Dickson.Bal207.Sz
public import CFSG.HardMathSupport.Dickson.Bal207.Center
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Certificates.Certificate113
import CFSG.LieType.Suzuki.SuzukiOuterCyclic
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Dickson.I271.I202Full
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Generic.Certificates
import CFSG.GH74.Statements
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.Assembly.LowTwoRank
  CFSG.Blueprint.Multiplier CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def Bal207SzNorm : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Blueprint.SuzukiModel G 2 5 →
    ∀ k : G, k ^ 5 = 1 → k ≠ 1 → ∀ S : Subgroup G, Nat.Coprime 5 (Nat.card S) →
      k ∈ Subgroup.normalizer (S : Set G) → S = ⊥

theorem szAux_index {d : TauCeti.ValidLieTypeIndex} (hd : IsSuzuki2Index d.1) :
    ∃ hv : (TauCeti.LieTypeIndex.suzuki 2).Valid, d = ⟨.suzuki 2, hv⟩ := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | suzuki m =>
    simp only [IsSuzuki2Index] at hd
    subst hd
    exact ⟨hv, rfl⟩
  | _ => exact absurd hd (by simp [IsSuzuki2Index])

theorem szAux_suzukiModel {S : Type} [Group S] {hv : (TauCeti.LieTypeIndex.suzuki 2).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group) :
    CFSG.Blueprint.SuzukiModel S 2 5 := by
  have hK : Nat.card (GaloisField 2 (2 * 2 + 1)) = 2 ^ (2 * 2 + 1) :=
    GaloisField.card 2 (2 * 2 + 1) (by omega)
  exact ⟨rfl, 2, by omega, GaloisField 2 (2 * 2 + 1), inferInstance, inferInstance, rfl, hK,
    ⟨e.trans ((CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).trans
      (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).symm)⟩⟩

theorem szAux_eq_bot_of_coprime {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ r : ℕ, r.Prime → Nat.Coprime r (Nat.card H)) : H = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  by_contra hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  exact (Nat.Prime.coprime_iff_not_dvd hr).mp (h r hr) hrd

theorem szAux_center_eq_bot (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hK : IsLieQuot K IsSuzuki2Index) :
    Subgroup.center K = ⊥ := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  obtain ⟨hv, rfl⟩ := szAux_index hd
  have hL := lieModel_lie (t := .twistedB2) (p := 2) (f := 2 * 2 + 1)
    ⟨Nat.prime_two, by omega, rfl, rfl, ⟨2, rfl⟩, by omega⟩ ⟨.suzuki 2, hv⟩ ⟨rfl, rfl⟩
  apply szAux_eq_bot_of_coprime
  intro r hr
  have hg : genericOrders .twistedB2 0 2 (2 * 2 + 1) = (1, 1) := by simp [genericOrders]
  have he : exceptionalOrders .twistedB2 0 2 (2 * 2 + 1) = (1, 1) := rfl
  have ht : tors r 1 = 1 := tors_of_not_dvd hr.not_dvd_one
  have hb : torsBound r .twistedB2 0 2 (2 * 2 + 1) = 1 := by
    simp only [torsBound, hg, he, ht]
  exact centerAux_coprime_of_card_le_one hr ((center_torsion_le hGA hq e hL hr).trans hb.le)

theorem szAux_card_outer_dvd {K : Type} [Group K]
    (hq : CFSG.Open.IsQuasisimple K) {hv : (TauCeti.LieTypeIndex.suzuki 2).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group) :
    Nat.card (Outer K) ∣ 5 := by
  have hM : CFSG.Blueprint.SuzukiModel (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group 2 5 :=
    szAux_suzukiModel (MulEquiv.refl _)
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  exact ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity _ 2 _ hM).2 K ⟨e⟩).2.1

theorem szAux_five_dvd_card {K : Type} [Group K] [Finite K]
    {hv : (TauCeti.LieTypeIndex.suzuki 2).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group) :
    5 ∣ Nat.card K := by
  obtain ⟨-, a, -, F, _, _, hf, hF, ⟨e'⟩⟩ := szAux_suzukiModel (hv := hv) (MulEquiv.refl _)
  have ha : a = 2 := by omega
  subst ha
  have h1 : Nat.card (K ⧸ Subgroup.center K) = 32537600 := by
    rw [Nat.card_congr (e.trans e').toEquiv, CFSG.LieType.Ree.suzuki_order hF]
    norm_num
  have h2 : 5 ∣ Nat.card (K ⧸ Subgroup.center K) := by
    rw [h1]
    norm_num
  exact h2.trans (Subgroup.card_quotient_dvd_card _)

theorem szAux_le_inner {K : Type*} [Group K] (hO : Nat.card (Outer K) ∣ 5)
    {T : Subgroup (MulAut K)} (hT : Nat.Coprime 5 (Nat.card T)) :
    T ≤ (MulAut.conj : K →* MulAut K).range := by
  let π : MulAut K →* Outer K := QuotientGroup.mk' (inner K)
  have h1 : Nat.card (T.map π) ∣ Nat.card T := Subgroup.card_map_dvd T π
  have h2 : Nat.card (T.map π) ∣ 5 := (Subgroup.card_subgroup_dvd_card _).trans hO
  have h3 : Nat.card (T.map π) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hT) h1
  have h4 := Subgroup.eq_bot_of_card_eq _ h3
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h4
  exact h4

theorem bal207SzAut_of_norm (hGA : GriessAllModelsStatement)
    (hN : Bal207SzNorm) : Bal207SzAut := by
  intro K _ _ hq hK α hα hfix T hT5 hαT
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have hZ : Subgroup.center K = ⊥ := szAux_center_eq_bot hGA hq hK
  have hZc : Nat.Coprime 5 (Nat.card (Subgroup.center K)) := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  obtain ⟨hv, rfl⟩ := szAux_index hd
  have h5 : 5 ∣ Nat.card K := szAux_five_dvd_card e
  have hin : α ∈ (MulAut.conj : K →* MulAut K).range := by
    by_contra hout
    obtain ⟨y, hy5, hyα, hyn⟩ := rankAux_fix_outer hp hZc h5 α hα hout
    exact hyn (hfix y hy5 hyα)
  obtain ⟨k, rfl⟩ := hin
  have hk5 : k ^ 5 = 1 := by
    have h1 : MulAut.conj (k ^ 5) = 1 := by rw [map_pow]; exact hα
    have h2 := rankAux_mem_center_of_conj_eq_one h1
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hk1 : k ≠ 1 := by
    rintro rfl
    haveI := Fact.mk hp
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
    have h1 := hfix y (hy ▸ pow_orderOf_eq_one y) (by simp)
    rw [map_one, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h1
    exact rankAux_conj_ne_one hp hZc hy h1
  have hTinn : T ≤ (MulAut.conj : K →* MulAut K).range :=
    szAux_le_inner (szAux_card_outer_dvd hq e) hT5
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := rankAux_mem_center_of_conj_eq_one ha
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  set S : Subgroup K := T.comap (MulAut.conj : K →* MulAut K) with hS
  have hST : S.map (MulAut.conj : K →* MulAut K) = T := Subgroup.map_comap_eq_self hTinn
  have hSc : Nat.card S = Nat.card T := by
    rw [← hST, Subgroup.card_map_of_injective hinj]
  have hkS : k ∈ Subgroup.normalizer (S : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    simp only [hS, SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hαT) (MulAut.conj s)
  have hM : CFSG.Blueprint.SuzukiModel K 2 5 :=
    szAux_suzukiModel (((QuotientGroup.quotientBot (G := K)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e)
  have hSbot := hN K hM k hk5 hk1 S (hSc ▸ hT5) hkS
  rw [← hST, hSbot, Subgroup.map_bot]

theorem bal207SzCyclic_of_norm (hGA : GriessAllModelsStatement)
    (hN : Bal207SzNorm) : Bal207SzCyclic :=
  bal207SzCyclic_of_aut (bal207SzAut_of_norm hGA hN)

end CFSG.HardMathSupport.Dickson.Bal207
