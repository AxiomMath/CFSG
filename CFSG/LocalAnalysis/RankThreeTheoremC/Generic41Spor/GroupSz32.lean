module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialCases
public import Certificates.Certificate43
public import Certificates.Certificate113
public import Certificates.Certificate9530
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupBridge
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigSzCore
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local
import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
import CFSG.RankThree.PartOne.KP.SporadicDefs
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.RankThree.PartOne.K159.AutSzIso
import CFSG.RankThree.PartOne.K159.AutSzAbs
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial (SignalizerTrivialOn)

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

@[expose] def NormalizerTransitiveOmega (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, ∀ a ∈ (S : Subgroup K), orderOf a = p → ∀ b ∈ (S : Subgroup K), orderOf b = p →
    ∃ n ∈ normalizer ((S : Subgroup K) : Set K), n * a * n⁻¹ = b

structure Sz32Facts : Prop where
  sylow : ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → SylowIsCyclicSq 5 K
  outer : ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → OutIsOrderP 5 K
  sigTriv : SignalizerTrivialX IsSz32Type 5

structure Sz32OpenFacts : Prop where
  transOmega : ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → NormalizerTransitiveOmega 5 K
  maximal : ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → NormalizerMaximal 5 K
  lemma45 : Lemma45Facts IsSz32Type 5 Sz32Shape

theorem sz32_sylow :
    ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → SylowIsCyclicSq 5 K := by
  intro K _ _ hK
  unfold SylowIsCyclicSq
  intro S
  obtain ⟨-, hiso⟩ := hK
  obtain ⟨hv, ⟨eK⟩⟩ := hiso
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have eKS := eK.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)
  have hKcard : Nat.card K = 32537600 := by
    rw [Nat.card_congr eKS.toEquiv,
      CFSG.BenderSuzuki.lemma114_suzukiMatrixGroup_card_formula 2 (by norm_num)]
    norm_num
  constructor
  · exact CFSG.BenderSuzuki.lemma114_suzuki_oddSylow_isCyclic_of_equiv eKS 5 (by norm_num) S
  · rw [Sylow.card_eq_multiplicity, hKcard,
      CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]

theorem sz32_outer :
    ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → OutIsOrderP 5 K := by
  intro K _ _ hK
  obtain ⟨-, hiso⟩ := hK
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  obtain rfl : a = 2 := by omega
  have hsplit := CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting 2 ha F hF
  have hOuterF : Nat.card (Outer (CFSG.Blueprint.suzukiGroup 2 F)) = 2 * 2 + 1 :=
    hsplit.2.2.2.2.2.1
  have hOuterK : Nat.card (Outer K) = Nat.card (Outer (CFSG.Blueprint.suzukiGroup 2 F)) :=
    CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv eF
  show Nat.card (Outer K) = 5
  omega

theorem sz32_signalizerOn :
    ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → SignalizerTrivialOn 5 K := by
  intro K _ _ hK
  have hK0 := hK
  obtain ⟨-, hiso⟩ := hK
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hmodel := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have hsimple : IsSimpleGroup K := by
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  obtain rfl : a = 2 := by omega
  let σ : F ≃+* CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    CFSG.AGLEmbedding.KFactProofs.Sz32.F32.ringEquiv F hF'
  let ε : K ≃* CFSG.Blueprint.suzukiGroup 2 CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    eF.trans (CFSG.AGLEmbedding.KFactProofs.Sz32Local.modelEquiv σ)
  have hC : ∀ T : Sylow 5 K, ∀ t ∈ (T : Subgroup K), t ≠ 1 → ∀ g : K, g * t = t * g →
      g ∈ (T : Subgroup K) := fun T =>
    CFSG.AGLEmbedding.KFactProofs.Sz32Local.centralizer_le_of_equiv ε T
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  have hcinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer.conj_injective hSz hsimple
  have hOutK : Nat.card (Outer K) = 5 := sz32_outer K hK0
  have hOut : Nat.card (MulAut K ⧸ Inn K) ∣ 5 := dvd_of_eq hOutK
  intro P W hW hnorm
  have hWK : W ≤ Inn K := by
    intro y hy
    have h1 : orderOf (QuotientGroup.mk' (Inn K) y) ∣ Nat.card W :=
      (orderOf_map_dvd (QuotientGroup.mk' (Inn K)) y).trans (Subgroup.orderOf_dvd_natCard W hy)
    have h2 : orderOf (QuotientGroup.mk' (Inn K) y) ∣ 5 :=
      (_root_.orderOf_dvd_natCard (QuotientGroup.mk' (Inn K) y)).trans hOut
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hW.symm) h2
    exact (QuotientGroup.eq_one_iff y).1 (orderOf_eq_one_iff.1 h3)
  set W' : Subgroup K := W.comap (MulAut.conj : K →* MulAut K) with hW'def
  have hmapW : W'.map (MulAut.conj : K →* MulAut K) = W := Subgroup.map_comap_eq_self hWK
  have hW'card : Nat.card W' = Nat.card W := by
    have := Subgroup.card_map_of_injective (f := (MulAut.conj : K →* MulAut K)) (K := W') hcinj
    rw [hmapW] at this
    exact this.symm
  have hW'norm : ∀ g ∈ (P : Subgroup K), ∀ w ∈ W', g * w * g⁻¹ ∈ W' := by
    intro g hg w hw
    have hw' : MulAut.conj w ∈ W := Subgroup.mem_comap.1 hw
    have key : MulAut.conj g * MulAut.conj w * (MulAut.conj g)⁻¹ ∈ W := hnorm g hg _ hw'
    refine Subgroup.mem_comap.2 ?_
    rw [map_mul, map_mul, map_inv]
    exact key
  have hPcard : Nat.card (P : Subgroup K) = 5 ^ 2 := (sz32_sylow K hK0 P).2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P : Subgroup K)) 5
    (by rw [hPcard]; norm_num)
  have hzord : orderOf (x : K) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hzP : (x : K) ∈ (P : Subgroup K) := x.2
  have hzN : (x : K) ∈ normalizer (W' : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hW'norm _ hzP h hh
    · intro hh
      have h' := hW'norm _ (inv_mem hzP) _ hh
      have e : (x : K)⁻¹ * ((x : K) * h * (x : K)⁻¹) * (x : K)⁻¹⁻¹ = h := by group
      rw [e] at h'
      exact h'
  have hW'cop : ¬ 5 ∣ Nat.card W' := by
    rw [hW'card]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hW
  have hW'bot : W' = ⊥ :=
    CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer.eq_bot_of_normalizes hSz hsimple hC
      hzord hW'cop hzN
  rw [← hmapW, hW'bot, Subgroup.map_bot]

theorem sz32_sigTriv :
    SignalizerTrivialX IsSz32Type 5 :=
  signalizerTrivialX_of_on (by norm_num) sz32_signalizerOn

theorem sz32Facts_holds :
    Sz32Facts :=
  ⟨sz32_sylow, sz32_outer, sz32_sigTriv⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
