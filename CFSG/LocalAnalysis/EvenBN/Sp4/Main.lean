module

public import CFSG.LocalAnalysis.EvenBN.Sp4.OneAxisExclusion
public import CFSG.LocalAnalysis.SteinbergSFFullCenterMutualCommutator
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenBNUnitaryFour
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenBNRankTwoFrontier
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.SymplecticFourStandard GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

@[expose] def SingleCommutatorExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    (∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥) →
    ∀ L : Subgroup G, standardComponentIsStandard L →
    ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
    ∀ T : Sylow 2 (centralizer (L : Set G)), IsCyclic (T : Subgroup (centralizer (L : Set G))) →
    ∀ t : centralizer (L : Set G), t ∈ T → orderOf t = 2 →
    ∀ (P : Sylow 2 L) (φ : L ≃* antiSp K),
      (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K →
    ∀ i : Axis,
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let ZP := (center PG).map PG.subtype
    let U : Axis → Subgroup G := fun k => ((rootU K k).comap φ.toMonoidHom).map L.subtype
    let A : Axis → Subgroup G := fun k => ((rootA K k).comap φ.toMonoidHom).map L.subtype
    let V : Axis → Subgroup G := fun k => zpowers (t : G) ⊔ U k
    let B : Axis → Subgroup G := fun k => zpowers (t : G) ⊔ A k
    let M : Axis → Subgroup G := fun k => normalizer (V k : Set G)
    let N : Axis → Subgroup G := fun k => normalizer (B k : Set G)
    let D : Axis → Subgroup G := fun k => (CFSG.pCore 2 (M k)).map (M k).subtype
    let E : Axis → Subgroup G := fun k => (CFSG.pCore 2 (N k)).map (N k).subtype
    let E₀ := E Axis.one ⊓ E Axis.two
    let J₀ := ((diagTorus K).comap φ.toMonoidHom).map L.subtype
    let F := closure {x : G | ∃ e ∈ E₀, ∃ j ∈ J₀, x = e⁻¹ * (j⁻¹ * e * j)}
    let Fi : Axis → Subgroup G := fun k => F ⊓ D k
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ ZP, x = t * z} →
    ⁅A i, Fi i.swap⁆ ≠ ⊥ → ⁅A i.swap, Fi i⁆ = ⊥ → False

@[expose] def BothTrivialExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    (∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥) →
    ∀ L : Subgroup G, standardComponentIsStandard L →
    ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ n →
    ∀ T : Sylow 2 (centralizer (L : Set G)), IsCyclic (T : Subgroup (centralizer (L : Set G))) →
    ∀ t : centralizer (L : Set G), t ∈ T → orderOf t = 2 →
    ∀ (P : Sylow 2 L) (φ : L ≃* antiSp K),
      (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K →
    let TG := (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype
    let PG := (P : Subgroup L).map L.subtype
    let Q := PG ⊔ TG
    let ZP := (center PG).map PG.subtype
    let U : Axis → Subgroup G := fun k => ((rootU K k).comap φ.toMonoidHom).map L.subtype
    let A : Axis → Subgroup G := fun k => ((rootA K k).comap φ.toMonoidHom).map L.subtype
    let V : Axis → Subgroup G := fun k => zpowers (t : G) ⊔ U k
    let B : Axis → Subgroup G := fun k => zpowers (t : G) ⊔ A k
    let M : Axis → Subgroup G := fun k => normalizer (V k : Set G)
    let N : Axis → Subgroup G := fun k => normalizer (B k : Set G)
    let D : Axis → Subgroup G := fun k => (CFSG.pCore 2 (M k)).map (M k).subtype
    let E : Axis → Subgroup G := fun k => (CFSG.pCore 2 (N k)).map (N k).subtype
    let E₀ := E Axis.one ⊓ E Axis.two
    let J₀ := ((diagTorus K).comap φ.toMonoidHom).map L.subtype
    let F := closure {x : G | ∃ e ∈ E₀, ∃ j ∈ J₀, x = e⁻¹ * (j⁻¹ * e * j)}
    let Fi : Axis → Subgroup G := fun k => F ⊓ D k
    {x : G | ∃ m ∈ normalizer (Q : Set G), x = m⁻¹ * t * m} = {x | ∃ z ∈ ZP, x = t * z} →
    ⁅A Axis.one, Fi Axis.two⁆ = ⊥ → ⁅A Axis.two, Fi Axis.one⁆ = ⊥ → False

theorem standard_simple_setting {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {L : Subgroup G} (hL : standardComponentIsStandard L) {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Field K] [CharP K 2] (hK : Nat.card K = 2 ^ n) (φ : L ≃* antiSp K)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥) :
    standardComponentOddCore G = ⊥ ∧ ¬ L.Normal ∧ Group.IsPerfect G := by
  have hS := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hLn : ¬ L.Normal := by
    intro hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hbot | htop
    · have h1 : ((φ.symm (uElt 1 0 0 0) : L) : G) = 1 :=
        (eq_bot_iff_forall L).mp hbot _ (φ.symm (uElt 1 0 0 0)).2
      rw [OneAxisFusion.coe_symm_eq_one_iff, ← uElt_zero_eq_one] at h1
      exact one_ne_zero (uElt_inj h1).1
    · exact hS.t_not_mem_L ((eq_top_iff' L).mp htop _)
  refine ⟨ComponentInitial.EvenResidual.standardComponentOddCore_eq_bot_of_simple
    (even_iff_two_dvd.2 (hS.order_t ▸ orderOf_dvd_natCard (t : G))), hLn,
    ComponentInitial.EvenResidual.isPerfect_of_simple ?_⟩
  by_contra hab
  exact hLn ⟨fun l hl g => by
    rw [show g * l = l * g from by_contra fun h => hab ⟨g, l, h⟩, mul_inv_cancel_right]
    exact hl⟩

theorem false_of_cross_commutator_cases {X Y : Prop} (hXY : X ∨ Y) (hb : X → Y → False)
    (h₁ : ¬ X → Y → False) (h₂ : ¬ Y → X → False) : False := by
  by_cases hX : X <;> by_cases hY : Y <;> tauto

theorem false_of_sectors_of_setup (hSC : SingleCommutatorExclusion)
    (hBT : BothTrivialExclusion) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hKp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hcore : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥)
    {L : Subgroup G} (hL : standardComponentIsStandard L) {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (P : Sylow 2 L) (φ : L ≃* antiSp K)
    (hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K) : False := by
  have hct : standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥ :=
    hcore _ ((Subgroup.orderOf_coe t).trans ht)
  obtain ⟨hO, hLn, -⟩ := standard_simple_setting hL hn hK φ T hT htT ht hct
  obtain ⟨-, -, -, -, horb⟩ := standard_symplectic_four_normalizer_fusion_orbits hO hL hLn hn hK
    T hT htT ht hct P φ hφP
  rcases horb with h₁ | h₂ | h₀
  · rw [axisOne_eq_rootU] at h₁
    exact false_of_one_axis hL hn hK T hT htT ht hct P φ hφP (Or.inl h₁)
  · rw [axisTwo_eq_rootU] at h₂
    exact false_of_one_axis hL hn hK T hT htT ht hct P φ hφP (Or.inr h₂)
  · exact false_of_cross_commutator_cases
      (standard_symplectic_four_full_center_mutual_commutator_exclusion hO hL hLn hn hK T hT htT
        ht hct P φ hφP h₀)
      (hBT G hKp hcore L hL n hn K hK T hT t htT ht P φ hφP h₀)
      (hSC G hKp hcore L hL n hn K hK T hT t htT ht P φ hφP Axis.one h₀)
      (hSC G hKp hcore L hL n hn K hK T hT t htT ht P φ hφP Axis.two h₀)

theorem false_of_sectors (hSC : SingleCommutatorExclusion)
    (hBT : BothTrivialExclusion) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hKp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hcore : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥)
    {L : Subgroup G} (hL : standardComponentIsStandard L) {n : ℕ} (hn : 2 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) (φ : L ≃* antiSp K) : False := by
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := (T : Subgroup (centralizer (L : Set G))))
    2 (T.dvd_card_of_dvd_card (even_iff_two_dvd.1 hL.2.1))
  obtain ⟨P, hP⟩ := exists_sylow_pull (G := G) φ
  have hφP : (P : Subgroup L).map φ.toMonoidHom = antiUnipotent K := by
    rw [map_injective L.subtype_injective hP, map_comap_eq_self_of_surjective φ.surjective]
  exact false_of_sectors_of_setup hSC hBT hKp hcore hL hn hK T hT s.2
    ((Subgroup.orderOf_coe s).trans hs) P φ hφP

theorem bnFamily_PSp2_of_sectors (hSC : SingleCommutatorExclusion)
    (hBT : BothTrivialExclusion) :
    ComponentInitial.EvenResidual.BNFamilyStatement
      fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSp 2 2 f := by
  intro G _ _ _ _ hKp L hL hcore S hS _ _ ⟨f, hf, hm⟩
  have h2 := ComponentInitial.EvenResidual.isPGroup_two_center hL hcore
  by_contra hodd
  have hZ : center L = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rcases k with _ | k
    · exact Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
    · exact (hodd (by rw [hk]; exact Nat.even_pow.2 ⟨even_two, by omega⟩)).elim
  let e : L ≃* L ⧸ center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hmL : LieModel L .PSp 2 2 f := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  obtain ⟨K, _, _, hK, ⟨ψ⟩⟩ :=
    ComponentInitial.SymplecticCoverFour.exists_mulEquiv_statedSp_of_lieModel hmL
  have : CharP K 2 := charP_two_of_card hK
  exact false_of_sectors hSC hBT hKp hcore hL hf hK S hS (ψ.trans (antiSpEquiv K).symm)

end CFSG.LocalAnalysis.EvenBN.Sp4
