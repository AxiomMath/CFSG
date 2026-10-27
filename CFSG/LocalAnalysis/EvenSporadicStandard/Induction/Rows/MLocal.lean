module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CentralizerQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HLambda
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSStd
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocGen
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.Open.MonsterY443Defs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Walter.JRFacts
public import Certificates.Certificate3085Base

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Open CFSG.Monster.Existence CFSG.Blueprint CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

@[expose] def IsMPairShape (P : PairClass) : Prop :=
  ∀ (H : Type) [Group H] (L K : Subgroup H) (u : H), P H L K u →
    u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ 2 * monsterBabyOrder ≤ Nat.card K

theorem sol78Local39Q_of_monsterFacts {P : PairClass} (hP : IsMPairShape P)
    (hmult : OddMultTrivial .M)
    (hM : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .M → MonsterFacts Y) :
    Sol78Local39Q .M P := by
  intro H _ _ N L K t u hcov hset hPP
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hP H L K u hPP
  have hMf := hM ↥L (hcov.isSporadic_of_mult hmult)
  obtain ⟨hKeq, hKeq', hA, hcoat, hC⟩ := m_pair_data hMf huL hu2 hKL hKu hcard
  let u' : ↥L := ⟨u, huL⟩
  have hu'2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hZK : ∀ z ∈ (center K).map K.subtype, z * z = 1 → z = 1 ∨ z = u := by
    intro z hz _
    obtain ⟨hzK, hzc⟩ := mem_center_map_iff.1 hz
    have hz'C : (⟨z, hKL hzK⟩ : ↥L) ∈ centralizer ({u'} : Set ↥L) := by
      rw [← hKeq']
      exact mem_subgroupOf.2 hzK
    have hcen : (⟨⟨z, hKL hzK⟩, hz'C⟩ : ↥(centralizer ({u'} : Set ↥L))) ∈
        center ↥(centralizer ({u'} : Set ↥L)) := by
      rw [Subgroup.mem_center_iff]
      intro c
      have hcK : (c : ↥L) ∈ K.subgroupOf L := by
        rw [hKeq']
        exact c.2
      exact Subtype.ext (Subtype.ext (hzc _ (mem_subgroupOf.1 hcK)).symm)
    have hmem : (⟨z, hKL hzK⟩ : ↥L) ∈
        (center ↥(centralizer ({u'} : Set ↥L))).map (centralizer ({u'} : Set ↥L)).subtype :=
      ⟨⟨⟨z, hKL hzK⟩, hz'C⟩, hcen, rfl⟩
    rw [hA.2.1] at hmem
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
    rcases zpow_eq_one_or_self_of_orderOf_eq_two hu'2 n with h | h
    · left
      exact congrArg Subtype.val (hn.symm.trans h)
    · right
      exact congrArg Subtype.val (hn.symm.trans h)
  have hKc : Nat.card K = 2 * monsterBabyOrder := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, hKeq', hC]
  have hlt : twoAdic K < twoAdic L := by
    unfold twoAdic
    rw [hKc, hMf.card, factorization_two_double_baby, factorization_two_monsterOrder]
    norm_num
  have hmax := maximal_of_isCoatom_subgroupOf hKL (by rw [hKeq']; exact hcoat)
  have hinn : ∀ α : MulAut ↥K, ∃ c ∈ K, ∀ k : K, ((α k : K) : H) = c * (k : H) * c⁻¹ := by
    intro α
    let ε : ↥K ≃* ↥(centralizer ({u'} : Set ↥L)) :=
      (Subgroup.subgroupOfEquivOfLe hKL).symm.trans (MulEquiv.subgroupCongr hKeq')
    obtain ⟨e⟩ := hA.2.2
    obtain ⟨c, hc⟩ := exists_inner_of_mulEquiv ε
      (@allInner_of_quotient ↥(centralizer ({u'} : Set ↥L)) NativeSporadic.B inferInstance
        inferInstance hA.1 e hMf.baby_allInner) α
    exact ⟨(c : H), c.2, fun k => congrArg Subtype.val (hc k)⟩
  exact sol78Local39Q_of_centralizer_allInner hset huL hKeq hZK hlt hmax hinn

theorem solomonLocalQ_of_monsterFacts {L K : Subgroup H} {u : H} (hcov : OddCover .M L)
    (hM : MonsterFacts ↥L) (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hcard : 2 * monsterBabyOrder ≤ Nat.card K) :
    SolomonLocalQ L K u ∧ twoAdic (autCentralizer L K) ≤ 1 := by
  obtain ⟨hKeq, hKeq', hA, hcoat, hC⟩ := m_pair_data hM huL hu2 hKL hKu hcard
  let u' : ↥L := ⟨u, huL⟩
  have hu'2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hq : CFSG.Open.IsQuasisimple ↥(K.subgroupOf L) := by
    rw [hKeq']
    obtain ⟨e⟩ := hA.2.2
    exact ⟨hA.1.commutator_eq_top, @MulEquiv.isSimpleGroup _ _ _ _ hM.baby_simple e⟩
  have hZ : Nat.card ↥(center ↥(K.subgroupOf L)) = 2 := by
    rw [hKeq', ← Subgroup.card_map_of_injective (centralizer ({u'} : Set ↥L)).subtype_injective,
      hA.2.1, Nat.card_zpowers, hu'2]
  have hzH : u' ∈ K.subgroupOf L := mem_subgroupOf.2 (by
    rw [hKeq]
    exact ⟨huL, mem_centralizer_singleton_iff.2 rfl⟩)
  have hcentC := card_centralizer_le_of_center (subgroupOf_eq_centralizer huL hKeq) hzH hZ.le
  have hout : OutTwo ↥L := outTwo_of_allInner hM.allInner
  refine ⟨?_, ?_⟩
  · exact
    { u_order := hu2
      u_mem := Subgroup.le_normalizer huL
      u_not_central := hcov.not_mem_centralizer_of_orderOf_two huL hu2
      K_le := hKL
      u_mem_centralizer_K := mem_centralizer_iff.2 hKu
      standard_in_L := solStd_of_standardComponentIsStandard
        (standard_subgroupOf_centralizer huL hu2 hKeq hq hZ.le)
      autCentralizer_two := twoAdic_autCentralizer_le hout hcentC }
  · have h1 := twoAdic_autCentralizer_le_of_allInner (L := L) (K := K) (fun α => by
      obtain ⟨g, hg⟩ := hM.allInner α
      exact ⟨g, fun x => by rw [hg]; rfl⟩)
    refine h1.trans ?_
    unfold twoAdic
    have h2 : Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ∣ 2 := by
      have hpos : 0 < Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) :=
        Nat.card_pos
      have : Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) = 1 ∨
          Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) = 2 := by omega
      rcases this with h | h
      · rw [h]; exact one_dvd _
      · rw [h]
    have h3 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by norm_num)).2 h2 2
    simpa [Nat.Prime.factorization Nat.prime_two] using h3

theorem sol78SettingLocalQ_of_monsterFacts {P : PairClass} (hP : IsMPairShape P)
    (hmult : OddMultTrivial .M)
    (hM : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .M → MonsterFacts Y) :
    Sol78SettingLocalQ .M P P := by
  intro H _ _ L K u hcov hPP
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hP H L K u hPP
  exact ⟨(solomonLocalQ_of_monsterFacts hcov (hM ↥L (hcov.isSporadic_of_mult hmult)) huL hu2 hKL
    hKu hcard).1, hPP⟩

theorem lemma36DataQ_of_monsterFacts {P : PairClass} (hP : IsMPairShape P)
    (hmult : OddMultTrivial .M)
    (hM : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .M → MonsterFacts Y)
    (hfix : ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover .M L →
      P H L K u → InvolutionFixesElem ↥K 8) : Lemma36DataQ .M P 1 8 := by
  refine ⟨by norm_num, ?_⟩
  intro H _ _ L K u hcov hPP
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hP H L K u hPP
  have hMf := hM ↥L (hcov.isSporadic_of_mult hmult)
  obtain ⟨hKeq, hKeq', hA, hcoat, hC⟩ := m_pair_data hMf huL hu2 hKL hKu hcard
  obtain ⟨-, hta⟩ := solomonLocalQ_of_monsterFacts hcov hMf huL hu2 hKL hKu hcard
  let u' : ↥L := ⟨u, huL⟩
  have hu'2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hZ : Nat.card ↥(center ↥(K.subgroupOf L)) = 2 := by
    rw [hKeq', ← Subgroup.card_map_of_injective (centralizer ({u'} : Set ↥L)).subtype_injective,
      hA.2.1, Nat.card_zpowers, hu'2]
  have hzH : u' ∈ K.subgroupOf L := mem_subgroupOf.2 (by
    rw [hKeq]
    exact ⟨huL, mem_centralizer_singleton_iff.2 rfl⟩)
  have hcentC := card_centralizer_le_of_center (subgroupOf_eq_centralizer huL hKeq) hzH hZ.le
  have hout : OutTwo ↥L := outTwo_of_allInner hMf.allInner
  let ε : ↥K ≃* ↥(centralizer ({u'} : Set ↥L)) :=
    (Subgroup.subgroupOfEquivOfLe hKL).symm.trans (MulEquiv.subgroupCongr hKeq')
  obtain ⟨e⟩ := hA.2.2
  have hq : CFSG.IsQuasisimple ↥(centralizer ({u'} : Set ↥L)) :=
    @isQuasisimple_of_perfect_simple_quotient ↥(centralizer ({u'} : Set ↥L)) NativeSporadic.B
      inferInstance inferInstance hA.1 e hMf.baby_simple
  refine ⟨hu2, ?_, hKeq.le, ?_, CFSG.LocalCores.isQuasisimple_of_mulEquiv ε.symm hq,
    isSolvable_autCentralizer_of_card_le (card_autCentralizer_le hout hcentC), hta,
    hfix H L K u hcov hPP⟩
  · rw [hKeq]
    exact ⟨huL, mem_centralizer_singleton_iff.2 rfl⟩
  · rw [hKeq, Subgroup.subgroupOf_self]
    infer_instance

end CFSG.EvenSporadicStandard.Induction
