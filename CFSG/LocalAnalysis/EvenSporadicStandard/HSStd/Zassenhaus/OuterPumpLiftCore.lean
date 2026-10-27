module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Section
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Blueprint.OddStandardExact
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Ind
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.OddStandard.ChildHe
public import CFSG.LocalAnalysis.OddStandard.GlueL34
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
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

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup
open scoped commutatorElement

section LiftCore

variable {H X : Type*} [Group H] [Group X]

theorem commutator_self_le (D : Subgroup H) : ⁅D, D⁆ ≤ D := by
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb)

@[expose] def liftCore (φ : H →* X) (K : Subgroup X) : Subgroup H :=
  ⁅K.comap φ, K.comap φ⁆

theorem liftCore_le_comap (φ : H →* X) (K : Subgroup X) : liftCore φ K ≤ K.comap φ :=
  commutator_self_le _

theorem map_liftCore {φ : H →* X} (hφ : Function.Surjective φ) {K : Subgroup X}
    (hK : ⁅K, K⁆ = K) : (liftCore φ K).map φ = K := by
  rw [liftCore, Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hφ, hK]

theorem liftCore_perfect {φ : H →* X} (hφ : Function.Surjective φ) (hker : φ.ker ≤ center H)
    {K : Subgroup X} (hK : ⁅K, K⁆ = K) : ⁅liftCore φ K, liftCore φ K⁆ = liftCore φ K := by
  refine le_antisymm (commutator_self_le _) ?_
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  have hmap := map_liftCore hφ hK
  have hlift : ∀ w ∈ K.comap φ, ∃ d ∈ liftCore φ K, d⁻¹ * w ∈ center H := by
    intro w hw
    have hw' : φ w ∈ (liftCore φ K).map φ := by rw [hmap]; exact hw
    obtain ⟨d, hd, hdw⟩ := hw'
    refine ⟨d, hd, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdw, inv_mul_cancel]
  obtain ⟨dx, hdx, hcx⟩ := hlift x hx
  obtain ⟨dy, hdy, hcy⟩ := hlift y hy
  have hx' : x = dx * (dx⁻¹ * x) := by group
  have hy' : y = dy * (dy⁻¹ * y) := by group
  rw [hx', hy', commutator_mul_central_mul hcx hcy]
  exact Subgroup.commutator_mem_commutator hdx hdy

@[expose] def liftCoreHom (φ : H →* X) (K : Subgroup X) : ↥(liftCore φ K) →* ↥K :=
  (φ.comp (liftCore φ K).subtype).codRestrict K fun d => liftCore_le_comap φ K d.2

theorem liftCoreHom_surjective {φ : H →* X} (hφ : Function.Surjective φ) {K : Subgroup X}
    (hK : ⁅K, K⁆ = K) : Function.Surjective (liftCoreHom φ K) := by
  intro k
  have hk : (k : X) ∈ (liftCore φ K).map φ := by rw [map_liftCore hφ hK]; exact k.2
  obtain ⟨d, hd, hdk⟩ := hk
  exact ⟨⟨d, hd⟩, Subtype.ext hdk⟩

theorem center_eq_bot_of_equiv_alt8' {K : Type*} [Group K]
    (e : K ≃* alternatingGroup (Fin 8)) : center K = ⊥ := by
  have hc : center (alternatingGroup (Fin 8)) = ⊥ := alternatingGroup.center_eq_bot (by norm_num)
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : e z ∈ center (alternatingGroup (Fin 8)) := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [hc, mem_bot] at hz'
  exact mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem center_liftCore {φ : H →* X} (hφ : Function.Surjective φ) (hker : φ.ker ≤ center H)
    {K : Subgroup X} (hK : ⁅K, K⁆ = K) (hKc : center ↥K = ⊥) :
    center ↥(liftCore φ K) = (liftCoreHom φ K).ker := by
  apply le_antisymm
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hzK : liftCoreHom φ K z ∈ center ↥K := by
      rw [mem_center_iff]
      intro k
      obtain ⟨d, rfl⟩ := liftCoreHom_surjective hφ hK k
      rw [← map_mul, ← map_mul, mem_center_iff.1 hz d]
    rw [hKc, mem_bot] at hzK
    exact hzK
  · intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hz1 : φ z = 1 := congrArg Subtype.val hz
    have hzc : (z : H) ∈ center H := hker hz1
    rw [mem_center_iff]
    intro d
    exact Subtype.ext (mem_center_iff.1 hzc d)

noncomputable def liftCore_quotientEquiv {φ : H →* X} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ center H) {K : Subgroup X} (hK : ⁅K, K⁆ = K) (hKc : center ↥K = ⊥) :
    (↥(liftCore φ K) ⧸ center ↥(liftCore φ K)) ≃* ↥K :=
  (QuotientGroup.quotientMulEquivOfEq (center_liftCore hφ hker hK hKc)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (liftCoreHom_surjective hφ hK))

theorem commutator_top_of_commutator_eq_self {Y : Type*} [Group Y] {D : Subgroup Y}
    (hD : ⁅D, D⁆ = D) : commutator ↥D = ⊤ := by
  have h2 : (commutator ↥D).map D.subtype = ⁅D, D⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h3 : (⊤ : Subgroup ↥D).map D.subtype = D := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective D.subtype_injective (by rw [h2, hD, h3])

theorem liftCore_isQuasisimple_open {φ : H →* X} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ center H) {K : Subgroup X} (e : ↥K ≃* alternatingGroup (Fin 8)) :
    CFSG.Open.IsQuasisimple ↥(liftCore φ K) := by
  have hK : ⁅K, K⁆ = K := commutator_eq_self_of_equiv_alternating_eight e
  have hKc : center ↥K = ⊥ := center_eq_bot_of_equiv_alt8' e
  refine ⟨commutator_top_of_commutator_eq_self (liftCore_perfect hφ hker hK), ?_⟩
  have hs : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by norm_num)
  exact @MulEquiv.isSimpleGroup _ _ _ _ hs ((liftCore_quotientEquiv hφ hker hK hKc).trans e)

theorem liftCore_isQuasisimple {φ : H →* X} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ center H) {K : Subgroup X} (e : ↥K ≃* alternatingGroup (Fin 8)) :
    CFSG.IsQuasisimple ↥(liftCore φ K) :=
  (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 (liftCore_isQuasisimple_open hφ hker e)

theorem liftCore_isSubnormal (φ : H →* X) {K : Subgroup X} (hK : K.IsSubnormal) :
    (liftCore φ K).IsSubnormal := by
  have hP : (K.comap φ).IsSubnormal := hK.comap φ
  refine Subgroup.IsSubnormal.trans (liftCore_le_comap φ K) ?_ hP
  refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hnP : (n : H) ∈ K.comap φ := liftCore_le_comap φ K hn
  have hcomm : ((g * n * g⁻¹ : ↥(K.comap φ)) : H) = ⁅(g : H), (n : H)⁆ * (n : H) := by
    simp [commutatorElement_def]
  rw [hcomm]
  exact (liftCore φ K).mul_mem (Subgroup.commutator_mem_commutator g.2 hnP) hn

theorem commutator_eq_bot_of_perfect {D E : Subgroup H} (hD : ⁅D, D⁆ = D)
    (h : ∀ d ∈ D, ∀ e ∈ E, ⁅d, e⁆ ∈ center H) : ⁅D, E⁆ = ⊥ := by
  have hDE : ⁅D, E⁆ ≤ center H := Subgroup.commutator_le.2 h
  have hED : ⁅E, D⁆ ≤ center H := by rw [Subgroup.commutator_comm]; exact hDE
  have hbot : ∀ {A B : Subgroup H}, A ≤ center H → ⁅A, B⁆ = ⊥ := by
    intro A B hA
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.2 fun a ha b _ => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.1 (hA ha) b).symm
  have h1 : ⁅⁅D, E⁆, D⁆ = ⊥ := hbot hDE
  have h2 : ⁅⁅E, D⁆, D⁆ = ⊥ := hbot hED
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [hD] at h3

end LiftCore

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
