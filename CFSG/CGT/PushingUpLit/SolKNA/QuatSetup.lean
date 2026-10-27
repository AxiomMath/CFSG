module

public import CFSG.CGT.PushingUpLit.SolKAb.Setup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.ClassicalInvolution.Basic
import CFSG.ClassicalInvolution.OrderForm
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels
  genFittingFStar_eq_top_of_isSimpleGroup)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.ComponentClassification.AschbacherTightEmbedding (tightlyEmbedded_iff_classical)
open CFSG.Open (classicalInvolutionTightlyEmbedded genFittingFStar IsSubnormal)

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem oddCore_eq_bot (S : STSetting G K) : CFSG.oddCore ↥K = ⊥ := by
  have hchar : (CFSG.oddCore ↥K).Characteristic :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_characteristic (G := ↥K)
  have hodd : Odd (Nat.card ↥(CFSG.oddCore ↥K)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := ↥K)
  have hNK : (CFSG.oddCore ↥K).map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hMN : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (((CFSG.oddCore ↥K).map K.subtype : Subgroup G) : Set G) :=
    fun m hm => CFSG.RankThree.GF2n.mem_normalizer_map_subtype_of_characteristic hm
      (CFSG.oddCore ↥K)
  have hNn : (((CFSG.oddCore ↥K).map K.subtype).subgroupOf
      (Subgroup.normalizer (K : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hNK.trans Subgroup.le_normalizer)).mpr hMN
  have hNodd : Odd (Nat.card ↥((CFSG.oddCore ↥K).map K.subtype)) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hodd
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp
    (S.eq_bot_of_normal_of_odd_card (hNK.trans Subgroup.le_normalizer) hNn hNodd)

theorem exists_central_involution_of_quaternion (S : STSetting G K) (R : Sylow 2 K)
    (hq : IsQuaternionTwoGroup (sylowImg R)) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ sylowImg R ∧ K ≤ Subgroup.centralizer ({t} : Set G) ∧
      ∀ u ∈ K, orderOf u = 2 → u = t := by
  obtain ⟨n, hn, ⟨e'⟩⟩ := hq
  have e : ↥(R : Subgroup K) ≃* QuaternionGroup (2 ^ (n - 2)) :=
    ((R : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans e'
  obtain ⟨u, hu2, -, -⟩ :=
    CFSG.ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup e
  have hu2' : orderOf (u : K) = 2 := by rwa [Subgroup.orderOf_coe]
  have hBS := CFSG.ClassicalInvolution.involution_mem_center_oddCore_quotient R hn ⟨e⟩
    (u : K) u.2 hu2'
  have hcentral : ∀ k : K, k * (u : K) = (u : K) * k := by
    intro k
    have h1 := Subgroup.mem_center_iff.mp hBS (QuotientGroup.mk k)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, oddCore_eq_bot S,
      Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  have ht2 : orderOf ((u : K) : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have htK : ((u : K) : G) ∈ K := (u : K).2
  have hcent : K ≤ Subgroup.centralizer ({((u : K) : G)} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcentral ⟨g, hg⟩)
  refine ⟨((u : K) : G), ht2, ⟨(u : K), u.2, rfl⟩, hcent, fun w hw hw2 => ?_⟩
  exact CFSG.ClassicalInvolution.eq_of_orderOf_eq_two_of_quaternion_sylow htK ht2 hcent R
    ⟨n, hn, ⟨e⟩⟩ hw hw2

theorem centralizer_eq_normalizer_of_quaternion (S : STSetting G K) (R : Sylow 2 K)
    (hq : IsQuaternionTwoGroup (sylowImg R)) {t : G} (htK : t ∈ K) (ht : orderOf t = 2) :
    Subgroup.centralizer ({t} : Set G) = Subgroup.normalizer (K : Set G) := by
  obtain ⟨t₀, ht₀, -, -, hU⟩ := exists_central_involution_of_quaternion S R hq
  obtain rfl : t = t₀ := hU t htK ht
  exact CFSG.ClassicalInvolution.centralizer_eq_normalizer_of_tightlyEmbedded htK ht hU
    ((tightlyEmbedded_iff_classical K).mp S.tight).2

theorem oddLie_or_sporadic_of_quaternion (hCIT : ClassicalInvolutionTheoremModels)
    (S : STSetting G K) (R : Sylow 2 K) (hq : IsQuaternionTwoGroup (sylowImg R)) :
    CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 := by
  have : IsSimpleGroup G := S.simple
  obtain ⟨t, ht2, htR, hKt, -⟩ := exists_central_involution_of_quaternion S R hq
  have htK : t ∈ K := (Subgroup.map_subtype_le _) htR
  have hCN := centralizer_eq_normalizer_of_quaternion S R hq htK ht2
  have hsub : IsSubnormal K (Subgroup.centralizer ({t} : Set G)) :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hKt
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKt).mpr hCN.le)
  have hTE : classicalInvolutionTightlyEmbedded K :=
    ((tightlyEmbedded_iff_classical K).mp S.tight).2
  let eF : genFittingFStar G ≃* G :=
    (MulEquiv.subgroupCongr (genFittingFStar_eq_top_of_isSimpleGroup S.nonab)).trans
      Subgroup.topEquiv
  have : IsSimpleGroup (genFittingFStar G) := eF.isSimpleGroup
  have hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := S.nonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  obtain ⟨n, hn, ⟨e'⟩⟩ := hq
  have e : ↥(R : Subgroup K) ≃* QuaternionGroup (2 ^ (n - 2)) :=
    ((R : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans e'
  rcases (hCIT G hFnonab t ht2 K htK hsub R ⟨n, hn, ⟨e⟩⟩).2 hTE with h | h | h
  · exact .inl ((CFSG.ClassicalInvolution.oddLieType_congr eF).1 h)
  · exact .inr (.inl ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h))
  · exact .inr (.inr ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h))

end CFSG.CGT.PushingUpLit.SolKNA
