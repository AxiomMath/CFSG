module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
import CFSG.ClassicalInvolution.Basic
import CFSG.ClassicalInvolution.OrderForm
import CFSG.LocalAnalysis.ComponentInitial.StandardBasics

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup CFSG.Open

@[expose] def ClassicalInvolutionTheoremModels : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (z : G), orderOf z = 2 →
    ∀ (J : Subgroup G), z ∈ J → CFSG.Open.IsSubnormal J (centralizer ({z} : Set G)) →
    ∀ (S : Sylow 2 J),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    (classicalInvolutionWitness J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → Blueprint.OddLieType (genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12)

theorem genFittingFStar_eq_top_of_isSimpleGroup {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) : genFittingFStar G = ⊤ := by
  have : IsSimpleGroup (⊤ : Subgroup G) := (Subgroup.topEquiv (G := G)).isSimpleGroup
  obtain ⟨a, b, hab⟩ := hnonab
  refine CFSG.ClassicalInvolution.genFittingFStar_eq_of_normal_simple ⊤
    ⟨⟨a, mem_top a⟩, ⟨b, mem_top b⟩, fun h => hab (congrArg Subtype.val h)⟩ ?_
  rw [coe_top, centralizer_univ]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exact absurd (mem_center_iff.mp (h ▸ mem_top a : a ∈ center G) b).symm hab

theorem quaternion_standard_recognition (hCIT : ClassicalInvolutionTheoremModels)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {L : Subgroup G} (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G))) {n : ℕ} (hn : 3 ≤ n)
    (hS : Nonempty ((S : Subgroup (centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (n - 2)))) :
    Blueprint.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11 ∨
      Blueprint.NativeSporadic.IsSporadic G .M12 := by
  obtain ⟨e⟩ := hS
  obtain ⟨u, hu2, hu, -⟩ :=
    CFSG.ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup e
  set t : centralizer (L : Set G) := (u : centralizer (L : Set G)) with ht_def
  have htS : t ∈ S := u.2
  have ht2 : orderOf (t : G) = 2 := by rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  have hST : ∀ s ∈ S, (s : G) ∈ centralizer ({(t : G)} : Set G) := fun s hs => by
    have hc : (⟨s, hs⟩ : S) * u * (⟨s, hs⟩ : S)⁻¹ = u :=
      hu _ (by rw [CFSG.ClassicalInvolution.orderOf_conj_eq, hu2])
    have hc' : s * t * s⁻¹ = t := congrArg Subtype.val hc
    exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mul_inv_eq_iff_eq_mul.1 hc'))
  set R : Subgroup G := centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G) with hR
  have hle : R ≤ centralizer (L : Set G) := inf_le_left
  have hrange : (S : Subgroup (centralizer (L : Set G))) ≤ (inclusion hle).range :=
    fun s hs => ⟨⟨s, s.2, hST s hs⟩, rfl⟩
  let SR : Sylow 2 R := S.comapOfInjective (inclusion hle) (inclusion_injective hle) hrange
  have eR : (SR : Subgroup R) ≃* QuaternionGroup (2 ^ (n - 2)) :=
    (((S : Subgroup _).comap (inclusion hle)).equivMapOfInjective _
      (inclusion_injective hle)).trans ((MulEquiv.subgroupCongr (map_comap_eq_self hrange)).trans e)
  obtain ⟨-, -, -, -, hRn⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL t.2 ht2
  have htR : (t : G) ∈ R := ⟨t.2, mem_centralizer_singleton_iff.2 rfl⟩
  have hRC : R ≤ centralizer ({(t : G)} : Set G) := inf_le_right
  have hsub : CFSG.Open.IsSubnormal R (centralizer ({(t : G)} : Set G)) :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hRC hRn
  have hTE : classicalInvolutionTightlyEmbedded R :=
    (CFSG.ClassicalInvolution.tightlyEmbedded_iff_centralizer_le_normalizer htR ht2 hRC SR
      ⟨n, hn, ⟨eR⟩⟩).2 ((normal_subgroupOf_iff_le_normalizer hRC).1 hRn)
  let eF : genFittingFStar G ≃* G :=
    (MulEquiv.subgroupCongr (genFittingFStar_eq_top_of_isSimpleGroup hnonab)).trans
      Subgroup.topEquiv
  have : IsSimpleGroup (genFittingFStar G) := eF.isSimpleGroup
  have hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  rcases (hCIT G hFnonab (t : G) ht2 R htR hsub SR ⟨n, hn, ⟨eR⟩⟩).2 hTE with h | h | h
  · exact .inl ((CFSG.ClassicalInvolution.oddLieType_congr eF).1 h)
  · exact .inr (.inl ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h))
  · exact .inr (.inr ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h))

end CFSG.ComponentClassification.StandardRecognition
