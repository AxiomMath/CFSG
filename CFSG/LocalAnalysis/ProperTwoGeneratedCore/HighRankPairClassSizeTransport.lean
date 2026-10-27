module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairClassSizeLinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureAmbientConjugation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalIdentification

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open scoped MatrixGroups

universe u

variable {G : Type u} [Group G]

theorem rightCosetMk_ne_one_of_not_mem {M : Subgroup G} {j : G} (hj : j ∉ M) :
    rightCosetMk M j ≠ rightCosetMk M 1 := by
  intro heq
  apply hj
  have := Quotient.exact heq
  change (QuotientGroup.rightRel M) j 1 at this
  rw [QuotientGroup.rightRel_apply] at this
  simpa using this

theorem mem_pairPointStabilizer_of_commute {M : Subgroup G} {j x : G} (hx : x ∈ M)
    (hxj : Commute x j) : x ∈ pairPointStabilizer M (rightCosetMk M j) := by
  refine Subgroup.mem_inf.mpr ⟨by rw [rightCosetStabilizer_base]; exact hx, ?_⟩
  rw [mem_rightCosetStabilizer_iff, rightCosetTranslate_mk, ← hxj.eq]
  apply Quotient.sound
  change (QuotientGroup.rightRel M) (x * j) j
  rw [QuotientGroup.rightRel_apply]
  simpa [mul_assoc] using M.inv_mem hx

theorem mem_rightPairFlipFiber_mk {M : Subgroup G} {t j : G} (hj : j ∈ involutionPointClass t) :
    j ∈ rightPairFlipFiber M t (rightCosetMk M j) :=
  ⟨hj, by rw [rightCosetTranslate_mk, one_mul]⟩

theorem pointRoots_eq_of_localDatum {M : Subgroup G} {t : G}
    (h : InvolutionPointLocalEmbedding M t) (s : G) :
    pointRoots M t s = involutionPointClass t ∩ (M : Set G) ∩
      (Subgroup.centralizer ({s} : Set G) : Set G) := by
  rw [pointRoots, ← LocalCriterionNumerator.original_point_class_intersection_eq_conjugacyWithin h]

variable [Finite G]

theorem minimalLocalFailure_fixed_point_transport {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {t : G} (ht : t ∈ involutionPointClass z)
    {γ : rightCosetSpace H} (hγ : rightCosetTranslate H γ t = γ) :
    MinimalInvolutionPointLocalFailure (rightCosetStabilizer H γ) t ∧
      involutionPointClass t = involutionPointClass z ∧
      Nat.card (conjugacyWithin (rightCosetStabilizer H γ) t) =
        Nat.card (conjugacyWithin H z) ∧
      ∀ x : G, Commute x t → x ∈ rightCosetStabilizer H γ := by
  obtain ⟨g, hg⟩ := ht
  have hg' : rightConjugateElem z g = t := hg
  have huniq := ((involution_point_unique_containment_action h.local_datum.distinguished_mem
    h.local_datum.distinguished_order).2 h.local_datum.unique_containment).2.1 t ⟨g, hg⟩
  have hbase := point_class_conjugate_fixed_rightCoset h.local_datum g
  rw [hg'] at hbase
  have hγ' : pointRightCosetMul H γ t = γ := by rw [pointRightCosetMul_eq_translate]; exact hγ
  have heq : γ = rightCosetMk H g := huniq.unique hγ' hbase
  have hstab : rightCosetStabilizer H γ = rightConjugate H g := by
    rw [heq, rightCosetStabilizer_mk]
  have h' := minimalLocalFailure_ambient_right_conjugate h g
  rw [hg', ← hstab] at h'
  refine ⟨h', ?_, ?_, ?_⟩
  · rw [← hg']
    exact minimalLocalFailure_conjugate_class z g
  · rw [hstab, ← hg']
    exact right_conjugate_point_class_card H z g
  · intro x hx
    rw [mem_rightCosetStabilizer_iff]
    have hfix : pointRightCosetMul H (rightCosetTranslate H γ x) t =
        rightCosetTranslate H γ x := by
      rw [pointRightCosetMul_eq_translate, rightCosetTranslate_mul, hx.eq,
        ← rightCosetTranslate_mul, hγ]
    exact huniq.unique hfix hγ'

theorem squareFieldAction_of_flip (hNC : NoncentralPairActionTheorem G)
    {M : Subgroup G} {t : G} (h : MinimalInvolutionPointLocalFailure M t) {j s r : G}
    (hj : j ∈ involutionPointClass t) (hjM : j ∉ M) (hsM : s ∈ M) (hrM : r ∈ M)
    (hs : orderOf s = 2) (hr : orderOf r = 2) (hst : Commute s t) (hsj : Commute s j)
    (hrj : Commute r j) (hsr : Commute s r) (hmove : ∃ x ∈ pointRoots M t s, ¬ Commute r x) :
    SquareFieldAction M t s r :=
  hNC M t h (rightCosetMk M j) (rightCosetMk_ne_one_of_not_mem hjM) j
    (mem_rightPairFlipFiber_mk hj) s r (mem_pairPointStabilizer_of_commute hsM hsj) hs hst hsj
    (mem_pairPointStabilizer_of_commute hrM hrj) hr hsr hmove

theorem exists_class_mem_not_mem_of_card_le {K M : Subgroup G} {F : Type*} [Field F] [Finite F]
    {a : ℕ} (hF : Nat.card F = 2 ^ a) (ψ : K ≃* SL(2, F)) {z t r s : G} (htK : t ∈ K)
    (ht : t ∈ involutionPointClass z) (htord : orderOf t = 2)
    (hKr : K ≤ Subgroup.centralizer ({r} : Set G)) (hKs : K ≤ Subgroup.centralizer ({s} : Set G))
    (hcard : Nat.card (involutionPointClass z ∩ (M : Set G) ∩
      (Subgroup.centralizer ({r} : Set G) : Set G) ∩
      (Subgroup.centralizer ({s} : Set G) : Set G) : Set G) ≤ 2 ^ a - 1) :
    ∃ j ∈ involutionPointClass z, Commute j r ∧ Commute j s ∧ j ∉ M := by
  by_contra hall
  push Not at hall
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · have := Finite.one_lt_card (α := F)
      rw [hF] at this
      omega
    · exact h
  have hsub : conjugacyWithin K t ⊆ involutionPointClass z ∩ (M : Set G) ∩
      (Subgroup.centralizer ({r} : Set G) : Set G) ∩
      (Subgroup.centralizer ({s} : Set G) : Set G) := by
    rintro x ⟨k, rfl⟩
    have hxr : (k : G)⁻¹ * t * k ∈ Subgroup.centralizer ({r} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKr k.2)) (hKr htK)) (hKr k.2)
    have hxs : (k : G)⁻¹ * t * k ∈ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKs k.2)) (hKs htK)) (hKs k.2)
    have hxD : (k : G)⁻¹ * t * k ∈ involutionPointClass z := pointClass_right_conjugate_mem ht k
    exact ⟨⟨⟨hxD, hall _ hxD (Subgroup.mem_centralizer_singleton_iff.mp hxr)
      (Subgroup.mem_centralizer_singleton_iff.mp hxs)⟩, hxr⟩, hxs⟩
  have hle := Nat.card_mono (Set.toFinite _) hsub
  have hlow := sq_sub_one_le_card_conjugacyWithin hF ψ htK htord
  have h2a : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have : 2 ^ a - 1 < (2 ^ a) ^ 2 - 1 := by
    have : 2 ^ a < (2 ^ a) ^ 2 := by nlinarith
    omega
  omega

end CFSG.ProperTwoGeneratedCore.HighRankPair
