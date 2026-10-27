module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCentralFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorRootAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCapture
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientRoot
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

universe v

variable {G : Type v} [Group G] [Finite G]

theorem original_pair_class_disjoint_distinguished_class
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) :
    ∀ w : G, w ∈ involutionPointClass z → w ∉ involutionPointClass u := by
  have hclassfix :=
    ((involution_point_unique_containment_action h.distinguished_mem h.distinguished_order).2
      h.unique_containment).2.1
  intro w hwz hwu
  obtain ⟨g, hg⟩ := hwu
  change rightConjugateElem u g = w at hg
  have hua := (point_right_base_fixed_iff H u).mpr
    (pairPointStabilizer_le_point H beta huD)
  have hub := (mem_point_right_stabilizer_iff H beta u).mp huD.2
  have hwa := point_right_fixed_conjugate hua g
  have hwb := point_right_fixed_conjugate hub g
  rw [hg] at hwa hwb
  obtain ⟨omega, _, huniq⟩ := hclassfix w hwz
  have heq : pointRightCosetMul H beta g =
      pointRightCosetMul H (rightCosetMk H 1) g :=
    (huniq _ hwb).trans (huniq _ hwa).symm
  have hback := congrArg (fun x : pointRightCosetSpace H => pointRightCosetMul H x g⁻¹) heq
  exact hb (by simpa only [pointRightCosetMul_mul, mul_inv_cancel,
    pointRightCosetMul_one] using hback)

theorem original_coset_stabilizer_full_off_u_orbit
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    ∀ s : G, s ∈ translatedCosetUnitSet H z u → s ≠ u →
      ∀ t : G, t ∈ translatedCosetUnitSet H z u → t ≠ u →
      ∃ a : (Subgroup.normalizer (translatedCosetUnitSet H z u) ⊓
          Subgroup.centralizer ({u} : Set G) : Subgroup G),
        rightConjugateElem s (a : G) = t := by
  intro s hs hsu t ht htu
  obtain ⟨x, hx, rfl⟩ := hs
  obtain ⟨y, hy, rfl⟩ := ht
  have hxclass : x ∈ involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G) := by
    exact hx.resolve_left (fun hone => hsu (by
      simp only [Set.mem_singleton_iff.mp hone, mul_one]))
  have hyclass : y ∈ involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G) := by
    exact hy.resolve_left (fun hone => htu (by
      simp only [Set.mem_singleton_iff.mp hone, mul_one]))
  obtain ⟨g, hg, hxy⟩ := original_point_centralizer_transitive_distinguished_set
    h u huz (h.local_embedding u hu huz hescape) x y hxclass hyclass
  refine ⟨⟨g, point_centralizer_le_translated_normalizer H z u ⟨hg.2, hg.1⟩, hg.2⟩, ?_⟩
  have huconj : rightConjugateElem u g = u := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg.2
    calc
      rightConjugateElem u g = g⁻¹ * (u * g) := mul_assoc _ _ _
      _ = g⁻¹ * (g * u) := congrArg (fun v : G => g⁻¹ * v) hcomm.symm
      _ = u := inv_mul_cancel_left g u
  have hmul : rightConjugateElem (u * x) g =
      rightConjugateElem u g * rightConjugateElem x g := by
    simpa only [MulAut.conj_apply, inv_inv, rightConjugateElem] using
      (MulAut.conj g⁻¹).map_mul u x
  exact hmul.trans (by rw [huconj, hxy])

theorem original_coset_full_conjugation_of_supplied_sylow_geometry
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : pointRightCosetSpace H) (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (U : Subgroup G) (hU : (U : Set G) = cosetUnitSet H z u)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hpartition : ∀ x : G,
      x ∈ (T : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype → IsInvolution x →
      x ∈ U ∨ x ∈ translatedCosetUnitSet H z u)
    (hDelta : involutionPointClass u ∩
      (((T : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype : Subgroup G) : Set G) =
      translatedCosetUnitSet H z u) :
    ∀ s : G, s ∈ translatedCosetUnitSet H z u →
      ∀ t : G, t ∈ translatedCosetUnitSet H z u →
      ∃ n : Subgroup.normalizer (translatedCosetUnitSet H z u),
        rightConjugateElem s (n : G) = t := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hz : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2,
      (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1⟩
  have htranslate : (fun v : G => u * v) '' (U : Set G) = translatedCosetUnitSet H z u := by
    rw [hU]
    rfl
  have hmove := coset_normalizer_moves_of_central_sylow_fusion U u z hz T S hzS hzcenter
    (original_pair_class_disjoint_distinguished_class h.local_datum beta hb huD)
    (by simpa only [htranslate] using hpartition)
    (hDelta.trans htranslate.symm)
  rw [htranslate] at hmove
  exact full_conjugation_transitivity_of_move_and_stabilizer _ u
    ⟨1, Set.mem_union_left _ (Set.mem_singleton 1), mul_one u⟩ hmove
    (original_coset_stabilizer_full_off_u_orbit h.local_datum hu huz hescape)

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
