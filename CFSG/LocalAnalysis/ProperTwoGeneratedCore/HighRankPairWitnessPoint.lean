module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairWitnessLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureAmbientConjugation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairWitnessCommutator
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalIdentification

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped commutatorElement MatrixGroups

universe u

variable {G : Type u} [Group G] [Finite G]

theorem class_fixed_point_unique {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {t : G} (ht : t ∈ involutionPointClass z)
    {γ δ : rightCosetSpace H} (hγ : rightCosetTranslate H γ t = γ)
    (hδ : rightCosetTranslate H δ t = δ) : γ = δ := by
  obtain ⟨_, huniq, _⟩ := (involution_point_unique_containment_action h.distinguished_mem
    h.distinguished_order).2 h.unique_containment
  obtain ⟨ω, -, hω⟩ := huniq t ht
  have hγ' : pointRightCosetMul H γ t = γ := by rw [pointRightCosetMul_eq_translate]; exact hγ
  have hδ' : pointRightCosetMul H δ t = δ := by rw [pointRightCosetMul_eq_translate]; exact hδ
  exact (hω γ hγ').trans (hω δ hδ').symm

theorem commute_fixes_class_fixed_point {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {t g : G} (ht : t ∈ involutionPointClass z)
    (hgt : Commute g t) {γ : rightCosetSpace H} (hγ : rightCosetTranslate H γ t = γ) :
    rightCosetTranslate H γ g = γ := by
  apply class_fixed_point_unique h ht _ hγ
  rw [rightCosetTranslate_mul, hgt.eq, ← rightCosetTranslate_mul, hγ]

theorem minimalLocalFailure_at_fixed_point {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {t : G} (ht : t ∈ involutionPointClass z)
    {γ : rightCosetSpace H} (hγ : rightCosetTranslate H γ t = γ) :
    MinimalInvolutionPointLocalFailure (rightCosetStabilizer H γ) t ∧
      involutionPointClass t = involutionPointClass z := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep γ
  have hγeq : rightCosetStabilizer H (Quotient.mk _ g) = rightConjugate H g :=
    rightCosetStabilizer_mk H g
  have h' := minimalLocalFailure_ambient_right_conjugate h g
  have hclass : involutionPointClass (rightConjugateElem z g) = involutionPointClass z :=
    minimalLocalFailure_conjugate_class z g
  have htH : t ∈ rightConjugate H g := by
    rw [← hγeq, mem_rightCosetStabilizer_iff]
    exact hγ
  have htmem : t ∈ conjugacyWithin (rightConjugate H g) (rightConjugateElem z g) := by
    rw [← original_point_class_intersection_eq_conjugacyWithin h'.local_datum, hclass]
    exact ⟨ht, htH⟩
  obtain ⟨h'', hclass', -⟩ := minimalLocalFailure_at_point_class_member h' htmem
  rw [hγeq]
  exact ⟨h'', hclass'.trans hclass⟩


omit [Finite G] in
theorem mem_localHull {z u y : G} (hy : y ∈ involutionPointClass z) (hyu : Commute y u) :
    y ∈ localInvolutionPointHull z u :=
  Subgroup.subset_closure ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyu.eq⟩

theorem involution_mem_pointClass_of_mem_localHull {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {r : G} (hr : orderOf r = 2) (hrz : Commute r z)
    (hesc : ¬ Subgroup.centralizer ({r} : Set G) ≤ H) {y : G}
    (hyL : y ∈ localInvolutionPointHull z r) (hy : orderOf y = 2) :
    y ∈ involutionPointClass z := by
  set L := localInvolutionPointHull z r
  have hse := native_strong_embedding_of_order_conditions (h.local_embedding r hr hrz hesc)
  have hzL : z ∈ L := mem_localHull (distinguished_mem_pointClass z) hrz.symm
  have hinv : ∀ x : L, orderOf (x : G) = 2 → IsInvolution x := fun x hx =>
    ⟨fun h1 => by
      have : (x : G) = 1 := congrArg Subtype.val h1
      rw [this, orderOf_one] at hx
      omega,
     Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx, pow_orderOf_eq_one])⟩
  obtain ⟨g, hg⟩ := CFSG.BenderSuzuki.IsStronglyEmbedded.involutions_conjugate hse
    (hinv ⟨z, hzL⟩ h.distinguished_order) (hinv ⟨y, hyL⟩ hy)
  refine ⟨(g : G), ?_⟩
  have := congrArg Subtype.val hg
  simpa [rightConjugateElem] using this

theorem hull_class_commute {H : Subgroup G} {t : G}
    (h : MinimalInvolutionPointLocalFailure H t)
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G) {r : G}
    (hrH : r ∈ H) (hr : orderOf r = 2) (hrt : Commute r t)
    (hesc : ¬ Subgroup.centralizer ({r} : Set G) ≤ H) {y : G}
    (hy : y ∈ involutionPointClass t ∩ (H : Set G) ∩
      (Subgroup.centralizer ({r} : Set G) : Set G)) : Commute y t := by
  obtain ⟨-, -, -, -, -, -, -, hxor⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull.minimalLocalFailure_arbitrary_involution_centralizer_hull
      h hcomm hR1 hrH hr hrt hesc
  rcases hxor with ⟨⟨-, hone, -⟩, -⟩ | ⟨⟨-, U, hU, hUelem, -⟩, -⟩
  · rw [hone] at hy
    rw [Set.mem_singleton_iff.mp hy]
  · have htU : t ∈ U := by
      have : t ∈ (U : Set G) := by
        rw [hU]
        exact Or.inr ⟨⟨distinguished_mem_pointClass t, h.local_datum.distinguished_mem⟩,
          Subgroup.mem_centralizer_singleton_iff.mpr hrt.symm.eq⟩
      exact this
    have hyU : y ∈ U := by
      have : y ∈ (U : Set G) := by rw [hU]; exact Or.inr hy
      exact this
    exact congrArg Subtype.val (hUelem.toIsMulCommutative.is_comm.comm ⟨y, hyU⟩ ⟨t, htU⟩)


theorem le_localHull_of_commutator_eq {H : Subgroup G} {t : G}
    (h : MinimalInvolutionPointLocalFailure H t)
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G) {s : G}
    (hsH : s ∈ H) (hs : orderOf s = 2) (hst : Commute s t)
    (hesc : ¬ Subgroup.centralizer ({s} : Set G) ≤ H) {M : Subgroup G}
    (hMs : M ≤ Subgroup.centralizer ({s} : Set G)) (hMt : ⁅M, Subgroup.zpowers t⁆ = M) :
    M ≤ localInvolutionPointHull t s := by
  obtain ⟨-, hnorm, -⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull.minimalLocalFailure_arbitrary_involution_centralizer_hull
      h hcomm hR1 hsH hs hst hesc
  set L := localInvolutionPointHull t s
  have hLY : L ≤ Subgroup.centralizer ({s} : Set G) := localInvolutionPointHull_le_centralizer t s
  have htL : t ∈ L := mem_localHull (distinguished_mem_pointClass t) hst.symm
  rw [← hMt, Subgroup.commutator_le]
  intro m hm k hk
  have hkL : k ∈ L := (Subgroup.zpowers_le.mpr htL) hk
  have hconj : m * k * m⁻¹ ∈ L := by
    have := hnorm.conj_mem ⟨k, hLY hkL⟩ hkL ⟨m, hMs hm⟩
    exact this
  rw [commutatorElement_def]
  exact L.mul_mem hconj (L.inv_mem hkL)


omit [Finite G] in
theorem mem_normalizer_localHull {z r f : G} (hfr : Commute f r) :
    f ∈ Subgroup.normalizer (localInvolutionPointHull z r : Set G) := by
  have hconj : ∀ k : G, Commute k r → ∀ d ∈ involutionPointClass z ∩
      (Subgroup.centralizer ({r} : Set G) : Set G),
      k * d * k⁻¹ ∈ localInvolutionPointHull z r := by
    intro k hkr d hd
    have hdr : Commute d r := (Subgroup.mem_centralizer_singleton_iff.mp hd.2)
    apply mem_localHull
    · have := pointClass_right_conjugate_mem hd.1 k⁻¹
      simpa [rightConjugateElem] using this
    · exact (hkr.mul_left hdr).mul_left hkr.inv_left
  exact mem_normalizer_closure (hconj f hfr) (fun d hd => by
    have := hconj f⁻¹ hfr.inv_left d hd
    rwa [inv_inv] at this)

theorem moves_class_flip_fixed_points {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G) (hR1 : SmallerR1Full G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) {M : Subgroup G}
    (hMB : M ≤ pairPointStabilizer H beta) (hMt : ⁅M, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∀ γ : rightCosetSpace H, rightCosetTranslate H γ t = γ →
      ∃ x ∈ M, rightCosetTranslate H γ x ≠ γ := by
  have htriple := CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull.properHull_minimal_failure_distinguished_triple_centralization
    h hcomm hR1
  have hno := CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree.noncentral_pair_subgroup_class_flip_has_no_fixed_point
    htriple beta hbeta t ht M hMB hMt
  intro γ hγ
  by_contra hall
  push Not at hall
  apply hno γ (fun m hm => by rw [pointRightCosetMul_eq_translate]; exact hall m hm)
  rw [pointRightCosetMul_eq_translate]
  exact hγ


omit [Finite G] in
theorem le_of_mul_self_mem_of_equiv {M K : Subgroup G} {k : Type*} [Field k] [CharP k 2]
    (ψ : M ≃* SL(2, k)) (hK : ∀ g ∈ M, g * g = 1 → g ∈ K) : M ≤ K := by
  intro m hm
  have hmem : ψ ⟨m, hm⟩ ∈ Subgroup.closure {g : SL(2, k) | g * g = 1} := by
    rw [sl2_closure_mul_self_eq_one]
    exact Subgroup.mem_top _
  have key : ∀ g ∈ Subgroup.closure {g : SL(2, k) | g * g = 1}, ((ψ.symm g : M) : G) ∈ K := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      apply hK _ (ψ.symm g).2
      have : ψ.symm g * ψ.symm g = 1 := by
        rw [← map_mul, show g * g = 1 from hg, map_one]
      exact congrArg Subtype.val this
    | one => simp
    | mul g g' _ _ hg hg' =>
      rw [map_mul, Subgroup.coe_mul]
      exact K.mul_mem hg hg'
    | inv g _ hg =>
      rw [map_inv, Subgroup.coe_inv]
      exact K.inv_mem hg
  have := key _ hmem
  rwa [MulEquiv.symm_apply_apply] at this

omit [Finite G] in
theorem mul_self_of_commute_of_equiv {L : Subgroup G} {F : Type*} [Field F] [CharP F 2]
    (φ : L ≃* SL(2, F)) {t g : G} (htL : t ∈ L) (ht : orderOf t = 2) (hgL : g ∈ L)
    (hgt : Commute g t) : g * g = 1 := by
  have hA1 : φ ⟨t, htL⟩ ≠ 1 := by
    intro h1
    have : (⟨t, htL⟩ : L) = 1 := by rw [← map_eq_one_iff φ φ.injective]; exact h1
    have ht1 : t = 1 := congrArg Subtype.val this
    rw [ht1, orderOf_one] at ht
    omega
  have hA2 : φ ⟨t, htL⟩ * φ ⟨t, htL⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htL⟩ : L) * ⟨t, htL⟩ = 1 :=
      Subtype.ext (show t * t = 1 by rw [← pow_two, ← ht, pow_orderOf_eq_one])
    rw [this, map_one]
  have hAB : φ ⟨t, htL⟩ * φ ⟨g, hgL⟩ = φ ⟨g, hgL⟩ * φ ⟨t, htL⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgt.symm.eq
  have hB := CFSG.Walter.sl2_mul_self_eq_one_of_commute hA1 hA2 hAB
  rw [← map_mul, map_eq_one_iff φ φ.injective] at hB
  exact congrArg Subtype.val hB

omit [Finite G] in
theorem card_inf_centralizer_of_equiv {M : Subgroup G} {k : Type*} [Field k] [Finite k]
    [CharP k 2] (ψ : M ≃* SL(2, k)) {t : G} (htM : t ∈ M) (ht : orderOf t = 2) :
    Nat.card (M ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = Nat.card k := by
  have hA1 : ψ ⟨t, htM⟩ ≠ 1 := by
    intro h1
    have : (⟨t, htM⟩ : M) = 1 := by rw [← map_eq_one_iff ψ ψ.injective]; exact h1
    have ht1 : t = 1 := congrArg Subtype.val this
    rw [ht1, orderOf_one] at ht
    omega
  have hA2 : ψ ⟨t, htM⟩ * ψ ⟨t, htM⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htM⟩ : M) * ⟨t, htM⟩ = 1 :=
      Subtype.ext (show t * t = 1 by rw [← pow_two, ← ht, pow_orderOf_eq_one])
    rw [this, map_one]
  rw [← sl2_card_centralizer_involution hA1 hA2]
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨ψ ⟨x, x.2.1⟩, ?_⟩
      invFun := fun g => ⟨ψ.symm g, (ψ.symm g).2, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun g => ?_ }
  · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2.2)
  · have hg := Subgroup.mem_centralizer_singleton_iff.mp g.2
    show ((ψ.symm g : M) : G) ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : ψ.symm g * ⟨t, htM⟩ = ⟨t, htM⟩ * ψ.symm g := by
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hg
    exact congrArg Subtype.val h1
  · apply Subtype.ext
    simp
  · apply Subtype.ext
    simp

end CFSG.ProperTwoGeneratedCore.HighRankPair
