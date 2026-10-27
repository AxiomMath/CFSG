module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ThreePointLeastFailureOuter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairCentralizerModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionPerfect

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1 (rightConjugateElem_comp)
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction
  (single_involution_class_four_group_isPerfect)
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
  (native_rank_two_of_two_le_twoRank)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial (outer_isomorphism)

universe u

variable {G : Type u} [Group G] [Finite G]

@[expose] def InvolutionHullConditions (H : Subgroup G) (z u : G) (L : Subgroup G) : Prop :=
  L ≤ Subgroup.centralizer ({u} : Set G) ∧
    (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal ∧
    (∃ s ∈ L, s ∈ involutionPointClass z) ∧
    (∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z) ∧
    (∀ a b : pointRightCosetSpace H,
      pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
        ∃ l ∈ L, pointRightCosetMul H a l = b) ∧
    Group.IsSolvable (outerAutomorphismGroup L)

omit [Finite G] in
theorem mem_map_conj_inv_iff (L : Subgroup G) (g x : G) :
    x ∈ L.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ L := by
  rw [Subgroup.mem_map_equiv]
  simp

omit [Finite G] in
theorem pointClass_rightConjugate_mem {z x : G} (hx : x ∈ involutionPointClass z) (g : G) :
    rightConjugateElem x g ∈ involutionPointClass z := by
  obtain ⟨k, rfl⟩ := hx
  exact ⟨k * g, (rightConjugateElem_comp z k g).symm⟩

omit [Finite G] in
theorem involutionHullConditions_conj {H : Subgroup G} {z u : G} {L : Subgroup G}
    (hL : InvolutionHullConditions H z u L) (g : G) :
    InvolutionHullConditions H z (rightConjugateElem u g)
      (L.map (MulAut.conj g⁻¹).toMonoidHom) := by
  obtain ⟨hLC, hLnormal, ⟨s, hsL, hsD⟩, hinv, htrans, hout⟩ := hL
  have hmem := mem_map_conj_inv_iff L g
  have hCv : ∀ y : G, y ∈ Subgroup.centralizer ({rightConjugateElem u g} : Set G) ↔
      g * y * g⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
    intro y
    simp only [Subgroup.mem_centralizer_singleton_iff, rightConjugateElem]
    constructor
    · intro hy
      calc g * y * g⁻¹ * u = g * (y * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * y) * g⁻¹ := by rw [hy]
        _ = u * (g * y * g⁻¹) := by group
    · intro hy
      calc y * (g⁻¹ * u * g) = g⁻¹ * (g * y * g⁻¹ * u) * g := by group
        _ = g⁻¹ * (u * (g * y * g⁻¹)) * g := by rw [hy]
        _ = g⁻¹ * u * g * y := by group
  have hLN := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mp hLnormal
  have hL'C : L.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer ({rightConjugateElem u g} : Set G) := fun x hx =>
    (hCv x).mpr (hLC ((hmem x).mp hx))
  refine ⟨hL'C, ?_, ⟨g⁻¹ * s * g, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hL'C).mpr fun y hy => ?_
    have hy' := hLN ((hCv y).mp hy)
    refine Subgroup.mem_normalizer_iff.mpr fun n => ?_
    rw [hmem, hmem, Subgroup.mem_normalizer_iff.mp hy' (g * n * g⁻¹)]
    constructor <;> intro hn <;> convert hn using 1 <;> group
  · rw [hmem]
    convert hsL using 1
    group
  · exact pointClass_rightConjugate_mem hsD g
  · intro x hx hxo
    have hl := hinv _ ((hmem x).mp hx) (by
      rw [show g * x * g⁻¹ = MulAut.conj g x by simp, MulEquiv.orderOf_eq, hxo])
    have := pointClass_rightConjugate_mem hl g
    simpa [rightConjugateElem, mul_assoc] using this
  · intro a b ha hb
    have hfix : ∀ c : pointRightCosetSpace H,
        pointRightCosetMul H c (rightConjugateElem u g) = c →
          pointRightCosetMul H (pointRightCosetMul H c g⁻¹) u = pointRightCosetMul H c g⁻¹ := by
      intro c hc
      rw [pointRightCosetMul_mul]
      conv_rhs => rw [← hc]
      rw [pointRightCosetMul_mul]
      congr 1
      simp [rightConjugateElem, mul_assoc]
    obtain ⟨l, hl, hal⟩ := htrans _ _ (hfix a ha) (hfix b hb)
    refine ⟨g⁻¹ * l * g, ?_, ?_⟩
    · rw [hmem]
      convert hl using 1
      group
    · have h1 := congrArg (fun c => pointRightCosetMul H c g) hal
      simp only [pointRightCosetMul_mul] at h1
      rw [inv_mul_cancel, pointRightCosetMul_one] at h1
      rw [← h1]
  · exact (outer_isomorphism
      (L.equivMapOfInjective _ (MulAut.conj g⁻¹).injective)).2.mp hout

theorem escaping_hull_class_generates {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    {u : G} (huH : u ∈ H) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    ∃ hzL : z ∈ localInvolutionPointHull z u,
      Subgroup.closure (conjugatesOf (⟨z, hzL⟩ : localInvolutionPointHull z u)) = ⊤ ∧
      (∀ x : localInvolutionPointHull z u, orderOf x = 2 → IsConj ⟨z, hzL⟩ x) ∧
      CFSG.BenderSuzuki.IsStronglyEmbedded (H.subgroupOf (localInvolutionPointHull z u)) := by
  classical
  set L := localInvolutionPointHull z u
  have hhull := minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hsmallerR1
    huH hu huz hescape
  dsimp only at hhull
  obtain ⟨-, -, hP, hclassY, hYL, -, -, -⟩ := hhull
  have hclassL : involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) =
      conjugacyWithin L z := hclassY.trans hYL
  have hDL : ∀ x ∈ involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G),
      x ∈ L := fun x hx => Subgroup.subset_closure hx
  have hzL : z ∈ L := hDL z ⟨distinguished_mem_pointClass z,
    Subgroup.mem_centralizer_singleton_iff.mpr huz.eq.symm⟩
  have hSE := native_strong_embedding_of_order_conditions hP
  refine ⟨hzL, ?_, fun x hx => ?_, hSE⟩
  · apply Subgroup.map_injective L.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    change _ = Subgroup.closure _
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := isConj_iff.mp hy
      rw [hclassL]
      exact ⟨c⁻¹, by simp⟩
    · intro hx
      have hxL := hDL x hx
      rw [hclassL] at hx
      obtain ⟨l, hl⟩ := hx
      exact ⟨⟨x, hxL⟩, isConj_iff.mpr ⟨l⁻¹, Subtype.ext (by simpa using hl)⟩, rfl⟩
  · have hzorder : orderOf (⟨z, hzL⟩ : L) = 2 :=
      (Subgroup.orderOf_mk z hzL).trans h.local_datum.distinguished_order
    obtain ⟨g, hg⟩ := hSE.involutions_conjugate
      ⟨(orderOf_eq_prime_iff.mp hzorder).2, (orderOf_eq_prime_iff.mp hzorder).1⟩
      ⟨(orderOf_eq_prime_iff.mp hx).2, (orderOf_eq_prime_iff.mp hx).1⟩
    exact isConj_iff.mpr ⟨g⁻¹, by simpa [rightConjugateElem] using hg⟩

theorem single_class_hull_perfect_and_simple {L : Type u} [Group L] [Finite L] {z : L}
    (hz : orderOf z = 2) (hgen : Subgroup.closure (conjugatesOf z) = ⊤)
    (hclass : ∀ x : L, orderOf x = 2 → IsConj z x) {M : Subgroup L}
    (hM : CFSG.BenderSuzuki.IsStronglyEmbedded M) (hrank : 2 ≤ twoRank L) :
    Group.IsPerfect L ∧ IsSimpleGroup (L ⧸ CFSG.oddCore L) := by
  obtain ⟨E, hEcard, hEsq⟩ := native_rank_two_of_two_le_twoRank hrank
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hEcard]; decide)
  have : IsKleinFour E := ⟨hEcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
    fun e he => orderOf_eq_prime (hEsq e) he⟩
  refine ⟨single_involution_class_four_group_isPerfect z hclass hgen E, ?_⟩
  have hcore : involutionCore L = ⊤ := by
    rw [eq_top_iff, ← hgen, involutionCore_eq_closure]
    refine Subgroup.closure_mono fun x hx => ?_
    obtain ⟨c, rfl⟩ := isConj_iff.mp hx
    have hxo : orderOf (c * z * c⁻¹) = 2 := by
      rw [show c * z * c⁻¹ = MulAut.conj c z by simp, MulEquiv.orderOf_eq, hz]
    exact ⟨(orderOf_eq_prime_iff.mp hxo).2, (orderOf_eq_prime_iff.mp hxo).1⟩
  have := hM.isSimpleGroup_quotient_twoPrimeCore hcore
  exact (QuotientGroup.quotientMulEquivOfEq (oddCore_eq_twoPrimeCore (G := L))).isSimpleGroup

theorem rank_one_pair_hull_conditions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    InvolutionHullConditions H z u (localInvolutionPointHull z u) := by
  classical
  set L := localInvolutionPointHull z u
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huB
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z u ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({u} : Set G))) := inferInstance
  have hmodel := rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm
    hsmallerR1 beta hbeta hpairRank huB hu huz hescape R T₁
  dsimp only at hmodel
  obtain ⟨-, -, hrank, hRcenter, -, U, -, -, -, -, -, hmodels, -⟩ := hmodel
  have hhull := minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hsmallerR1
    huH hu huz hescape
  dsimp only at hhull
  obtain ⟨-, hLnormal, -, -, -, -, hfixL, -⟩ := hhull
  obtain ⟨hzL, hgen, hclass, hSE⟩ :=
    escaping_hull_class_generates h hcomm hsmallerR1 huH hu huz hescape
  have hzorder : orderOf (⟨z, hzL⟩ : L) = 2 :=
    (Subgroup.orderOf_mk z hzL).trans h.local_datum.distinguished_order
  obtain ⟨hperfect, hsimple⟩ := single_class_hull_perfect_and_simple hzorder hgen hclass hSE hrank
  have hout : Group.IsSolvable (Outer (L ⧸ CFSG.oddCore L)) := by
    rcases hmodels with ⟨-, f, -, -, -, E, -⟩ | ⟨-, m, hm, -, -, E, -⟩ |
        ⟨-, f, hf, hUcard, k, _, _, J, hJ, hkcard, hfixed, _, _, E, -⟩
    · exact (outer_isomorphism E).2.mpr (linear_model_outer_solvable f)
    · exact (outer_isomorphism E).2.mpr (suzuki_model_outer_solvable m hm)
    · exact (outer_isomorphism E).2.mpr (unitary_model_outer_solvable J f hf hJ
        (by rw [hkcard, hUcard]) (by rw [hfixed, hUcard]))
  refine ⟨localInvolutionPointHull_le_centralizer z u, hLnormal,
    ⟨z, hzL, distinguished_mem_pointClass z⟩, fun l hl hlo => ?_, fun a b ha hb => ?_,
    outer_solvable_of_simple_oddCore_quotient hRcenter hsimple hout⟩
  · obtain ⟨c, hc⟩ := isConj_iff.mp (hclass ⟨l, hl⟩ ((Subgroup.orderOf_mk l hl).trans hlo))
    exact ⟨(c : G)⁻¹, by simpa [rightConjugateElem] using congrArg Subtype.val hc⟩
  · have ha' : a ∈ elementFixedSet H u := ha
    have hb' : b ∈ elementFixedSet H u := hb
    rw [hfixL] at ha' hb'
    obtain ⟨l₁, hl₁, rfl⟩ := ha'
    obtain ⟨l₂, hl₂, rfl⟩ := hb'
    refine ⟨l₁⁻¹ * l₂, L.mul_mem (L.inv_mem hl₁) hl₂, ?_⟩
    rw [pointRightCosetMul_mul, mul_inv_cancel_left]

end CFSG.ProperTwoGeneratedCore.RankOnePair
