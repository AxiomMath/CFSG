module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoSectionEightFour
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PairStabilizerRankOneHolds
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ShultCentralizerIndices
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ThreePointLeastFailure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairCentralizerModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorDistinguished
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniInvariant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniOriginalAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniRepresentatives
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniVectorIdentity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedField
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.Walter.J1

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

theorem closure_pair_eq_zpowers_sup (u t : G) :
    Subgroup.closure ({u, t} : Set G) = Subgroup.zpowers u ⊔ Subgroup.zpowers t := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

variable [Finite G]

theorem distinguishedThreePointCentralization_of_minimalLocalFailure
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (hrank : twoRank (pairPointStabilizer H beta) = 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    DistinguishedThreePointCentralization H (pairPointStabilizer H beta) t := by
  intro X hXD hX3 htX x hx
  have hX :=
    RankOnePair.minimalLocalFailure_rank_one_pair_three_point_normalized_subgroup_centralization
      h (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) beta hbeta hrank t ht X
      hXD htX hX3
  have hc : ⁅x, t⁆ ∈ ⁅X, Subgroup.zpowers t⁆ :=
    Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers t)
  rw [hX, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact Subgroup.mem_centralizer_singleton_iff.mpr hc

theorem nonunitary_linear_degree_of_trivial_odd_core
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {w : G} (hwB : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwt : Commute w t)
    (hwz : Commute w z) (hodd : CFSG.oddCore (localInvolutionPointHull z w) = ⊥)
    {i : ℕ} (hi : i = 1 ∨ i = 2)
    (hdeg : Nat.card (elementFixedSet H w) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ i + 1) :
    i = 1 ∧ 4 ≤ Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ∧
      Nat.card (pointRightCosetSpace H) =
        Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 2 + 1 := by
  classical
  have hcomm := properStrongEmbeddingCommutingImages_holds G
  have hR1 := smallerR1Full G
  have hrank : twoRank (pairPointStabilizer H beta) = 1 :=
    ((pairStabilizerRankOneTheorem_of_generation hgen.pairGenerationTheorem) H z h beta hbeta).1
  have htH := not_mem_of_mem_rightPairFlipFiber hbeta ht
  have hesc : ¬ Subgroup.centralizer ({w} : Set G) ≤ H := fun hle =>
    htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr hwt.eq.symm))
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, -, -, -, U, hU, -, hU4, -, -, hmodel, hpre, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, hinvG, -, -, -⟩ :=
    RankOnePair.rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm hR1
      beta hbeta hrank hwB hw hwz hesc R T₁
  have hUcard : Nat.card U = Nat.card ({1} ∪ distinguishedRoots H z w : Set G) := by
    have hset : (U : Set G) = {1} ∪ distinguishedRoots H z w := by
      rw [hU]
      ext x
      simp only [distinguishedRoots, Set.mem_union, Set.mem_inter_iff]
      tauto
    rw [← hset]
    rfl
  set q := Nat.card ({1} ∪ distinguishedRoots H z w : Set G) with hqdef
  rw [hUcard] at hU4
  have hq2 : 2 ≤ q := by omega
  have hlt2 : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hlt1 : q < q ^ 2 := by
    calc q = q ^ 1 := (pow_one _).symm
      _ < q ^ 2 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  obtain ⟨S, hzS, hzc⟩ := h.central_sylow
  have hfaithful : ∀ g : G,
      (∀ x : pointRightCosetSpace H, pointRightCosetMul H x g = x) → g = 1 := fun g hg =>
    RankOnePair.rightCosetTranslate_faithful h g fun ω => by
      rw [← LocalCriterionInvariantNormalizer.pointRightCosetMul_eq_translate]
      exact hg ω
  have hdouble := (minimalLocalFailureSylowFixedPoints h).2.2.1
  have hoddn := original_coset_degree_odd h.local_datum
  have huC : w ∈ pairPointStabilizer H beta ⊓ Subgroup.centralizer ({t} : Set G) :=
    ⟨hwB, Subgroup.mem_centralizer_singleton_iff.mpr hwt.eq⟩
  have hno := no_four_of_twoRank_eq_one hrank
  have htwo : ∀ v : G, orderOf v = 2 →
      v ∈ involutionPointClass w ∨ v ∈ involutionPointClass z := by
    intro v hv
    have : v ∈ {x : G | orderOf x = 2} := hv
    rw [hinvG] at this
    exact this
  have hcentralizer : ∀ a b c d : pointRightCosetSpace H,
      pointRightCosetMul H a w = a → pointRightCosetMul H b w = b →
      pointRightCosetMul H c w = c → pointRightCosetMul H d w = d →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({w} : Set G),
        pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d := by
    intro a b c d ha hb hc hd hab hcd
    let := LocalCriterionNumerator.originalCentralizerFixedSetAction H w
    have hne1 : (⟨a, ha⟩ : elementFixedSet H w) ≠ ⟨b, hb⟩ := fun h' =>
      hab (congrArg Subtype.val h')
    have hne2 : (⟨c, hc⟩ : elementFixedSet H w) ≠ ⟨d, hd⟩ := fun h' =>
      hcd (congrArg Subtype.val h')
    obtain ⟨g, hga, hgb⟩ := (MulAction.is_two_pretransitive_iff.mp hpre) hne1 hne2
    exact ⟨(g : G)⁻¹, Subgroup.inv_mem _ g.property, congrArg Subtype.val hga,
      congrArg Subtype.val hgb⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlast⟩ :=
    LocalCriterionDegreeIdentity.unique_two_involution_class_fixed_point_degree_identity
      h.local_datum S hzS hzc hfaithful hdouble hoddn beta hbeta w t hw huC ht hno htwo
      hcentralizer
  have hi1 : 1 ≤ i := by omega
  have hk := hlast q i hq2 hi1 hdeg
  have hdvd := exact_two_power_point_index_dvd h hbeta hrank hwB hw hwz hesc
  rw [hdeg, Nat.add_sub_cancel] at hdvd
  have h3pt := distinguishedThreePointCentralization_of_minimalLocalFailure h hbeta hrank ht
  have hV := closure_pair_eq_zpowers_sup w t
  have : Nonempty (pointRightCosetSpace H) := ⟨rightCosetMk H 1⟩
  have hn1 : 1 ≤ Nat.card (pointRightCosetSpace H) := Nat.card_pos
  have hU' : Nat.card ↥(({1} : Set G) ∪ (involutionPointClass z ∩
      (Subgroup.centralizer ({w} : Set G) : Set G) ∩ (H : Set G))) = q := by
    rw [hqdef]
    congr 2
    ext x
    simp only [distinguishedRoots, Set.mem_union, Set.mem_inter_iff]
    tauto
  rcases hmodel with ⟨hΓ, f, hf, hUf, hkf, E, -, -, -⟩ | ⟨hΓ, m, hm, hUm, hkm, E, -, -, -⟩ |
      ⟨hΓ, -⟩
  ·
    rw [hUcard] at hΓ hUf hkf
    have hi' : i = 1 := by
      rcases hi with rfl | rfl
      · rfl
      · omega
    subst hi'
    have hcardk : Nat.card (BinaryGaloisField f) = 2 ^ f := hkf.trans hUf
    let eL : localInvolutionPointHull z w ≃* GLAProj (GLASLGroup (Fin 2) (BinaryGaloisField f)) :=
      (((QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot).symm.trans
        E).trans (glaSL2EquivNative f hf hcardk).symm
    obtain ⟨-, hnum, hden⟩ :=
      RankOnePair.shult_centralizer_indices_of_distinguished_three_point h hcomm hR1 hgen beta
        hbeta ht hrank hwB hw hwt hwz hodd (k := BinaryGaloisField f)
        (Or.inl ⟨f, hf, hcardk, ⟨eL⟩⟩)
    have hden1 := (hden h3pt).1 f ⟨hf, hcardk, ⟨eL⟩⟩
    rw [hU', hV] at hnum hden1
    rw [hnum, hden1] at hk
    have heq : (((Nat.card (pointRightCosetSpace H) : ℤ) : ℚ)) - 1 = ((q : ℤ) : ℚ) *
        (((((q : ℤ) : ℚ) + 1) * (((q : ℤ) : ℚ) - 1)) / (((q : ℤ) : ℚ) + 1) + 1) := by
      rw [Int.cast_natCast, hk]
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
      ring
    have hsq := rank_one_involution_count_two_adic_obstructions.1
      (q : ℤ) (Nat.card (pointRightCosetSpace H) : ℤ) (by exact_mod_cast hq2)
      (by exact_mod_cast hn1) heq
    refine ⟨rfl, hU4, ?_⟩
    have : ((Nat.card (pointRightCosetSpace H) : ℕ) : ℤ) = ((q ^ 2 + 1 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  ·
    rw [hUcard] at hΓ hUm hkm
    have hi' : i = 2 := by
      rcases hi with rfl | rfl
      · rw [pow_one] at hdeg
        omega
      · rfl
    subst hi'
    exfalso
    have hcardk : Nat.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) := hkm.trans hUm
    let eS : localInvolutionPointHull z w ≃* GLASzGroup m (BinaryGaloisField (2 * m + 1)) :=
      (((QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot).symm.trans
        E).trans ((glaSzEquivNative m hm hcardk).trans (suzukiCoverNativeEquiv m)).symm
    obtain ⟨-, hnum, hden⟩ :=
      RankOnePair.shult_centralizer_indices_of_distinguished_three_point h hcomm hR1 hgen beta
        hbeta ht hrank hwB hw hwt hwz hodd (k := BinaryGaloisField (2 * m + 1))
        (Or.inr ⟨m, hm, hcardk, ⟨eS⟩⟩)
    have hden2 := (hden h3pt).2 m ⟨hm, hcardk, ⟨eS⟩⟩
    rw [hU', hV] at hnum hden2
    rw [hnum] at hk
    have hr : 2 ^ (m + 1) < 2 ^ (2 * m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    obtain ⟨eps, heps, hdeneq⟩ : ∃ eps : ℤ, (eps = -1 ∨ eps = 1) ∧
        (((pairPointStabilizer H beta ⊓ Subgroup.centralizer
          ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
          (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({w * t} : Set G)) : ℕ) : ℚ) =
          (2 : ℚ) ^ (2 * m + 1) + (eps : ℚ) * (2 : ℚ) ^ (m + 1) + 1 := by
      rcases hden2 with hd | hd
      · refine ⟨-1, Or.inl rfl, ?_⟩
        rw [hd, hUm]
        push_cast [Nat.cast_sub hr.le]
        ring
      · refine ⟨1, Or.inr rfl, ?_⟩
        rw [hd, hUm]
        push_cast
        ring
    rw [hdeneq] at hk
    have heq : (((Nat.card (pointRightCosetSpace H) : ℤ) : ℚ)) - 1 =
        ((2 : ℚ) ^ (2 * m + 1)) ^ 2 * (((((2 : ℚ) ^ (2 * m + 1)) ^ 2 + 1) *
          ((2 : ℚ) ^ (2 * m + 1) - 1)) /
          ((2 : ℚ) ^ (2 * m + 1) + (eps : ℚ) * (2 : ℚ) ^ (m + 1) + 1) + 1) := by
      rw [Int.cast_natCast, hk, hUm]
      push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
      ring
    obtain ⟨-, -, hnot⟩ :=
      rank_one_involution_count_two_adic_obstructions.2.1
        m hm eps (Nat.card (pointRightCosetSpace H) : ℤ) heps (by exact_mod_cast hn1) heq
    apply hnot
    have hdvdZ : ((q * q ^ 2 : ℕ) : ℤ) ∣ ((Nat.card (pointRightCosetSpace H) - 1 : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hdvd
    rw [Nat.cast_sub hn1, Nat.cast_mul, Nat.cast_pow, hUm] at hdvdZ
    push_cast at hdvdZ
    have h3 : ((2 : ℤ) ^ (2 * m + 1)) * ((2 : ℤ) ^ (2 * m + 1)) ^ 2 =
        ((2 : ℤ) ^ (2 * m + 1)) ^ 3 := by ring
    rw [h3] at hdvdZ
    exact hdvdZ
  ·
    rw [hUcard] at hΓ
    exfalso
    rcases hi with rfl | rfl
    · rw [pow_one] at hdeg
      omega
    · omega

@[expose] def LinearSuzukiHullOddCoreTrivial (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, twoRank (pairPointStabilizer H beta) = 1 →
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w z → Commute w t →
          ∀ i : ℕ, (i = 1 ∨ i = 2) →
            Nat.card (elementFixedSet H w) =
                Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ i + 1 →
              CFSG.oddCore (localInvolutionPointHull z w) = ⊥

theorem nonunitaryLinearDegreeTheorem_of_parts
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G)
    (hker : LinearSuzukiHullOddCoreTrivial G) : NonunitaryLinearDegreeTheorem G := by
  intro H z h beta hbeta t ht w hwB hw hwt hwz i hi hdeg
  have hrank : twoRank (pairPointStabilizer H beta) = 1 :=
    ((pairStabilizerRankOneTheorem_of_generation hgen.pairGenerationTheorem) H z h beta hbeta).1
  exact nonunitary_linear_degree_of_trivial_odd_core hgen h hbeta ht hwB hw hwt hwz
    (hker H z h beta hbeta t ht hrank w hwB hw hwz hwt i hi hdeg) hi hdeg

end CFSG.ProperTwoGeneratedCore.HighRankPair
