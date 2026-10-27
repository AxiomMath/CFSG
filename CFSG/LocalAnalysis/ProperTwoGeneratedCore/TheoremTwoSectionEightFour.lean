module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCosetFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOriginalAffineAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTwoAdic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairPremises
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairCentralizerModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoParts

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe u

variable {G : Type u} [Group G]

@[expose] def rootCoset (H : Subgroup G) (z w : G) : Set G :=
  (fun v : G => w * v) '' ({1} ∪ distinguishedRoots H z w)

@[expose] def NonunitaryLinearDegreeTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta,
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w t → Commute w z →
          ∀ i : ℕ, (i = 1 ∨ i = 2) →
            Nat.card (elementFixedSet H w) =
              Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ i + 1 →
            i = 1 ∧ 4 ≤ Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ∧
              Nat.card (pointRightCosetSpace H) =
                Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 2 + 1

@[expose] def LinearDegreeNormalizerSolvableTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta,
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w t → Commute w z →
          Nat.card (elementFixedSet H w) =
              Nat.card ({1} ∪ distinguishedRoots H z w : Set G) + 1 →
            Nat.card (pointRightCosetSpace H) =
                Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 2 + 1 →
              Group.IsSolvable (cosetNormalizerPerm (rootCoset H z w)).range

@[expose] def SolvableLinearCosetNormalizerTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, twoRank (pairPointStabilizer H beta) = 1 →
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w z → Commute w t →
          Nat.card (elementFixedSet H w) =
              Nat.card ({1} ∪ distinguishedRoots H z w : Set G) + 1 →
            Nat.card (pointRightCosetSpace H) =
                Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 2 + 1 →
              Group.IsSolvable (cosetNormalizerPerm (rootCoset H z w)).range →
                ¬ IsConj w z ∧ ∃ V U A : Subgroup G,
                  (U : Set G) = {1} ∪ distinguishedRoots H z w ∧ (∀ x ∈ U, x * x = 1) ∧
                  4 ≤ U.relIndex V ∧ (∀ x ∈ U, x ≠ 1 → IsConj z x) ∧
                  A ≤ Subgroup.normalizer (V : Set G) ∧
                  (∀ x ∈ V, x ∉ U → ∀ y ∈ V, y ∉ U → ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ U) ∧
                  (∀ x ∈ V, IsConj w x → ∀ y ∈ U, IsConj w (x * y)) ∧
                  (∀ x y : G, IsConj w x → IsConj w y → x ≠ y → Commute x y →
                    IsConj z (x * y)) ∧
                  ∃ x ∈ V, IsConj w x

theorem nonunitaryContradictionTheorem_of_parts {G : Type} [Group G] [Finite G]
    (hP : PairStabilizerRankOneTheorem G) (hLin : NonunitaryLinearDegreeTheorem G)
    (hSol : LinearDegreeNormalizerSolvableTheorem G)
    (hSLC : SolvableLinearCosetNormalizerTheorem G) : NonunitaryContradictionTheorem G := by
  intro H z h beta hbeta t ht w hwB hw hwt hwz i hi hdeg
  obtain ⟨hrank, -⟩ := hP H z h beta hbeta
  obtain ⟨rfl, -, hn⟩ := hLin H z h beta hbeta t ht w hwB hw hwt hwz i hi hdeg
  rw [pow_one] at hdeg
  have hsolv := hSol H z h beta hbeta t ht w hwB hw hwt hwz hdeg hn
  obtain ⟨hnconj, V, U, A, -, hUsq, hindex, hUz, hAV, htrans, hsat, hprod, x, hxV, hx⟩ :=
    hSLC H z h beta hbeta t ht hrank w hwB hw hwz hwt hdeg hn hsolv
  exact InvolutionCosetFusion.transitive_quotient_cosets_exclude_class hw hnconj V U hUsq
    hindex hUz A hAV htrans hsat hprod x hxV hx

@[expose] def UnitaryNumeratorTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, twoRank (pairPointStabilizer H beta) = 1 →
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w z → Commute w t →
          Nat.card (elementFixedSet H w) =
              Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1 →
            (∃ f : ℕ, 2 ≤ f ∧ Nat.card ({1} ∪ distinguishedRoots H z w : Set G) = 2 ^ f) ∧
            (pairPointStabilizer H beta ⊓ Subgroup.centralizer
                ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
              (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({w} : Set G)) =
              Nat.card ({1} ∪ distinguishedRoots H z w : Set G) - 1

@[expose] def UnitaryMonomialTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, twoRank (pairPointStabilizer H beta) = 1 →
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w z → Commute w t →
          Nat.card (elementFixedSet H w) =
              Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 3 + 1 →
            (pairPointStabilizer H beta ⊓ Subgroup.centralizer
                ((Subgroup.zpowers w ⊔ Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
              (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({w * t} : Set G)) =
              3 * (Nat.card ({1} ∪ distinguishedRoots H z w : Set G) + 1)

theorem card_cosetUnitSet_eq (H : Subgroup G) (z w : G) :
    Nat.card (cosetUnitSet H z w) = Nat.card ({1} ∪ distinguishedRoots H z w : Set G) := by
  have : cosetUnitSet H z w = {1} ∪ distinguishedRoots H z w := by
    ext x
    simp only [cosetUnitSet, distinguishedRoots, Set.mem_union, Set.mem_inter_iff]
    tauto
  rw [this]

theorem no_four_of_twoRank_eq_one [Finite G] {D : Subgroup G} (hD : twoRank D = 1) :
    ∀ E : Subgroup D, IsElementaryAbelian 2 E → Nat.card E ≠ 4 := by
  intro E hE hcard
  have hel : IsElemAbelian 2 E :=
    ⟨hE.toIsMulCommutative, fun x hx => by
      have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx
      exact this⟩
  have := CFSG.SectionRank.le_pRank one_lt_two (le_top : E ≤ ⊤) hel
    (show Nat.card E = 2 ^ 2 by rw [hcard]; norm_num)
  have h1 : twoRank D = CFSG.Open.pRank 2 (⊤ : Subgroup D) := rfl
  omega

theorem exact_two_power_point_index_dvd
    [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (hrank : twoRank (pairPointStabilizer H beta) = 1)
    {w : G} (hwB : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwz : Commute w z)
    (hesc : ¬ Subgroup.centralizer ({w} : Set G) ≤ H) :
    Nat.card ({1} ∪ distinguishedRoots H z w : Set G) * (Nat.card (elementFixedSet H w) - 1) ∣
      Nat.card (pointRightCosetSpace H) - 1 := by
  have hcomm := properStrongEmbeddingCommutingImages_holds G
  have hR1 := smallerR1Full G
  have hrank2 := RankOnePair.two_le_twoRank_localInvolutionPointHull_of_pair_rank_one h hcomm hR1
    beta hbeta hrank hwB hw hwz hesc
  obtain ⟨T1⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({w} : Set G) ⊓ H)) := inferInstance
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, a, i, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, hdvd, -⟩ :=
    original_exact_index_native_affine_of_original_rank_data h hcomm hR1 beta hbeta hwB hw hwz
      hesc hrank2 hrank T1
  rw [← card_cosetUnitSet_eq]
  exact hdvd

theorem not_mem_of_mem_rightPairFlipFiber {H : Subgroup G} {z : G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    t ∉ H := by
  intro htH
  apply hbeta
  rw [← ht.2]
  change rightCosetMk H (1 * t) = rightCosetMk H 1
  refine Quotient.sound ?_
  change (QuotientGroup.rightRel H) (1 * t) 1
  rw [QuotientGroup.rightRel_apply]
  simpa using H.inv_mem htH

theorem unitaryContradictionTheorem_of_parts
    [Finite G]
    (hNum : UnitaryNumeratorTheorem G) (hMon : UnitaryMonomialTheorem G) :
    UnitaryContradictionTheorem G := by
  intro H z h beta hbeta t ht hrank w hwB hw hwz hwt hdeg
  have hcomm := properStrongEmbeddingCommutingImages_holds G
  have hR1 := smallerR1Full G
  obtain ⟨⟨f, hf, hq⟩, hnum⟩ := hNum H z h beta hbeta t ht hrank w hwB hw hwz hwt hdeg
  have hmon := hMon H z h beta hbeta t ht hrank w hwB hw hwz hwt hdeg
  set q := Nat.card ({1} ∪ distinguishedRoots H z w : Set G) with hqdef
  have htH := not_mem_of_mem_rightPairFlipFiber hbeta ht
  have hesc : ¬ Subgroup.centralizer ({w} : Set G) ≤ H := fun hle =>
    htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr hwt.eq.symm))
  have hdvd := exact_two_power_point_index_dvd h hbeta hrank hwB hw hwz hesc
  rw [hdeg, Nat.add_sub_cancel] at hdvd
  obtain ⟨S, hzS, hzc⟩ := h.central_sylow
  have hfaithful : ∀ g : G,
      (∀ x : pointRightCosetSpace H, pointRightCosetMul H x g = x) → g = 1 := fun g hg =>
    RankOnePair.rightCosetTranslate_faithful h g fun ω => by
      rw [← LocalCriterionInvariantNormalizer.pointRightCosetMul_eq_translate]
      exact hg ω
  have hdouble := (minimalLocalFailureSylowFixedPoints h).2.2.1
  have hodd := original_coset_degree_odd h.local_datum
  have huC : w ∈ pairPointStabilizer H beta ⊓ Subgroup.centralizer ({t} : Set G) :=
    ⟨hwB, Subgroup.mem_centralizer_singleton_iff.mpr hwt.eq⟩
  have hno := no_four_of_twoRank_eq_one hrank
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, -, -, -, U, -, -, -, -, -, -, hpre, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, hinvG, -, -, -⟩ :=
    RankOnePair.rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm hR1
      beta hbeta hrank hwB hw hwz hesc R T₁
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
      h.local_datum S hzS hzc hfaithful hdouble hodd beta hbeta w t hw huC ht hno htwo
      hcentralizer
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk := hlast q 3 hq2 (by norm_num) hdeg
  rw [hnum, hmon] at hk
  have : Nonempty (pointRightCosetSpace H) := ⟨rightCosetMk H 1⟩
  have hn1 : 1 ≤ Nat.card (pointRightCosetSpace H) := Nat.card_pos
  have hq1 : 1 ≤ q := by omega
  have heq : (((Nat.card (pointRightCosetSpace H) : ℤ) : ℚ)) - 1 = ((2 : ℚ) ^ f) ^ 3 *
      (((((2 : ℚ) ^ f) ^ 3 + 1) * ((2 : ℚ) ^ f - 1)) / (3 * ((2 : ℚ) ^ f + 1)) + 1) := by
    rw [Int.cast_natCast, hk]
    have hqQ : (q : ℚ) = (2 : ℚ) ^ f := by rw [hq]; push_cast; ring
    push_cast [Nat.cast_sub hq1]
    rw [hqQ]
    ring
  obtain ⟨-, -, hnot⟩ := (CFSG.ProperTwoGeneratedCore.LocalCriterionTwoAdic.rank_one_involution_count_two_adic_obstructions).2.2
    f hf (Nat.card (pointRightCosetSpace H) : ℤ) (by exact_mod_cast hn1) heq
  apply hnot
  have hdvdZ : ((q * q ^ 3 : ℕ) : ℤ) ∣ ((Nat.card (pointRightCosetSpace H) - 1 : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hdvd
  rw [Nat.cast_sub hn1, Nat.cast_mul, Nat.cast_pow, hq] at hdvdZ
  push_cast at hdvdZ
  have : ((2 : ℤ) ^ f) * ((2 : ℤ) ^ f) ^ 3 = ((2 : ℤ) ^ f) ^ 4 := by ring
  rw [this] at hdvdZ
  exact hdvdZ

end CFSG.ProperTwoGeneratedCore.HighRankPair
