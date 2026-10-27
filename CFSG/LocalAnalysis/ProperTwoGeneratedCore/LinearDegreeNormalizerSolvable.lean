module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NonunitaryLinearDegree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSeven
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightExclusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExactTwoPowerPointIndex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LinearDegreeNormalizerSolvableQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LinearDegreeNormalizerSolvableOrderFour

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.CosetNormalizer
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

universe u

private theorem cosetUnitSet_eq_union_distinguishedRoots {G : Type*} [Group G] (H : Subgroup G)
    (z w : G) : cosetUnitSet H z w = {1} ∪ distinguishedRoots H z w := by
  ext x
  simp only [cosetUnitSet, distinguishedRoots, Set.mem_union, Set.mem_inter_iff]
  tauto

theorem linear_degree_involution_coset_normalizer_solvable
    {G : Type} [Group G] [Finite G]
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    {w : G} (hwB : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwt : Commute w t)
    (hwz : Commute w z)
    (hdeg : Nat.card (elementFixedSet H w) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) + 1)
    (hn : Nat.card (pointRightCosetSpace H) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 2 + 1)
    (hodd : CFSG.oddCore (localInvolutionPointHull z w) = ⊥)
    (hK : Subgroup.centralizer ({w} : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z w : Set G) = Subgroup.zpowers w)
    (R : Sylow 2 ↥(localInvolutionPointHull z w ⊓ H))
    (hRcard : Nat.card R = Nat.card ({1} ∪ distinguishedRoots H z w : Set G))
    (hB : Subgroup.centralizer (rootCoset H z w) = Subgroup.zpowers w ⊔
      (R : Subgroup ↥(localInvolutionPointHull z w ⊓ H)).map
        (localInvolutionPointHull z w ⊓ H).subtype) :
    Group.IsSolvable (cosetNormalizerPerm (rootCoset H z w)).range := by
  classical
  have hcomm := properStrongEmbeddingCommutingImages_holds G
  have hR1 := smallerR1Full G
  have hrank : twoRank (pairPointStabilizer H beta) = 1 :=
    ((pairStabilizerRankOneTheorem_of_generation hgen.pairGenerationTheorem) H z h beta hbeta).1
  have htH := not_mem_of_mem_rightPairFlipFiber hbeta ht
  have hesc : ¬ Subgroup.centralizer ({w} : Set G) ≤ H := fun hle =>
    htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr hwt.eq.symm))
  have hwH : w ∈ H := pairPointStabilizer_le_point H beta hwB
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨⟨hsimple, hnonab⟩, -, -, -, -, U, hUset, hUelem, -, hΩR, -, hmodels, -, -, huL, -, -,
      -, -, -, -, -, -, hUclass, -, -, hinterA, -, -, -, -, -, -⟩ :=
    RankOnePair.rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm hR1
      beta hbeta hrank hwB hw hwz hesc R T₁
  obtain ⟨U', hU'elem, hU'set, -, hΔ, -, -, -, -, j, -, -, -, -, -, halt⟩ :=
    RankOnePair.involution_coset_normalizer_solvable_or_projective_seven h hcomm hR1 beta hbeta
      hrank hwB hw hwz hesc R T₁
  have hUU' : U = U' := SetLike.coe_injective (hUset.trans hU'set.symm)
  subst hUU'
  set q := Nat.card ({1} ∪ distinguishedRoots H z w : Set G) with hqdef
  have hUroots : (U : Set G) = {1} ∪ distinguishedRoots H z w :=
    hUset.trans (cosetUnitSet_eq_union_distinguishedRoots H z w)
  have hUq : Nat.card U = q := by
    rw [hqdef, ← hUroots]
    rfl
  have hroot : rootCoset H z w = (fun v : G => w * v) '' (U : Set G) := by
    rw [rootCoset, hUroots]
  have hΔ' := hΔ.trans hroot.symm
  rcases halt with ⟨hsolv, -⟩ | ⟨hU8, hb, -⟩
  · rw [hΔ'] at hsolv
    exact hsolv
  exfalso
  clear j hU'elem
  rw [hΔ'] at hb
  obtain ⟨b, hb⟩ := hb
  set Rg := (R : Subgroup ↥(localInvolutionPointHull z w ⊓ H)).map
    (localInvolutionPointHull z w ⊓ H).subtype with hRgdef
  have hURg : U ≤ Rg := by
    rw [← hΩR]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨(y : ↥(localInvolutionPointHull z w ⊓ H)), y.2, rfl⟩
  have hRgcard : Nat.card Rg = Nat.card U := by
    rw [hRgdef, Subgroup.card_map_of_injective
      (localInvolutionPointHull z w ⊓ H).subtype_injective, hRcard, hUq]
  have hRgU : U = Rg := Subgroup.eq_of_le_of_card_ge hURg hRgcard.le
  have hUL : U ≤ localInvolutionPointHull z w :=
    hRgU ▸ (Subgroup.map_subtype_le _).trans inf_le_left
  have hcent : Subgroup.centralizer (rootCoset H z w) = Subgroup.zpowers w ⊔ U := by
    rw [hB, ← hRgU]
  obtain ⟨hnormal, hsimpleQ, hnonabQ, hcardQ⟩ :=
    cosetNormalizer_quotient_simple_of_projective_seven hcent b hb
  have hno4 : ∀ x ∈ Subgroup.centralizer ({w} : Set G), orderOf x ≠ 4 := by
    obtain ⟨-, hLnormal, -, -, -, -, hfixL, -⟩ :=
      minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hR1 hwH hw hwz hesc
    have hLM := localInvolutionPointHull_le_centralizer z w
    rcases hmodels with ⟨-, f, -, hUf, hkf, E, -, -, -⟩ | ⟨hΓ, -⟩ | ⟨hΓ, -⟩
    · have hf3 : f = 3 := by
        have : 2 ^ f = 2 ^ 3 := by
          rw [← hUf, hU8]
          norm_num
        exact Nat.pow_right_injective le_rfl this
      subst hf3
      let e : localInvolutionPointHull z w ≃*
          Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField 3) :=
        (((QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot).symm.trans
          E).trans LocalCriterionSquareField.sl2EquivPSL2.symm
      have hoddorbit : Odd (Nat.card (LocalCriterionNumerator.numeratorRightOrbit H
          (localInvolutionPointHull z w) (rightCosetMk H 1))) := by
        rw [← hfixL, hdeg, ← hUq, hU8]
        decide
      obtain ⟨R', hR'⟩ := RankOnePair.exists_sylow_of_odd_orbit hoddorbit R
      have hUidx : ¬ 2 ∣ U.relIndex (localInvolutionPointHull z w) := by
        have hUR' : U.subgroupOf (localInvolutionPointHull z w) = R' := by
          rw [hRgU, hRgdef, ← hR']
          exact Subgroup.comap_map_eq_self_of_injective
            (localInvolutionPointHull z w).subtype_injective _
        change ¬ 2 ∣ (U.subgroupOf (localInvolutionPointHull z w)).index
        rw [hUR']
        exact R'.not_dvd_index
      have : IsElementaryAbelian 2 U := hUelem
      exact centralizer_no_order_four_of_SL2_hull hw hLM hLnormal huL hK (by norm_num)
        (hkf.trans hUf) (by decide) e hUL hUidx
    · rw [hdeg, ← hUq, hU8] at hΓ
      omega
    · rw [hdeg, ← hUq, hU8] at hΓ
      omega
  have hsmul : w • (U : Set G) = rootCoset H z w := by
    rw [hroot]
    rfl
  have hUM : U ≤ Subgroup.centralizer ({w} : Set G) :=
    hUL.trans (localInvolutionPointHull_le_centralizer z w)
  have huU : w ∉ U := fun hwU => huL (hUL hwU)
  have hwD : w ∉ involutionPointClass z :=
    LocalCriterionDegreeIdentity.pair_stabilizer_not_distinguished h.local_datum beta hbeta w hwB
  have hconj : ∀ x ∈ w • (U : Set G), IsConj w x := by
    intro x hx
    rw [hsmul, hroot, ← hinterA] at hx
    exact mem_involutionPointClass_iff.mp hx.1
  have hdisj : ∀ x ∈ U, x ≠ 1 → ¬ IsConj w x := by
    intro x hx hx1 hwx
    have hzx : IsConj z x := mem_involutionPointClass_iff.mp (hUclass ⟨hx, hx1⟩)
    exact hwD (mem_involutionPointClass_iff.mpr (hzx.trans hwx.symm))
  have hindex := @RankOnePair.index_ne_two_of_isSimpleGroup G _ hsimple hnonab
  have : IsElementaryAbelian 2 U := hUelem
  have hexcl := ExceptionalEight.exceptional_eight_involution_coset_normalizer_exclusion
    (E := Subgroup.zpowers w ⊔ U) (N := Subgroup.normalizer (rootCoset H z w)) hindex hw hU8
    hUM huU rfl (by rw [hsmul]) (by rw [hsmul, hcent]) hnonabQ hcardQ hconj hdisj hno4
  obtain ⟨T1⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({w} : Set G) ⊓ H)) := inferInstance
  obtain ⟨-, -, -, hDelta, -, -, -, -, -, -, hglobal⟩ :=
    involution_coset_normalizer_exact_two_power_point_index hgen.pairGenerationTheorem h beta
      hbeta hwB hw hwz hesc T1
  have hcosetU : (fun x : G => w * x) '' cosetUnitSet H z w = rootCoset H z w := by
    rw [rootCoset, cosetUnitSet_eq_union_distinguishedRoots]
  rw [hDelta.trans hcosetU] at hglobal
  have heq : Nat.card (pointRightCosetSpace H) - 1 =
      Nat.card (cosetUnitSet H z w) * (Nat.card (cosetFixedSet H w) - 1) := by
    rw [card_cosetUnitSet_eq, ← hqdef,
      show Nat.card (cosetFixedSet H w) = Nat.card (elementFixedSet H w) from rfl, hdeg, hn,
      Nat.add_sub_cancel, Nat.add_sub_cancel, sq]
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(Subgroup.normalizer (rootCoset H z w))) := inferInstance
  obtain ⟨Q, hQ⟩ := hglobal heq S
  exact hexcl Q (hQ ▸ Subgroup.map_subtype_le _)

@[expose] def LinearSuzukiPointKernelRootClauses (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, twoRank (pairPointStabilizer H beta) = 1 →
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w z → Commute w t →
          ∀ i : ℕ, (i = 1 ∨ i = 2) →
            Nat.card (elementFixedSet H w) =
                Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ i + 1 →
              Subgroup.centralizer ({w} : Set G) ⊓
                  Subgroup.centralizer (localInvolutionPointHull z w : Set G) =
                Subgroup.zpowers w ∧
              ∀ R : Sylow 2 ↥(localInvolutionPointHull z w ⊓ H),
                Nat.card R = Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ i ∧
                Subgroup.centralizer (rootCoset H z w) = Subgroup.zpowers w ⊔
                  (R : Subgroup ↥(localInvolutionPointHull z w ⊓ H)).map
                    (localInvolutionPointHull z w ⊓ H).subtype ∧
                Disjoint (Subgroup.zpowers w)
                  ((R : Subgroup ↥(localInvolutionPointHull z w ⊓ H)).map
                    (localInvolutionPointHull z w ⊓ H).subtype) ∧
                ∀ a ∈ Subgroup.zpowers w,
                  ∀ c ∈ (R : Subgroup ↥(localInvolutionPointHull z w ⊓ H)).map
                    (localInvolutionPointHull z w ⊓ H).subtype, Commute a c

theorem linearDegreeNormalizerSolvableTheorem_of_parts
    {G : Type} [Group G] [Finite G]
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G)
    (hodd : LinearSuzukiHullOddCoreTrivial G) (hker : LinearSuzukiPointKernelRootClauses G) :
    LinearDegreeNormalizerSolvableTheorem G := by
  intro H z h beta hbeta t ht w hwB hw hwt hwz hdeg hn
  have hrank : twoRank (pairPointStabilizer H beta) = 1 :=
    ((pairStabilizerRankOneTheorem_of_generation hgen.pairGenerationTheorem) H z h beta hbeta).1
  have hdeg1 : Nat.card (elementFixedSet H w) =
      Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ 1 + 1 := by
    rw [pow_one]
    exact hdeg
  obtain ⟨hK, hroot⟩ := hker H z h beta hbeta t ht hrank w hwB hw hwz hwt 1 (Or.inl rfl) hdeg1
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨hRcard, hB, -, -⟩ := hroot R
  rw [pow_one] at hRcard
  exact linear_degree_involution_coset_normalizer_solvable hgen h hbeta ht hwB hw hwt hwz hdeg hn
    (hodd H z h beta hbeta t ht hrank w hwB hw hwz hwt 1 (Or.inl rfl) hdeg1) hK R hRcard hB

end CFSG.ProperTwoGeneratedCore.HighRankPair
