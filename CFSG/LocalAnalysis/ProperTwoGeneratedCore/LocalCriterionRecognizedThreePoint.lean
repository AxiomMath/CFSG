module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointLifting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma312
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointCosets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointRoot
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryRecognition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open LocalCriterionGeometry LocalCriterionMaximalPrime LocalCriterionRecognizedThreePoint

variable {G : Type*} [Group G] [Finite G]

theorem recognized_three_point_p_subgroup_involution_normalizer
    (hrank : 2 ≤ CFSG.Open.twoRank G) : R1Full G →
    ∀ (H : Subgroup G), fusionStronglyEmbedded H →
    ∀ (z : G), z ∈ H → orderOf z = 2 →
    ∀ (p : ℕ), p.Prime → Odd p →
    ∀ (P : Subgroup G), IsPGroup p P → P ≤ H →
      3 ≤ Nat.card (pointFixedSet H P) →
      (∃ T : Sylow p (CFSG.oddCore G),
        (T : Subgroup (CFSG.oddCore G)).map (CFSG.oddCore G).subtype =
          P ⊓ CFSG.oddCore G) →
      (conjugacyWithin H z ∩ (Subgroup.normalizer (P : Set G) : Set G)).Nonempty := by
  intro _ H hH z hzH hz p hp _ P hP hPH hthree hintersection
  have hnative : IsStronglyEmbedded H := native_strong_embedding_of_order_conditions hH
  have hrankNative : TwoRankAtLeastTwo G := native_rank_two_of_two_le_twoRank hrank
  let R : Subgroup G := CFSG.oddCore G
  let Q := G ⧸ R
  let q : G →* Q := QuotientGroup.mk' R
  let Hbar : Subgroup Q := H.map q
  let Pbar : Subgroup Q := P.map q
  have hRH : R ≤ H := oddCore_le_of_rank_two_stronglyEmbedded H hnative hrankNative
  have hRodd : Odd (Nat.card R) := CFSG.ComponentClassification.OddCore.odd_card G
  have hHbar : IsStronglyEmbedded Hbar :=
    IsStronglyEmbedded.map_quotient_of_odd_kernel hnative hRH hRodd
  have hQrank : TwoRankAtLeastTwo Q := rank_two_quotient_of_odd R hRodd hrankNative
  have hQcore : CFSG.oddCore Q = ⊥ := by
    change componentClassificationOddCore (G ⧸ componentClassificationOddCore G) = ⊥
    exact CFSG.ComponentClassification.OddCore.quotient_corefree G
  obtain ⟨S, hS2, hSHbar, hSnormal, hregular⟩ :=
    exists_normal_regular_twoSubgroup_of_corefree Hbar hHbar hQrank hQcore
  have hPbarH : Pbar ≤ Hbar := Subgroup.map_mono hPH
  have hPbarNormS : Pbar ≤ Subgroup.normalizer (S : Set Q) :=
    hPbarH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hSHbar).mp hSnormal)
  let alpha : Q ⧸ Hbar := QuotientGroup.mk 1
  have hstabilizer : MulAction.stabilizer Q alpha = Hbar := by simp [alpha]
  have hSalpha : S ≤ MulAction.stabilizer Q alpha := by rwa [hstabilizer]
  have halpha : alpha ∈ fixedPointsOfSubgroup Q (Q ⧸ Hbar) Pbar := by
    intro x hx
    apply MulAction.mem_stabilizer_iff.mp
    rw [hstabilizer]
    exact hPbarH hx
  have hkernel : q.ker = R := QuotientGroup.ker_mk' R
  have hkernelH : q.ker ≤ H := by rwa [hkernel]
  have hthreeQ : 3 ≤ Nat.card {omega : Q ⧸ Hbar //
      omega ∈ fixedPointsOfSubgroup Q (Q ⧸ Hbar) Pbar} := by
    change 3 ≤ Nat.card {omega : Q ⧸ H.map q //
      ∀ x ∈ P.map q, x • omega = omega}
    rw [← cosetProjection_fixed_card q H P (QuotientGroup.mk'_surjective R) hkernelH,
      ← rightCoset_fixed_card H P]
    exact hthree
  obtain ⟨u, huH, hu, huNormalizer⟩ :=
    exists_local_normalizer_involution_of_regular_twoSubgroup
      hS2 hSalpha hPbarNormS hregular halpha hthreeQ
  have huHbar : u ∈ Hbar := by rwa [hstabilizer] at huH
  have hkernelOdd : Odd (Nat.card q.ker) := by rwa [hkernel]
  have hkernelIntersection : ∃ T : Sylow p q.ker,
      (T : Subgroup q.ker).map q.ker.subtype = P ⊓ q.ker := by
    rw [hkernel]
    exact hintersection
  obtain ⟨v, hvNormalizer, hv, hvImage⟩ :=
    normalizer_involution_lift_of_sylow_intersection hp q
      (QuotientGroup.mk'_surjective R) hkernelOdd P hP hkernelIntersection hu huNormalizer
  have hvH : v ∈ H := by
    have hpreimage : v ∈ (H.map q).comap q := by
      change q v ∈ Hbar
      rw [hvImage]
      exact huHbar
    rwa [Subgroup.comap_map_eq_self hkernelH] at hpreimage
  have hzInvolution : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp hz).2, (orderOf_eq_prime_iff.mp hz).1⟩
  obtain ⟨g, hgH, hconj⟩ := hnative.involutions_conjugate_in hzH hzInvolution hvH hv
  exact ⟨v, ⟨⟨⟨g, hgH⟩, hconj⟩, hvNormalizer⟩⟩

end CFSG.ProperTwoGeneratedCore
