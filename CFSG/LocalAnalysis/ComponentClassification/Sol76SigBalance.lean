module

import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Local
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Setting
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Aux
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem pRank_coe_eq (X : Subgroup G) : CFSG.pRank 2 ↥X = CFSG.Open.pRank 2 X :=
  CFSG.SectionRank.pRank_coe_eq_openPRank 2 X

omit [Finite G] in
theorem kStarComponents_eq_range {r : ℕ} {Kf : Fin r → Subgroup G}
    (hiff : ∀ J : Subgroup G, (IsTwoComponentIn J N ∧ J ∈ solomonKStar G) ↔ ∃ i, Kf i = J) :
    kStarComponents N = Set.range Kf := by
  ext J
  exact (hiff J).trans (by simp only [Set.mem_range])

theorem three_le_pRank_of_ncard_eq_two (hN : IsSolomonChoice N)
    (hr : (kStarComponents N).ncard = 2) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') :
    3 ≤ CFSG.Open.pRank 2 ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K) ∨
      3 ≤ CFSG.Open.pRank 2 ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') := by
  obtain ⟨r, Kf, hinj, hiff, h2r, -, ⟨l, hl⟩, -⟩ := hN.1
  have hr2 : r = 2 := by
    rw [kStarComponents_eq_range hiff, Set.ncard_range_of_injective hinj, Nat.card_fin] at hr
    exact hr
  obtain ⟨i, hi⟩ := (hiff K).mp hK
  obtain ⟨j, hj⟩ := (hiff K').mp hK'
  have hij : i.val ≠ j.val := fun h => hne (by rw [← hi, ← hj, Fin.ext h])
  rw [pRank_coe_eq] at hl
  have hl2 : l.val = i.val ∨ l.val = j.val := by
    have := l.isLt
    have := i.isLt
    have := j.isLt
    omega
  rcases hl2 with hli | hlj
  · left
    rw [← hi, ← Fin.ext hli]
    exact hl
  · right
    rw [← hj, ← Fin.ext hlj]
    exact hl

theorem exists_involution_or_three_le_of_ncard_eq_two (hN : IsSolomonChoice N)
    (hr : (kStarComponents N).ncard = 2) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') :
    (∃ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
        orderOf z = 2) ∨
      (3 ≤ CFSG.Open.pRank 2 K ∧ 3 ≤ CFSG.Open.pRank 2 K' ∧
        (HasStronglyEmbedded ↥K ∨ HasStronglyEmbedded ↥K' →
          IsTwoDisconnected ↥K ∧ IsTwoDisconnected ↥K')) := by
  obtain ⟨r, Kf, hinj, hiff, h2r, -, -, h3⟩ := hN.1
  have hr2 : r = 2 := by
    rw [kStarComponents_eq_range hiff, Set.ncard_range_of_injective hinj, Nat.card_fin] at hr
    exact hr
  obtain ⟨i, hi⟩ := (hiff K).mp hK
  obtain ⟨j, hj⟩ := (hiff K').mp hK'
  have hij : i.val ≠ j.val := fun h => hne (by rw [← hi, ← hj, Fin.ext h])
  rcases h3 with h3 | h3 | ⟨h0, h1, hSE⟩
  · omega
  · left
    rw [pRank_coe_eq] at h3
    exact exists_orderOf_eq_two_of_pRank h3
  · right
    rw [pRank_coe_eq] at h0 h1
    have hcase : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) := by
      have := i.isLt
      have := j.isLt
      omega
    rcases hcase with ⟨hi0, hj1⟩ | ⟨hi1, hj0⟩
    · have hi' : Kf ⟨0, by omega⟩ = K := by rw [← hi]; exact congrArg Kf (Fin.ext hi0.symm)
      have hj' : Kf ⟨1, h2r⟩ = K' := by rw [← hj]; exact congrArg Kf (Fin.ext hj1.symm)
      rw [hi'] at h0 hSE
      rw [hj'] at h1 hSE
      exact ⟨h0, h1, hSE⟩
    · have hi' : Kf ⟨1, h2r⟩ = K := by rw [← hi]; exact congrArg Kf (Fin.ext hi1.symm)
      have hj' : Kf ⟨0, by omega⟩ = K' := by rw [← hj]; exact congrArg Kf (Fin.ext hj0.symm)
      rw [hj'] at h0 hSE
      rw [hi'] at h1 hSE
      exact ⟨h1, h0, fun h => (hSE h.symm).symm⟩

end CFSG.ComponentClassification.Sol76.Sig
