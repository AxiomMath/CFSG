module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporStruct
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicCoverReduce
public import CFSG.HardMathSupport.Solomon.Coordinator.SporCover
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MM22

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (SporadicMultipliers sporadicMultiplierOrder)

section SporData

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem T29Setup.card_center_spor (h : T29Setup X L x)
    (hSpM : SporadicMultipliers) (hZ : center ↥L ≠ ⊥)
    {s : TauCeti.SporadicName}
    (e : (↥L ⧸ center ↥L) ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    Nat.card ↥(center ↥L) = 3 ∧
      (s = .M22 ∨ s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Fi22 ∨ s = .Fi24Prime) := by
  have hdvd := card_center_dvd_sporadicMultiplierOrder hSpM h.comp.2.2 s e
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.center_isPGroup
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hZ
    exact Subgroup.card_eq_one.mp (by rw [hk, pow_zero])
  have h3 : 3 ∣ Nat.card ↥(center ↥L) := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  have hs := eq_of_three_dvd_sporadicMultiplierOrder (h3.trans hdvd)
  refine ⟨?_, hs⟩
  have h9 : ¬ 9 ∣ sporadicMultiplierOrder s := by
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sporadicMultiplierOrder]
  have hk1 : k = 1 := by
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    apply h9
    refine (pow_dvd_pow 3 hk2 : 3 ^ 2 ∣ 3 ^ k).trans ?_
    rw [← hk]
    exact hdvd
  rw [hk, hk1, pow_one]

theorem T29Setup.false_of_cover_J3
    (h : T29Setup X L x)
    (hcard3 : Nat.card ↥(center ↥L) = 3)
    (e : (↥L ⧸ center ↥L) ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group) :
    False := by
  have h1 := sporCover_J3_pRank_ge_four ↥L h.isPerfect hcard3 ⟨e⟩
  have h2 := h.pRank_component_le
  omega

theorem T29Setup.false_of_cover_McL
    (h : T29Setup X L x) (hcard3 : Nat.card ↥(center ↥L) = 3)
    (e : (↥L ⧸ center ↥L) ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group) :
    False := by
  have h1 := sporCover_McL_pRank_ge_four ↥L h.isPerfect hcard3 ⟨e⟩
  have h2 := h.pRank_component_le
  omega

theorem T29Setup.false_of_cover_Suz
    (h : T29Setup X L x)
    (hcard3 : Nat.card ↥(center ↥L) = 3)
    (e : (↥L ⧸ center ↥L) ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Suz).Group) :
    False := by
  have h1 := sporCover_Suz_pRank_ge_four ↥L h.isPerfect hcard3 ⟨e⟩
  have h2 := h.pRank_component_le
  omega

theorem T29Setup.false_of_cover_Fi22
    (h : T29Setup X L x)
    (hcard3 : Nat.card ↥(center ↥L) = 3)
    (e : (↥L ⧸ center ↥L) ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) :
    False := by
  have h1 := sporCover_Fi22_pRank_ge_four ↥L h.isPerfect hcard3 ⟨e⟩
  have h2 := h.pRank_component_le
  omega

theorem T29Setup.false_of_cover_Fi24Prime
    (h : T29Setup X L x) (hcard3 : Nat.card ↥(center ↥L) = 3)
    (e : (↥L ⧸ center ↥L) ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi24Prime).Group) : False := by
  have h1 := sporCover_Fi24Prime_pRank_ge_four ↥L h.isPerfect hcard3 ⟨e⟩
  have h2 := h.pRank_component_le
  omega

end SporData

theorem abelian_three_card_le_nine_hatM22 {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) (hZ : Nat.card (Subgroup.center K) = 3)
    (e : (K ⧸ Subgroup.center K) ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group)
    (A : Subgroup K) (hA : IsPGroup 3 A) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh : IsHatMTwentyTwo K := ⟨hperf, hZ, ⟨e⟩⟩
  obtain ⟨R, hAR⟩ := hA.exists_le_sylow
  obtain ⟨hR, ⟨r, hr, s, hs, hrs⟩, -⟩ := t112m_sylow_hatM22 hh R
  have hdvd : Nat.card A ∣ 3 ^ 3 := by
    have h1 := Subgroup.card_dvd_of_le hAR
    rw [hR] at h1
    simpa using h1
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  by_contra hgt
  have hk3' : k = 3 := by
    by_contra hne
    have hk2 : k ≤ 2 := by omega
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  have hAeq : A = (R : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hAR (by rw [hR, hk, hk3']; norm_num)
  have hrA : r ∈ A := hAeq ▸ hr
  have hsA : s ∈ A := hAeq ▸ hs
  exact hrs (hcomm r hrA s hsA)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
