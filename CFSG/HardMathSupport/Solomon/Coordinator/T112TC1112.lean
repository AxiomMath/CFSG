module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTables
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicCoverReduce
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Main

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator

structure CoverT10112 : Prop where
  G23 : ∀ (L : Type) [Group L] [Finite L], IsHatGTwoThree L →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)
  J3 : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)
  McL : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)
  Suz : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Suz).Group) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)
  Fi22 : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)
  Fi24Prime : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi24Prime).Group) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)

theorem tables112Types_T10_11_2_of_cover (hSpM : Tables.Multiplier.SporadicMultipliers)
    (h113 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      CFSG.Open.IsKGroup K → Nat.card (Subgroup.center K) = 3 → LieCentralQuotient K →
      CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 4 →
        IsTenElevenOne K ∨ IsHatGTwoThree K)
    (C : CoverT10112) :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      CFSG.Open.IsKGroup K → Nat.card (Subgroup.center K) = 3 →
      CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
        IsTenElevenOne K ∨ IsHatON K := by
  intro K _ _ hq hK hZ hrk
  have hperf : Group.IsPerfect K := ⟨hq.1⟩
  have h3Z : 3 ∣ Nat.card (Subgroup.center K) := by rw [hZ]
  rcases centralQuotient_family hq hK with hA | hL | hS
  · obtain ⟨n, hn, ⟨e⟩⟩ := Tables.Alt.alt_data hA hq
    have hn67 := ((Tables.Alt.center_facts hn e Nat.prime_three (by norm_num)).2 h3Z).2
    left
    rcases hn67 with rfl | rfl
    · exact Or.inl ⟨hq.1, hZ, ⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨hq.1, hZ, ⟨e⟩⟩)
  · rcases h113 K hq hK hZ hL (by omega) with h | h
    · exact Or.inl h
    · exfalso
      have := C.G23 K h
      omega
  · obtain ⟨s, ⟨e⟩⟩ := hS
    have hs := eq_of_three_dvd_sporadicMultiplierOrder
      (h3Z.trans (card_center_dvd_sporadicMultiplierOrder hSpM hq s e))
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hq.1, hZ, ⟨e⟩⟩)))
    · exfalso
      have := C.J3 K hperf hZ ⟨e⟩
      omega
    · exfalso
      have := C.McL K hperf hZ ⟨e⟩
      omega
    · exfalso
      have := C.Suz K hperf hZ ⟨e⟩
      omega
    · exact Or.inr ⟨hq.1, hZ, ⟨e⟩⟩
    · exfalso
      have := C.Fi22 K hperf hZ ⟨e⟩
      omega
    · exfalso
      have := C.Fi24Prime K hperf hZ ⟨e⟩
      omega

end CFSG.HardMathSupport.Solomon.Coordinator
