module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Main
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CoverRank
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TT1010
public import CFSG.RankThree.PartTwo.Sec4.Item47Native

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.T1b

theorem pRank_mulAut_le_of_coprime_outer_cover {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hcop : Nat.Coprime 3 (Nat.card (Outer (K ⧸ Subgroup.center K)))) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) :=
  (pRank_mulAut_le_of_quasisimple (p := 3) (by norm_num) hq).trans
    (pRank_three_mulAut_le_of_coprime_outer (center_quotient_eq_bot_of_quasisimple hq) hcop)

structure CoverT1068 : Prop where
  J3 : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group) →
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup L)
  McL : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group) →
    5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)
  Suz : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Suz).Group) →
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)
  Fi22 : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) →
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)
  Fi24Prime : ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
    Nat.card (Subgroup.center L) = 3 →
    Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi24Prime).Group) →
    8 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)

section Certs


theorem tables112Types_T10_6_8_of_cover (hSpM : Tables.Multiplier.SporadicMultipliers)
    (C : CoverT1068) :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      CFSG.Open.IsKGroup K → Nat.card (Subgroup.center K) = 3 →
      CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 4 →
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) = CFSG.Open.pRank 3 (⊤ : Subgroup K) + 1 →
        IsHatON K ∨ LieCentralQuotient K := by
  intro K _ _ hq hK hZ h4 hrk
  rcases centralQuotient_family hq hK with hA | hL | hS
  · exfalso
    have := Tables.Alt.pRank_aut_le_top hA hq Nat.prime_three (by norm_num)
    omega
  · exact Or.inr hL
  · obtain ⟨s, ⟨e⟩⟩ := hS
    have hperf : Group.IsPerfect K := ⟨hq.1⟩
    have h3Z : 3 ∣ Nat.card (Subgroup.center K) := by rw [hZ]
    have hs := eq_of_three_dvd_sporadicMultiplierOrder
      (h3Z.trans (card_center_dvd_sporadicMultiplierOrder hSpM hq s e))
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
      have hnot := CFSG.Quasithin.A318P.not_dvd_outer_M22 (e.trans b.symm) Nat.prime_three
        (by norm_num)
      have h1 := pRank_mulAut_le_of_coprime_outer_cover hq
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnot)
      have := pRank_quotient_le_of_le_two Nat.prime_three (by norm_num) h3Z
        (sporadicThreeRankLe_M22 _ ⟨e⟩)
      omega
    · exfalso
      obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
      have b : CFSG.Blueprint.NativeSporadic.Carrier .J3 ≃*
          (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group := b0
      have hnot := CFSG.Quasithin.A318P.not_dvd_outer_of_carrier (e.trans b.symm)
        CFSG.RankThree.PartTwo.Sec4.card_outer_J3 Nat.prime_three (by norm_num)
      have h1 := pRank_mulAut_le_of_coprime_outer_cover hq
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnot)
      have := C.J3 K hperf hZ ⟨e⟩
      omega
    · exfalso
      have := C.McL K hperf hZ ⟨e⟩
      omega
    · exfalso
      have := C.Suz K hperf hZ ⟨e⟩
      omega
    · exact Or.inl ⟨hq.1, hZ, ⟨e⟩⟩
    · exfalso
      have := C.Fi22 K hperf hZ ⟨e⟩
      omega
    · exfalso
      have := C.Fi24Prime K hperf hZ ⟨e⟩
      omega

end Certs

end CFSG.HardMathSupport.Solomon.Coordinator
