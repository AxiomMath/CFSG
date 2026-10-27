module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual
public import CFSG.Sporadic.McL.Simple
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Ly

public section

namespace CFSG.EvenSporadicStandard.LyStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB CFSG.EvenSporadicStandard.McLStd

theorem card_eq_of_isSporadic_ly {T : Type} [Group T]
    (hT : IsSporadic T .Ly) : Nat.card T = 51765179004000000 := by
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Ly.card_Ly

theorem exists_involution_of_isSporadic_ly {T : Type} [Group T]
    [Finite T] (hT : IsSporadic T .Ly) : ∃ t : T, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card T := by rw [card_eq_of_isSporadic_ly hT]; norm_num
  exact exists_prime_orderOf_dvd_card' 2 h2

theorem isDoubleCoverOfAlt_ly
    {T : Type} [Group T] (hT : IsSporadic T .Ly) {t : T}
    (ht : orderOf t = 2) : IsDoubleCoverOfAlt ↥(centralizer ({t} : Set T)) 11 := by
  obtain ⟨hq, hc, hquot⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple hT t ht
  exact ⟨hq, hc, hquot⟩

theorem stdHasIntrinsicAn_ly_of_maximal
    (hmax : CentralizerComponentMaximal .Ly) : StdHasIntrinsicAn .Ly :=
  stdHasIntrinsicAn_of_maximal (by norm_num)
    (fun _ _ _ hT => exists_involution_of_isSporadic_ly hT)
    (fun _ _ hT _ ht => isDoubleCoverOfAlt_ly hT ht) hmax

theorem stdHasIntrinsicAn_ly_of_residuals
    (hsw : NoSwappedPair .Ly) (hct : ContainerIsDoubleCover .Ly) : StdHasIntrinsicAn .Ly :=
  stdHasIntrinsicAn_of_residuals (n := 11)
    (fun _ _ _ hT => exists_involution_of_isSporadic_ly hT)
    (fun _ _ hT _ ht => isDoubleCoverOfAlt_ly hT ht) hsw hct

theorem ly_not_standard
    (hS : Solomon2AnInput) (hI : StdHasIntrinsicAn .Ly)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) :
    ¬ IsSporadic L .Ly := by
  intro hL
  have := h.simple
  have hLcard : Nat.card L = 51765179004000000 := card_eq_of_isSporadic_ly hL
  rcases mulEquiv_mcl_or_ly_of_hasIntrinsicAn hS (hI G L h hL) with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hGcard : Nat.card G = 898128000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.McL.card_McL
    have hle := Subgroup.card_le_card_group L
    rw [hLcard, hGcard] at hle
    omega
  · have hGcard : Nat.card G = 51765179004000000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Ly.card_Ly
    exact h.ne_top ((Subgroup.card_eq_iff_eq_top L).1 (hLcard.trans hGcard.symm))

end CFSG.EvenSporadicStandard.LyStd
