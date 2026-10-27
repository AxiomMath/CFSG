module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.GSThmB CFSG.OddStandard.Solomon75

theorem card_eq_of_isSporadic_mcl {T : Type} [Group T]
    (hT : IsSporadic T .McL) : Nat.card T = 898128000 := by
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.McL.card_McL

theorem exists_involution_of_isSporadic_mcl {T : Type} [Group T]
    [Finite T] (hT : IsSporadic T .McL) : ∃ t : T, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card T := by rw [card_eq_of_isSporadic_mcl hT]; norm_num
  exact exists_prime_orderOf_dvd_card' 2 h2

theorem isDoubleCoverOfAlt_mcl
    {T : Type} [Group T]
    (hT : IsSporadic T .McL) {t : T} (ht : orderOf t = 2) :
    IsDoubleCoverOfAlt ↥(centralizer ({t} : Set T)) 8 := by
  obtain ⟨h1, h2, h3⟩ :=
    CFSG.Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate hT ht
  exact isDoubleCoverOfAlt_of_cover ht (by norm_num) h1 h2 h3

theorem stdHasIntrinsicAn_mcl_of_residuals
    (hsw : NoSwappedPair .McL) (hct : ContainerIsDoubleCover .McL) : StdHasIntrinsicAn .McL :=
  stdHasIntrinsicAn_of_residuals (n := 8)
    (fun _ _ _ hT => exists_involution_of_isSporadic_mcl hT)
    (fun _ _ hT _ ht => isDoubleCoverOfAlt_mcl hT ht) hsw hct

theorem mcl_not_standard
    (hS : Solomon2AnInput) (hI : StdHasIntrinsicAn .McL)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L) :
    ¬ IsSporadic L .McL := by
  intro hL
  have := h.simple
  have hLcard : Nat.card L = 898128000 := card_eq_of_isSporadic_mcl hL
  rcases mulEquiv_mcl_or_ly_of_hasIntrinsicAn hS (hI G L h hL) with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hGcard : Nat.card G = 898128000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.McL.card_McL
    exact h.ne_top ((Subgroup.card_eq_iff_eq_top L).1 (hLcard.trans hGcard.symm))
  · obtain ⟨t, ht, ht2⟩ := h.exists_involution_centralizer
    have hLle : L ≤ centralizer ({t} : Set G) := fun l hl =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)
    have hcard := CFSG.Sporadic.Recognition.LyonsSims.card_centralizer_of_equiv_ly ⟨e⟩ ht2
    have hle := Subgroup.card_le_of_le hLle
    rw [hLcard, hcard] at hle
    omega

end CFSG.EvenSporadicStandard.McLStd
