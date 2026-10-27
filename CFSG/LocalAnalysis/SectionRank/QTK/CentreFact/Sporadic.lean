module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.OddCover
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog
public import CFSG.Sporadic.Recognition.McLMultiplierCert

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup CFSG.Blueprint

theorem not_dvd_card_center_of_M12
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .M12) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (center Y) :=
  not_dvd_card_center_of_odd_cover_trivial hY e hr hr2 fun _ _ _ _ π hπ hC hodd =>
    M12_perfect_odd_cover_trivial π hπ hC hodd

theorem not_dvd_card_center_of_M24
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .M24) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (center Y) :=
  not_dvd_card_center_of_odd_cover_trivial hY e hr hr2 fun _ _ _ _ π hπ hC hodd =>
    M24_perfect_odd_cover_trivial π hπ hC hodd

theorem not_dvd_card_center_of_J2
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .J2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (center Y) :=
  not_dvd_card_center_of_odd_cover_trivial hY e hr hr2 fun _ _ _ _ π hπ hC hodd =>
    J2_perfect_odd_cover_trivial π hπ hC hodd

theorem not_dvd_card_center_of_HS
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .HS) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (center Y) :=
  not_dvd_card_center_of_odd_cover_trivial hY e hr hr2 fun _ _ _ _ π hπ hC hodd =>
    HS_perfect_odd_cover_trivial π hπ hC hodd

theorem not_dvd_card_center_of_He
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .He) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (center Y) :=
  not_dvd_card_center_of_odd_cover_trivial hY e hr hr2 fun _ _ _ _ π hπ hC hodd =>
    He_perfect_odd_cover_trivial π hπ hC hodd

theorem not_dvd_card_center_of_Ru
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .Ru) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (center Y) :=
  not_dvd_card_center_of_odd_cover_trivial hY e hr hr2 fun _ _ _ _ π hπ hC hodd =>
    Ru_perfect_odd_cover_trivial π hπ hC hodd

theorem not_dvd_card_center_of_J4 (hJ4 : J4OrderHyp)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .J4) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (center Y) :=
  not_dvd_card_center_of_odd_cover_trivial hY e hr hr2 fun _ _ _ _ π hπ hC hodd =>
    J4_perfect_odd_cover_trivial hJ4 π hπ hC hodd

theorem not_dvd_card_center_of_McL_ne_three
    {Y : Type} [Group Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .McL) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) :
    ¬ r ∣ Nat.card (center Y) := fun hrZ =>
  hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
    (hrZ.trans
      (CFSG.Sporadic.Recognition.McLMultiplier.card_center_dvd_three_of_certificate hY.1 e)))

end CFSG.SectionRank.QTK.CentreFact
