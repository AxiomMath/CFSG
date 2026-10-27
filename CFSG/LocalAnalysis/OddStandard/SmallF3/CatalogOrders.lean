module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Facts
public import CFSG.GH74.Generic.S45.LSporJ2
public import CFSG.RankThree.PartTwo.Census.Sporadic.J3
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatFittingTransfer

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard.SmallF3Interfaces

theorem le_card_of_smallF3LieQuotient {Q : Type} [Group Q] (hQ : SmallF3LieQuotient Q) :
    5616 ≤ Nat.card Q := by
  have hmem := card_mem_smallF3Orders hQ
  simp only [smallF3Orders, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h <;> omega

theorem not_card_dvd_card_of_isSporadic
    {G Q : Type} [Group G] [Group Q] (hQ : SmallF3LieQuotient Q)
    (hG : IsSporadic G .M11 ∨ IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .HS) :
    ¬ Nat.card Q ∣ Nat.card G := by
  have hmem := card_mem_smallF3Orders hQ
  simp only [smallF3Orders, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    or_false] at hmem
  rcases hG with h | h | h | h
  · have hc : Nat.card G = 7920 :=
      CFSG.GH74.card_eq_of_isSporadic (s := .M11) (n := 7920)
        CFSG.Sporadic.Mathieu.card_M11 h
    rw [hc]
    rcases hmem with h | h | h | h | h | h | h | h <;>
      rw [h, Nat.dvd_iff_mod_eq_zero] <;> decide +kernel
  · have hc : Nat.card G = 2 ^ 6 * 3 ^ 3 * 5 * 11 :=
      CFSG.GH74.card_of_isSporadic_M12 h
    rw [hc]
    rcases hmem with h | h | h | h | h | h | h | h <;>
      rw [h, Nat.dvd_iff_mod_eq_zero] <;> decide +kernel
  · have hc : Nat.card G = 2 ^ 3 * 3 * 5 * 7 * 11 * 19 :=
      CFSG.GH74.card_of_isSporadic_J1 h
    rw [hc]
    rcases hmem with h | h | h | h | h | h | h | h <;>
      rw [h, Nat.dvd_iff_mod_eq_zero] <;> decide +kernel
  · have hc : Nat.card G = 44352000 :=
      CFSG.GH74.card_eq_of_isSporadic (s := .HS) (n := 44352000)
        CFSG.Sporadic.HS.card_HS h
    rw [hc]
    rcases hmem with h | h | h | h | h | h | h | h <;>
      rw [h, Nat.dvd_iff_mod_eq_zero] <;> decide +kernel

theorem card_le_of_isSporadic_J2
    {G : Type} [Group G] [Finite G] (hG : IsSporadic G .J2) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ≤ centralizer ({t} : Set G)) : Nat.card H ≤ 1920 := by
  obtain ⟨e⟩ := hG
  let φ : G ≃* CFSG.ComponentClassification.J2Cover.P :=
    e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have hle : Nat.card H ≤ Nat.card (Subgroup.centralizer ({t} : Set G)) :=
    Subgroup.card_le_of_le hH
  rw [Nat.card_congr (CFSG.ComponentClassification.BMCase.gmatCentralizerEquiv φ t).toEquiv]
    at hle
  rcases CFSG.GH74.Generic.S45.j2_involution_data (p := φ t)
      (by rw [MulEquiv.orderOf_eq]; exact ht) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rw [h] at hle <;> omega

theorem card_le_of_isSporadic_J3
    {G : Type} [Group G] [Finite G] (hG : IsSporadic G .J3) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ≤ centralizer ({t} : Set G)) : Nat.card H ≤ 1920 := by
  obtain ⟨e⟩ := hG
  let φ : G ≃* ↥CFSG.Sporadic.Schreier.j3P := e.trans CFSG.Sporadic.Schreier.j3PermEquiv
  have hle : Nat.card H ≤ Nat.card (Subgroup.centralizer ({t} : Set G)) :=
    Subgroup.card_le_of_le hH
  rw [Nat.card_congr (CFSG.ComponentClassification.BMCase.gmatCentralizerEquiv φ t).toEquiv,
      CFSG.RankThree.PartTwo.Census.card_centralizer_j3P
        (by rw [MulEquiv.orderOf_eq]; exact ht)] at hle
  omega

end CFSG.OddStandard.SmallF3
