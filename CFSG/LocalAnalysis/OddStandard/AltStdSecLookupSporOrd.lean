module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporBase
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

theorem noLargeAlt_of_not_dvd {s : TauCeti.SporadicName}
    (hs : ¬ 181440 ∣ Nat.card (NativeSporadic.Carrier s)) : NoLargeAltComponents s := by
  constructor
  · intro G _ _ _ hG t ht B hB hAlt
    have hBt : Nat.card B ∣ Nat.card (centralizer ({t} : Set G)) :=
      Subgroup.card_subgroup_dvd_card B
    apply hs
    obtain ⟨e⟩ := hG
    have h2 : Nat.card (centralizer ({t} : Set G)) ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_congr e.toEquiv] at h2
    exact (dvd_card_of_isLargeAlt hAlt).trans (hBt.trans h2)
  · intro G _ _ _ _ hG α hα2 hα B hB hAlt
    have hBt : Nat.card B ∣ Nat.card (fixSub α) := Subgroup.card_subgroup_dvd_card B
    apply hs
    obtain ⟨e⟩ := hG
    have h2 : Nat.card (fixSub α) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_congr e.toEquiv] at h2
    exact (dvd_card_of_isLargeAlt hAlt).trans (hBt.trans h2)

theorem noLargeAlt_of_order
    {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨
      s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) :
    NoLargeAltComponents s := by
  refine noLargeAlt_of_not_dvd ?_
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show Nat.card (NativeSporadic.Carrier .M11) = Nat.card NativeSporadic.M11 from rfl,
      Sporadic.Mathieu.card_M11]; decide
  · rw [show Nat.card (NativeSporadic.Carrier .M12) = Nat.card NativeSporadic.M12 from rfl,
      Sporadic.Mathieu.card_M12]; decide
  · rw [show Nat.card (NativeSporadic.Carrier .M22) = Nat.card NativeSporadic.M22 from rfl,
      Sporadic.Mathieu.card_M22]; decide
  · rw [show Nat.card (NativeSporadic.Carrier .M23) = Nat.card NativeSporadic.M23 from rfl,
      Sporadic.Schreier.m23_card]; decide
  · rw [show Nat.card (NativeSporadic.Carrier .M24) = Nat.card NativeSporadic.M24 from rfl,
      Sporadic.Mathieu.card_M24]; decide
  · rcases SectionRank.card_small_sporadic (s := .J1) (Or.inr (Or.inr (Or.inr rfl))) with
      h | h | h | h <;> rw [h] <;> decide
  · rw [show Nat.card (NativeSporadic.Carrier .J2) = Nat.card NativeSporadic.J2 from rfl,
      Sporadic.J2.card_J2]; decide
  · rw [show Nat.card (NativeSporadic.Carrier .J3) = Nat.card NativeSporadic.J3 from rfl,
      Sporadic.J3.card_J3]; decide
  · rw [show Nat.card (NativeSporadic.Carrier .J4) = Nat.card NativeSporadic.J4 from rfl,
      Sporadic.J4.card_J4]; decide
  · rw [show Nat.card (NativeSporadic.Carrier .HS) = Nat.card NativeSporadic.HS from rfl,
      Sporadic.HS.card_HS]; decide
  · rw [show Nat.card (NativeSporadic.Carrier .He) = Nat.card NativeSporadic.He from rfl,
      Sporadic.He.card_He]; decide
  · rw [show Nat.card (NativeSporadic.Carrier .Ru) = Nat.card NativeSporadic.Ru from rfl,
      Sporadic.Ru.card_Ru]; decide

end CFSG.OddStandard.AltStdSec
