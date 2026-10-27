module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTU4M3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFU
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem FU4.of_mulEquiv' {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : FU4 Y) :
    FU4 Y' := by
  obtain ⟨p, f, hp, hf, hp2, hq8, hlie⟩ := h
  exact ⟨p, f, hp, hf, hp2, hq8, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hlie⟩

theorem vFam_fu4 : VFam FU4 where
  iso e h := FU4.of_mulEquiv' e h
  bad k _ _ _ _ hF := by
    obtain ⟨p, f, hp, hf, hp2, -, hlie⟩ := hF
    exact not_kindFactorAll_fu4 hp hp2 hf hlie k
  char Y _ _ hF := by
    obtain ⟨p, f, hp, hf, hp2, hq8, hlie⟩ := hF
    have hd : FU4d p Y := ⟨f, hf, hq8, hlie⟩
    obtain ⟨-, K, _, _, hcard, ⟨e₀⟩⟩ := Final.lieModel_psu_unpack hlie
    have : Fact p.Prime := ⟨hp⟩
    have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
    have : CharP K p := h.charP
    obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
    have e : Y ≃* hypPSU h 2 0 := e₀.trans (hypPSUEquivStatedProj h hR₀ (by omega)).symm
    refine ⟨p, ⟨hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl hd)))))))⟩, fun h120 => ?_, outerFalseNS_of_fu4d hp hp2 hd, fun k hk hBT => ?_⟩
    · apply not_card_dvd_factorial_statedProj_four hp2 hf hcard
      rw [← Nat.card_congr e₀.toEquiv]
      exact h120.trans (by decide)
    · exact BU4.not_btConfig_u4 hk h hp2 (BTConfig.of_mulEquiv e hBT)

theorem cellV_fu4 (hInv : InvSec) (hX : Cross55) : CellV FU4 :=
  cellV_of_vfam hInv hX vFam_fu4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
