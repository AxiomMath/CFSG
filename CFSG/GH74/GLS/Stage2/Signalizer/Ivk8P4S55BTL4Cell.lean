module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4C3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFL
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem FL4.of_mulEquiv' {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : FL4 Y) :
    FL4 Y' := by
  obtain ⟨p, f, hp, hf, hp2, hq8, hlie⟩ := h
  exact ⟨p, f, hp, hf, hp2, hq8, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hlie⟩

theorem vFam_fl4 : VFam FL4 where
  iso e h := FL4.of_mulEquiv' e h
  bad k _ _ _ _ hF := by
    obtain ⟨p, f, hp, hf, hp2, -, hlie⟩ := hF
    exact not_kindFactorAll_fl4 hp hp2 hf hlie k
  char Y _ _ hF := by
    obtain ⟨p, f, hp, hf, hp2, hq8, hlie⟩ := hF
    have hd : FL4d p Y := ⟨f, hf, hq8, hlie⟩
    obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hlie
    refine ⟨p, ⟨hp, hp2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd))))))⟩,
      fun h120 => ?_, outerFalseNS_of_fl4d hp hp2 hd, fun k hk hBT => ?_⟩
    · have hFodd : Odd (Nat.card F) := by
        rw [hcard, Nat.odd_iff]
        exact Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
      have h3 : 3 ≤ Nat.card F := by
        rw [hcard]
        have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        have := Nat.odd_iff.mp hFodd
        omega
      apply not_card_dvd_factorial_projectiveSL4 hFodd h3
      rw [← Nat.card_congr e.toEquiv]
      exact h120.trans (by decide)
    · exact BL4.not_btConfig_l4 hk hp hp2 hf hq8 hcard (BTConfig.of_mulEquiv e hBT)

theorem cellV_fl4 (hInv : InvSec) (hX : Cross55) : CellV FL4 :=
  cellV_of_vfam hInv hX vFam_fl4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
