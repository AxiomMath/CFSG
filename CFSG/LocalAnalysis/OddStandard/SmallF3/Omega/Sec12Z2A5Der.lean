module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.OutRows

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed
  CFSG.EvenSporadicStandard.HSStd.InvCent.Harada CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial

theorem card_outer_L216_dvd_twelve {T : Type} [Group T] (h : LieModel T .PSL 2 2 4) :
    Nat.card (Outer T) ∣ 12 := by
  have hM := h.statedClassicalModel_of_ne_zero (by norm_num)
  exact ((linear_model_outer_two_part_bound T 2 2 4 hM).2.2.2.1 rfl).trans (by decide)

theorem card_outer_U34_dvd_twelve {T : Type} [Group T] (h : LieModel T .PSU 3 2 2) :
    Nat.card (Outer T) ∣ 12 := by
  have hM := h.statedClassicalModel_of_ne_zero (by norm_num)
  rw [(unitary_model_outer_two_part_bound T 3 2 2 hM).2.2.1]
  decide

theorem z2a5_derived_le {Y : Type} [Group Y] [Finite Y] {S : Subgroup Y} (hS : FixedData Y S)
    (hT : LieModel ↥S .PSL 2 2 4 ∨ LieModel ↥S .PSU 3 2 2 ∨ LieModel ↥S .PSL 3 2 2) :
    derivedSeries Y 2 ≤ S := by
  haveI := hS.normal
  have h12 : Nat.card (Outer ↥S) ∣ 12 := by
    rcases hT with h | h | h
    · exact card_outer_L216_dvd_twelve h
    · exact card_outer_U34_dvd_twelve h
    · exact card_outer_L34 h
  have hd : Nat.card (outerHom S).range ∣ 12 := (Subgroup.card_subgroup_dvd_card _).trans h12
  exact derivedSeries_le_of_outer hS.cent 2 (derivedSeries_two_eq_bot_of_card_dvd_twelve hd)

end CFSG.OddStandard.SmallF3.Omega
