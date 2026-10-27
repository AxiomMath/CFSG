module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRowsLarge
public import CFSG.Sporadic.Recognition.ThMultiplier

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Monster.Schur

theorem noPerfectDoubleCover_of_equiv_Th
    {T : Type} [Group T]
    (hT : Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.Carrier .Th)) :
    NoPerfectDoubleCover T := by
  obtain ⟨e⟩ := hT
  obtain ⟨H, hodd, hperf, hnd⟩ :=
    CFSG.Sporadic.Recognition.ThMultiplier.exists_odd_perfect_noCover
  have hfin : Finite CFSG.Sporadic.Th.J := inferInstance
  have hJ : NoPerfectDoubleCover CFSG.Sporadic.Th.J :=
    noPerfectDoubleCover_of_odd_index H hodd hperf hnd
  have e' : T ≃* CFSG.Sporadic.Th.J := e.trans CFSG.Sporadic.Th.thEquivJ
  exact NoPerfectDoubleCover.of_mulEquiv (G := ↥CFSG.Sporadic.Th.J) (H := T) e'.symm hJ

theorem rowBound_Th :
    RowBound .Th :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs =>
    center_eq_bot_of_noPerfectDoubleCover
      (noPerfectDoubleCover_of_equiv_Th (T := L ⧸ center L) hs) hq hZ (MulEquiv.refl _)

end CFSG.EvenSporadicStandard
