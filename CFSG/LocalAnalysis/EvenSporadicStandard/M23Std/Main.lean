module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem center_eq_bot_of_isSporadic_M23
    {Y : Type} [Group Y] (hY : IsSporadic Y .M23) : center Y = ⊥ := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* NativeSporadic.M23 := e
  have hc := CFSG.Sporadic.Schreier.m23_center_eq_bot'
  refine eq_bot_iff.2 fun y hy => ?_
  have hmem : e' y ∈ center NativeSporadic.M23 := by
    rw [mem_center_iff] at hy ⊢
    intro g
    have h2 := congrArg e' (hy (e'.symm g))
    simpa using h2
  rw [hc, mem_bot] at hmem
  rw [mem_bot]
  exact e'.injective (hmem.trans (map_one e').symm)

theorem isSporadic_quotient_of_center_eq_bot {Y : Type} [Group Y] (h : center Y = ⊥)
    {s : TauCeti.SporadicName} (hs : IsSporadic Y s) : IsSporadic (Y ⧸ center Y) s := by
  obtain ⟨e⟩ := hs
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).trans e⟩

end CFSG.EvenSporadicStandard.M23Std
