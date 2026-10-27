module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.SmallOddCore.HSAut

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem card_mulAut_of_isSporadic_hs
    {Y : Type} [Group Y] (h : IsSporadic Y .HS) :
    Nat.card (MulAut Y) = 88704000 := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.HS := e₀
  obtain ⟨-, -, -, -, hcard⟩ := CFSG.Sporadic.SmallOddCore.hs_full_automorphism_model
  have eP : Y ≃* CFSG.Sporadic.Schreier.hsP := e.trans CFSG.Sporadic.Schreier.hsPermEquiv
  rw [Nat.card_congr (MulAut.congr eP).toEquiv, hcard]

end CFSG.EvenSporadicStandard.HSStd
