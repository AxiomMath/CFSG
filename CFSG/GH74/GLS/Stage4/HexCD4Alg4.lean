module

public import CFSG.GH74.GLS.Stage4.HexCD4Gal

public section

namespace CFSG.GH74.GLS.Stage4.Hex

variable {F K : Type} [Field F] [Field K]

theorem GalData.two_ne_zero_K (G : GalData F K) (h2 : (2 : F) ≠ 0) : (2 : K) ≠ 0 := by
  intro h
  apply h2
  apply G.θ.injective
  rw [map_ofNat, map_zero]
  exact h

end CFSG.GH74.GLS.Stage4.Hex
