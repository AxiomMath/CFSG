module

public import CFSG.GH74.AS16.E2.Data
public import CFSG.GH74.KGroups.Sz8Tables

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

theorem szData :
    SzData where
  out_inner := fun _ _ _ hK φ n hφ => CFSG.GH74.KGroups.Sz8.out_inner hK φ n hφ
  sylow := by
    intro K _ _ hK Q hQ hQi
    obtain ⟨h1, h2, h3, x, hxN, hx⟩ := CFSG.GH74.KGroups.Sz8.bender hK Q hQ hQi
    exact ⟨h1, h2, h3, x, ⟨trivial, hxN⟩, hx⟩

end CFSG.GH74.AS16.E2
