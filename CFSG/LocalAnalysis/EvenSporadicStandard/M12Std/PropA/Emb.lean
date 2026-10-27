module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.TransportAPI

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

structure IsEmb {G P : Type*} [Group G] [Group P] (L : Subgroup G) (t x : G) (K D : Subgroup P)
    (t₀ x₀ : P) (ι : ↥(centralizer ({t} : Set G)) →* P) : Prop where
  inj : Function.Injective ι
  range_eq : ι.range = K
  push_L : push ι L = D
  map_t : ∀ c : ↥(centralizer ({t} : Set G)), (c : G) = t → ι c = t₀
  map_x : ∀ c : ↥(centralizer ({t} : Set G)), (c : G) = x → ι c = x₀
  t_mem : t ∈ centralizer (L : Set G)
  x_mem : x ∈ L

end CFSG.EvenSporadicStandard.M12Std.PropA
