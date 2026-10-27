module

public import CFSG.GH74.GLS.SP.Local.SPLCtStage2
public import CFSG.GH74.GLS.SP.Local.SPLCtU
public import CFSG.GH74.GLS.SP.Local.SPLCtD
public import CFSG.GH74.GLS.SP.Local.SPLCtA1
public import CFSG.GH74.GLS.SP.Local.SPLCtA2a
public import CFSG.GH74.GLS.SP.Local.SPLCtA2b

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup

theorem ctA_exists {G : Type} [Group G] [Finite G] (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0)
    (hK1 : SPLPumpAt D) (hK3 : ∀ u : G, SPLCtU D u → SPLCenUAt D u) :
    ∃ u : G, SPLCtUD D u ∧ SPLCtA D := by
  obtain ⟨u, hu⟩ := exists_u D hs
  have hd := exists_d D hs hu.mem_I hu.ord
  have hA0 := A0_cyclic D hs hu (hK3 u hu) hd
  have hcomm := Aprime_centralizes_I D hs hK1 hu hA0
  exact ⟨u, ⟨hu, hd, hK3 u hu⟩, ctA_of_layer D hs hK1 hu hA0 hcomm⟩

end CFSG.GH74.GLS.SP.Local
