module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SetupG
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42TransA
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42TransB
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Setup

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem GomiU42SetupG.toSetup {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {e t : G}
    {J₀ E₂ : Subgroup G} (h : GomiU42SetupG G Bs e t J₀ E₂) :
    GomiU42Setup ↥Bs ⟨e, h.e_mem⟩ ⟨t, h.t_mem⟩ (J₀.subgroupOf Bs) (E₂.subgroupOf Bs) where
  kGroup := h.kGroup
  e_central := fun y => Subtype.ext (h.e_central y y.2)
  orderOf_e := by
    rw [Subgroup.orderOf_mk]
    exact h.orderOf_e
  t_sq := Subtype.ext h.t_sq
  t_ne_one := fun h1 => h.t_ne_one (congrArg Subtype.val h1)
  lieModel := lieModel_subgroupOf_PSU h.J₀_le h.lieModel
  le_centralizer := le_centralizer_subgroupOf h.t_mem h.le_centralizer
  inf_e := inf_e_subgroupOf h.e_mem h.J₀_le h.inf_e
  centralizer_eq := centralizer_eq_subgroupOf h.e_mem h.t_mem h.J₀_le h.centralizer_eq
  inf_t := inf_t_subgroupOf h.e_mem h.t_mem h.J₀_le h.inf_t
  two_pow_dvd := h.two_pow_dvd
  elementary := elementary_subgroupOf h.E₂_le h.elementary
  card_E₂ := (card_subgroupOf_of_le h.E₂_le).trans h.card_E₂
  mem_normalizer := mem_normalizer_subgroupOf h.t_mem h.mem_normalizer
  isPGroup_sup := isPGroup_sup_subgroupOf h.t_mem h.E₂_le h.isPGroup_sup
  card_inf := card_inf_subgroupOf h.t_mem h.E₂_le h.card_inf
  inf_le := inf_le_subgroupOf h.t_mem h.inf_le

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
