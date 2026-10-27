module

public import CFSG.GH74.Filter.Sporadic.Ru
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique

theorem not_isSporadic_Ru_of_gen4 {G : Type} [Group G] [Finite G]
    (hG : CFSG.GH74.Gen4 G) (K : Subgroup G) (hK : IsSporadic .Ru ↥K) : False := by
  obtain ⟨e⟩ := hK
  exact CFSG.GH74.Filter.not_gen4_Ru (CFSG.GH74.Gen4.of_mulEquiv e (CFSG.GH74.Gen4.subgroup K hG))

end CFSG.GH74.QTGen4.Leaves
