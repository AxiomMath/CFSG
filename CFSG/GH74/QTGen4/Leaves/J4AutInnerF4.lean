module

public import CFSG.GH74.Filter.Sporadic.J4
public import CFSG.GH74.QTGen4.DCopy.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain

public section

namespace CFSG.GH74.QTGen4.Leaves

theorem j4AutInner_F4_holds :
    CFSG.QuasithinUnique.Ch1.J4AutInner_F4 := by
  intro K _ _ hK
  obtain ⟨e⟩ := hK
  exact (CFSG.GH74.Filter.not_gen4_J4
    (CFSG.GH74.Gen4.of_mulEquiv e (Finite4.gen4 (G := K)))).elim

end CFSG.GH74.QTGen4.Leaves
