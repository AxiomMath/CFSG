module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAut

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

theorem pg_eq_autC : Pg = AutC :=
  Subgroup.eq_of_le_of_card_ge pg_le_autC (by rw [card_Pg]; exact card_autC_le)

end CFSG.EvenSporadicStandard.Fin76b.W16
