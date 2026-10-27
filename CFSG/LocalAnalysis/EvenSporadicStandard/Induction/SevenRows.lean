module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowEntries

public section

namespace CFSG.EvenSporadicStandard.Induction

@[expose] def sevenTypes : List TauCeti.SporadicName := [.ONan, .Suz, .M, .B, .Co1, .HN, .Ru]

theorem sol78PredS_seven_of_entries
    (QON QSuz QM QB QCo1 QHN QRu : TauCeti.SporadicName → PairClass)
    (hON : EntryOK sevenTypes (rowEntry [.ONan] [] QON))
    (hSuz : EntryOK sevenTypes (rowEntry [.Suz] [.ONan] QSuz))
    (hM : EntryOK sevenTypes (rowEntry [.M] [] QM))
    (hB : EntryOK sevenTypes (rowEntry [.B] [.M] QB))
    (hCo1 : EntryOK sevenTypes (rowEntry [.Co1] [] QCo1))
    (hHN : EntryOK sevenTypes (rowEntry [.HN] [] QHN))
    (hRu : EntryOK sevenTypes (rowEntry [.Ru] [] QRu))
    (H : Type) [Group H] [Finite H] (hH : Balance.UHered H) : Sol78PredS sevenTypes H :=
  sol78PredS_sevenRows QON QSuz QM QB QCo1 QHN QRu (A := sevenTypes)
    (fun s hs => by simpa [sevenTypes] using hs)
    (fun r hr => by
      simp only [sevenRows, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [hON, hSuz, hM, hB, hCo1, hHN, hRu]) H hH

end CFSG.EvenSporadicStandard.Induction
