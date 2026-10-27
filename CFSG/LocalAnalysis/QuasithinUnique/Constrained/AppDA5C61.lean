module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDA5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDC61
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppC56A5

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem c61_a5
    {T M H S L : Subgroup G} (hcs : ConstrainedSetting G T M H S L)
    (h5 : IsAltType L 5) (hj : conjJoin S L = L) : C61Concl T H S L := by
  obtain ⟨C⟩ := AppC.nonempty_cfg hcs hj h5
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two hcs
  have hO2 : blockU0 S L = pCoreOf 2 (conjJoin S L) :=
    (AppC.c56A5Case G T M H S L hcs h5 hj M₀ hSM hMT h2).1
  refine c61_gen (GCfg.ofCfg C) hO2 ?_ (Or.inl ⟨h5, hj⟩) (fun h3 _ => AppC.not_alt3_of_alt5 h5 h3)
  rintro - (⟨n, hn, hlin⟩ | h3)
  · exact AppC.not_lin2_of_alt5 (C56.isShort hcs) h5 hn hlin
  · exact AppC.not_alt3_of_alt5 h5 h3

end CFSG.QuasithinUnique.AppD
