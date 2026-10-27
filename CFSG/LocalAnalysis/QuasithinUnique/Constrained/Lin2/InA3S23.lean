module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Syl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem lemma2_4_23_main (E : Lin2Hyp) : Lemma2_4_23_main := by
  intro G _ _ T M H S L D n hcfg s hs hsR hs2
  obtain ⟨h1, hO, hLs2⟩ := E.block_s hcfg hs hsR hs2
  obtain ⟨x, hx, hxS⟩ := E.exists_mem_T_centralizer_not_mem_S hcfg hs hsR hs2
  refine ⟨h1, E.R_s_eq_strongClosure hcfg hs hsR hs2 hx hxS, ⟨hO.symm, ?_⟩,
    ⟨E.T_eq_sup_centralizer hcfg hs hsR hs2, ⟨x, hx, hxS⟩,
      E.T_s_sylow hcfg hs hsR hs2 hO hLs2⟩⟩
  rw [← E.UQ hcfg]
  exact E.normalizer_U_s_le hcfg hs hsR hs2 hO

end CFSG.QuasithinUnique.Lin2
