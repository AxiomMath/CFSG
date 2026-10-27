module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1Q8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1Z

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

theorem a5_step1
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (cfg : A5Cfg G T M H S L) : A5Step1 T M H S L := by
  have hcs := cfg.cs
  have hj := cfg.single
  have hTC := a5_TC_eq_bot h247 h245_4 hC54 h314 cfg
  have F := h247_facts h247 hcs cfg.alt5 hj
  have hQ := blockQ_eq_blockU h245_4 hcs hj
  obtain ⟨D, hsurj, hker, hRE, hRE', hHeq⟩ := exists_stdData hcs hj cfg.alt5 F hQ hC54
  let C : StdCfg T M H S L := ⟨hcs, hj, F, D, hsurj, hker, hRE, hRE', hHeq⟩
  obtain ⟨X⟩ := exists_sec C hTC
  exact
    { index_two := F.index_two
      join_eq := hHeq
      P_le := X.P_le_S
      q8 := X.q8
      S_eq := X.S_eq
      frattini_le := X.frattini_le
      Z_card := X.Z_card
      Z_eq := X.Z_eq
      Z_le := X.Z_le }

theorem lemma2_4_29_1
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) : Lemma2_4_29_1 := by
  intro G _ _ T M H S L cfg
  exact a5_step1 h247 h245_4 hC54 h314 cfg

end CFSG.QuasithinUnique.A5
