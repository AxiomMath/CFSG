module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5V1367e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622t
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367n

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Exists1367TC_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∃ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) ∧ S.InYz K ∧
      S.Tv ≤ Subgroup.normalizer (K : Set G)

theorem exists1367TC_of_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h56 : AsB56) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) : Exists1367TC_F4 := by
  intro G _ _ T L V S hH
  obtain ⟨Kb, hKb⟩ := S.exists_goodComp_F4 h1222 h517 h56 hH
  obtain ⟨K, hK, hKK⟩ :=
    S.exists_cComp_autOn_eq h39 (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hH.hF) hKb.1
  have hgood : S.GoodComp (autOn K S.Uv) := by
    rw [hKK]
    exact hKb
  exact ⟨K, hK, S.inYz_of_goodComp_F4 h1222 h517 h37 h38 hH.hF hK hgood,
    S.Tv_le_normalizer_goodComp_F4 h1222 h517 h56 h37 h38 factSylowNormS5 factSylowNormSL3
      (swapL21367_of_F4 h1222 h517 h56) hH hK hgood⟩

theorem main1367_of_TC_F4 (hE : Exists1367TC_F4) (hL : List1367_F4) (h18 : Lemma13618_F4)
    (h19 : Lemma13619_F4) (h22 : Lemma13622C_F4) (h23 : Lemma13623C_F4) (hNQ : NotQS1367) :
    Main1367_F4 := by
  intro G _ _ T L V S hab hF hVv hJ
  have hH : S.Hyp1367 := ⟨hab, hF, hVv, hJ⟩
  obtain ⟨K, hKC, hK, hT⟩ := hE G T L V S hH
  obtain ⟨hqs, hlist⟩ := hL G T L V S hH K hK hT
  have h22' := h22 G T L V S hH K hKC hK hT
  have h23' := h23 G T L V S hH K hKC hK hT
  rcases hlist with ⟨n, F, _, _, hF2, he⟩ | ⟨n, F, _, _, hF2, he⟩ | ⟨n, F, _, _, hF2, he⟩ |
    ⟨n, F, _, _, hF2, he⟩ | h6 | h7 | h6h | ⟨F, _, _, hF2, he⟩ | h4 | h5
  · exact h18 G T L V S hH K hK hT n F hF2 he
  · have hn := two_le_of_field hF2
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have h1 : n = 1 := by omega
      subst h1
      exact h22'.1 F (by simpa using hF2) he
    · exact (h19 G T L V S hH K hK hT n F hn2 hF2).1 he
  · have hn := two_le_of_field hF2
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have h1 : n = 1 := by omega
      subst h1
      exact (hNQ _ hqs F (by simpa using hF2)).1 he
    · exact (h19 G T L V S hH K hK hT n F hn2 hF2).2.1 he
  · have hn := two_le_of_field hF2
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have h1 : n = 1 := by omega
      subst h1
      exact (hNQ _ hqs F (by simpa using hF2)).2 he
    · exact (h19 G T L V S hH K hK hT n F hn2 hF2).2.2 he
  · exact h22'.2.1 h6
  · exact h22'.2.2.2.2 h7
  · exact h22'.2.2.2.1 h6h
  · exact h22'.2.2.1 F hF2 he
  · exact h23'.1 h4
  · exact h23'.2 h5

end CFSG.Quasithin.H13.A5
