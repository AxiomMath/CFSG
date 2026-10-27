module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Blueprint CFSG.Quasithin

theorem two_le_pRank_three_of_sporadic
    {X : Type} [Group X] [Finite X]
    {s : TauCeti.SporadicName} (hs : IsBadSporadicName s ∨ s = .M22 ∨ s = .M23)
    (e : X ≃* NativeSporadic.Carrier s) : 2 ≤ CFSG.pRank 3 X := by
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl
  · exact two_le_pRank_three_M12 e
  · exact two_le_pRank_three_M24 e
  · exact two_le_pRank_three_J2 e
  · exact two_le_pRank_three_J4 e
  · exact two_le_pRank_three_HS e
  · exact two_le_pRank_three_He e
  · exact two_le_pRank_three_Ru e
  · exact (CFSG.RankThree.Asc83Table.M22.table ⟨e⟩).2.1.ge
  · exact (CFSG.RankThree.Asc83Table.M23.table ⟨e⟩).2.1.ge

theorem l239NotRankOne_sporadic
    {G : Type} [Group G] [Finite G] (L : Subgroup G)
    (h : IsBadSporadicQuot L ∨ IsM22M23Quot L) : ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L) := by
  intro hA
  have hrank := CFSG.QuasithinUnique.Id2519.lemma122Rank _ hA 3 Nat.prime_three (by norm_num)
  have h2 : 2 ≤ CFSG.pRank 3 (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases h with ⟨s, hs, ⟨e⟩⟩ | h | h
    · exact two_le_pRank_three_of_sporadic (Or.inl hs) e
    · obtain ⟨e⟩ := h
      exact two_le_pRank_three_of_sporadic (Or.inr (Or.inl rfl)) e
    · obtain ⟨e⟩ := h
      exact two_le_pRank_three_of_sporadic (Or.inr (Or.inr rfl)) e
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  omega

end CFSG.QuasithinUnique.Vol2Native.L239
