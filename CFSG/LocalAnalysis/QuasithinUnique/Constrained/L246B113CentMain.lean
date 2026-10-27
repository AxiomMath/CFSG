module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentSmall

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Blueprint

theorem sylowAutTrivial_of_native
    (h : AsLieRank2SylowAut) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (hnat : SQTKCharTwoOrAltNative S) :
    SylowAutTrivial S := by
  rcases hnat with ⟨n, hn5, hn8, ⟨e⟩⟩ | h5 | h7' | h9 | hu | ⟨⟨f, hf⟩ | ht⟩ | ⟨n, hn, hm⟩
  · have : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact sylowAutTrivial_alt (Or.inl rfl) e
    · exact sylowAutTrivial_alt (Or.inr (Or.inl rfl)) e
    · exact SylowAutTrivial.of_mulEquiv e sylowAutTrivial_alt_seven
    · exact sylowAutTrivial_alt (Or.inr (Or.inr rfl)) e
  · exact sylowAutTrivial_model_five h5
  · exact sylowAutTrivial_model_seven h7'
  · exact sylowAutTrivial_model_nine h9
  · exact sylowAutTrivial_psu_three_three hS hnc hu
  · rcases hf with ⟨hf2, hm⟩ | ⟨hf1, hm⟩ | ⟨hf2, hm⟩ | ⟨hf2, hm⟩ | ⟨hf2, hm⟩ | ⟨hf1, hm⟩ |
      ⟨hodd, hf3, hm⟩ | ⟨hodd, hf3, hm⟩
    · exact sylowAutTrivial_isPSL_two hm
    · rcases Nat.eq_or_lt_of_le hf1 with rfl | hf2
      · exact sylowAutTrivial_psl_three_two hm
      · exact h S (Or.inl ⟨f, Or.inl ⟨hf2, hm⟩⟩)
    · exact sylowAutTrivial_isPSU_three hf2 hm
    · exact h S (Or.inl ⟨f, Or.inr (Or.inl ⟨hf2, hm⟩)⟩)
    · exact h S (Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf2, hm⟩))⟩)
    · exact h S (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inl ⟨hf1, hm⟩)))⟩)
    · exact h S (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr ⟨hodd, hf3, hm⟩)))⟩)
    · exact sylowAutTrivial_isSz hm
  · exact h S (Or.inr (Or.inl ht))
  · rcases hn with rfl | rfl
    · exact sylowAutTrivial_psl_four_two hm
    · exact h S (Or.inr (Or.inr hm))

theorem asLieAltSylowCentralizerList_of
    (h : AsLieRank2SylowAut) :
    AsLieAltSylowCentralizerList := by
  intro Ω _ _ L T hq _ _ hnat hT x hxN hxT hxo
  exact centralizes_of_sylowAutTrivial hq hT (sylowAutTrivial_of_native h hq.2.1 hq.2.2 hnat) hxN
    hxT hxo

end CFSG.QuasithinUnique.Bridge
