module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverDihedral
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverEven
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem sylowCentralizerCentral_of_altList
    {X : Type} [Group X] [Finite X] (h : AltList X) :
    SylowCentralizerCentral X := by
  obtain ⟨n, h5, h8, ⟨e⟩⟩ := h
  interval_cases n
  · exact sylowCentralizerCentral_of_small (Or.inl ⟨e⟩)
  · exact sylowCentralizerCentral_of_small (Or.inr (Or.inl ⟨e⟩))
  · exact sylowCentralizerCentral_of_alt_seven ⟨e⟩
  · exact sylowCentralizerCentral_of_alt_eight ⟨e⟩

theorem sylowCentralizerCentral_of_oddList {X : Type} [Group X] [Finite X] (h : OddList X) :
    SylowCentralizerCentral X := by
  obtain ⟨p, -, hp2, h | h | h⟩ := h
  · obtain ⟨f, hf, h⟩ := h
    exact sylowCentralizerCentral_of_psl_two_odd hp2 (by omega) h
  · exact sylowCentralizerCentral_of_psl_three_odd hp2 h
  · exact sylowCentralizerCentral_of_psu_three_odd hp2 h

theorem sylowCentralizerCentral_of_charTwoList
    (hT : TitsTwoCoverTrivial) {X : Type} [Group X]
    [Finite X] (h : SQTKCharTwoLie X) (hA : ¬ IsL34OrG24 X) : SylowCentralizerCentral X := by
  rcases h with (⟨f, h | h | h | h | h | h | h | h⟩ | h) | ⟨n, hn, h⟩
  · exact sylowCentralizerCentral_of_psl_two_even h.1 h.2
  · obtain ⟨hf, h⟩ := h
    rcases Nat.lt_or_ge f 3 with hf3 | hf3
    · rcases (show f = 1 ∨ f = 2 by omega) with rfl | rfl
      · exact sylowCentralizerCentral_of_small (Or.inr (Or.inr (Or.inr h)))
      · exact (hA (Or.inl h)).elim
    · exact sylowCentralizerCentral_of_psl_three_large hf3 h
  · exact sylowCentralizerCentral_of_psu_three_even h.1 h.2
  · exact sylowCentralizerCentral_of_psp_four h.1 h.2
  · obtain ⟨hf, h⟩ := h
    rcases Nat.lt_or_ge f 3 with hf3 | hf3
    · obtain rfl : f = 2 := by omega
      exact (hA (Or.inr h)).elim
    · exact sylowCentralizerCentral_of_g2_large hf3 h
  · exact sylowCentralizerCentral_of_triality h.1 h.2
  · exact sylowCentralizerCentral_of_ree h.1 h.2.1 h.2.2
  · exact sylowCentralizerCentral_of_suzuki h.2.2
  · exact sylowCentralizerCentral_of_tits hT h
  · rcases hn with rfl | rfl
    · exact sylowCentralizerCentral_of_alt_eight
        ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff X).mp
          (Or.inl ⟨by decide, h⟩))
    · exact sylowCentralizerCentral_of_psl_five_two h

theorem sylowCentralizerCentral_of_nonSporadic
    (hT : TitsTwoCoverTrivial) {X : Type} [Group X]
    [Finite X] (h : NonSporadicList X) (hA : ¬ IsL34OrG24 X) : SylowCentralizerCentral X := by
  rcases h with h | h | h
  · exact sylowCentralizerCentral_of_altList h
  · exact sylowCentralizerCentral_of_oddList h
  · exact sylowCentralizerCentral_of_charTwoList hT h hA

theorem innerCover_nonSporadic
    (hT : TitsTwoCoverTrivial) : InnerCover NonSporadicList :=
  innerCover_nonSporadic_of_sylowCentralizerCentral fun _ _ _ h hA =>
    sylowCentralizerCentral_of_nonSporadic hT h hA

end CFSG.QuasithinUnique.Ch1
