module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.SylowData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.RowsOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.RowsE16
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.RowsL34
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.RowsSz8M12

public section

namespace CFSG.EvenSporadicStandard.HNRecog.GH73

open CFSG.GH74

theorem survivors
    {X : Type} [Group X] [Finite X] (D : A8SylowData X) (hX : GH74Conclusion X) :
    Nonempty (X ≃* alternatingGroup (Fin 8)) ∨ Nonempty (X ≃* alternatingGroup (Fin 9)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧
        CFSG.Blueprint.LieModel X .PSp 2 p f := by
  have hc := D.card_eq
  rcases hX with ⟨p, f, hp, hp2, hf, h | h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
      ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hp2, hf, hq, h⟩ | ⟨p, f, hp, hf, hq, h⟩ |
      ⟨p, f, hp, hf, hq, h⟩ | (h | h | h | h) | ⟨n, hn, hn', h⟩ |
      (h | h | h | h | h | h | h | h)
  · exact absurd h (not_g2_of_e16 D.exists_e16 hp hp2 hf)
  · exact absurd h (not_trialityD4_of_e16 D.exists_e16 hp hp2 hf)
  · exact Or.inr (Or.inr ⟨p, f, hp, hp2, hf, psp4_mod_eight_of_card hc hp hp2 hf h, h⟩)
  · exact absurd h (not_ree_of_card hc)
  · exact absurd h (not_psl4_of_card hc hp hp2 hf hq)
  · exact absurd h (not_psu4_of_card hc hp hp2 hf hq)
  · exact absurd h (not_psl5_of_card hc hp hf hq)
  · exact absurd h (not_psu5_of_card hc hp hf hq)
  · exact absurd h (not_l28_of_card hc)
  · exact absurd h (not_l216_of_card hc)
  · exact absurd h (not_l34_of_center_two D.card_center)
  · exact absurd h (not_sz8_of_noncomm D.exists_noncomm)
  · by_cases h8 : n = 8
    · subst h8
      exact Or.inl h
    · by_cases h9 : n = 9
      · subst h9
        exact Or.inr (Or.inl h)
      · exact absurd h (not_alternating_of_card hc (by omega) hn')
  · exact absurd h (not_M12_of_no_order_eight D.no_order_eight)
  · exact absurd h (not_M22_of_card hc)
  · exact absurd h (not_M23_of_card hc)
  · exact absurd h (not_J1_of_card hc)
  · exact absurd h (not_J2_of_card hc)
  · exact absurd h (not_J3_of_card hc)
  · exact absurd h (not_McL_of_card hc)
  · exact absurd h (not_Ly_of_card hc)

end CFSG.EvenSporadicStandard.HNRecog.GH73
