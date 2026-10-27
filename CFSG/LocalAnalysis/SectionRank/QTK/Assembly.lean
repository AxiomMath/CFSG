module

public import CFSG.LocalAnalysis.SectionRank.QTK.Interface

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem qtkSimpleList_of_exceptionalList {S : Type} [Group S] (h : QTExceptionalList S) :
    QTKSimpleList S := by
  rcases h with ⟨p, hp, hp2, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hodd, hf, hm⟩ | hm |
      ⟨f, hodd, hf, hm⟩
  · exact Or.inr (Or.inl ⟨p, hp, hp2, Or.inr (Or.inr (Or.inr (Or.inl hm)))⟩)
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hf, hm⟩)))))⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨hf, hm⟩))))))⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨hodd, hf, hm⟩)))))))⟩)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hm))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr ⟨hodd, hf, hm⟩)))))))⟩)))

theorem qtkSimpleList_of_mem_qtkSporadicNames {S : Type} [Group S] {s : TauCeti.SporadicName}
    (hs : s ∈ qtkSporadicNames) (e : S ≃* NativeSporadic.Carrier s) : QTKSimpleList S := by
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨s, ?_, ⟨e⟩⟩)))
  simp only [qtkSporadicNames, Finset.mem_insert, Finset.mem_singleton] at hs
  exact hs

theorem qtkSimpleList_of_restrictions (hAlt : QTAltRestriction)
    (hOdd : QTOddClassicalRestriction) (hEven : QTEvenClassicalRestriction)
    (hExc : QTExceptionalRestriction) (hSpor : QTSporadicRestriction) (S : Type) [Group S]
    [Finite S] (hnonab : ∃ a b : S, a * b ≠ b * a) (hQT : CFSG.Open.evenRank S ≤ 2)
    (hcat : Catalog S) : QTKSimpleList S := by
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hex | ⟨s, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact Or.inl ⟨n, hn, hAlt S n hQT ⟨e⟩, ⟨e⟩⟩
  · by_cases hp2 : p = 2
    · subst hp2
      exact hEven S t n f hQT hm
    · exact hOdd S t n p f hp2 hQT hm
  · exact qtkSimpleList_of_exceptionalList (hExc S hQT hex)
  · exact qtkSimpleList_of_mem_qtkSporadicNames (hSpor S hnonab hQT s ⟨e⟩) e

end CFSG.SectionRank.QTK
