module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem fusion3_of_fusion2 (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) :
    Fusion3Facts a z := by
  have hF1a : Fusion1Facts a z := hF1.self
  have hF2a : Fusion2Facts a z := hF2.self
  have hne : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have clash : ∀ {x : G}, IsConj a x → IsConj z x → False :=
    fun hax hzx => hne (hax.trans hzx.symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases fusion3_class hI h hF1a hF2a (Or.inl ht.1) (Or.inl ht.2) with
      ⟨hzt, -⟩ | ⟨-, hzat, -⟩ | ⟨-, -, hsh⟩ | ⟨hzt, -⟩
    · exact (clash ht.1 hzt).elim
    · exact (clash ht.2 hzat).elim
    · exact hsh
    · exact (clash ht.1 hzt).elim
  · intro w hw
    rcases fusion3_class hI h hF1a hF2a (Or.inr hw.1) (Or.inl hw.2) with
      ⟨-, -, hsh, haQ⟩ | ⟨haw, -⟩ | ⟨haw, -⟩ | ⟨-, hzaw, -⟩
    · exact ⟨hsh, haQ⟩
    · exact (clash haw hw.1).elim
    · exact (clash haw hw.1).elim
    · exact (clash hw.2 hzaw).elim
  · intro t ht
    rcases fusion3_class hI h hF1a hF2a (Or.inl ht.1) (Or.inr ht.2) with
      ⟨hzt, -⟩ | ⟨-, -, hsh⟩ | ⟨-, hat, -⟩ | ⟨hzt, -⟩
    · exact (clash ht.1 hzt).elim
    · exact hsh
    · exact (clash hat ht.2).elim
    · exact (clash ht.1 hzt).elim
  · intro w hw
    rcases fusion3_class hI h hF1a hF2a (Or.inr hw.1) (Or.inr hw.2) with
      ⟨-, haaw, -⟩ | ⟨haw, -⟩ | ⟨haw, -⟩ | ⟨-, -, hsh, hQ⟩
    · exact (clash haaw hw.2).elim
    · exact (clash haw hw.1).elim
    · exact (clash haw hw.1).elim
    · exact ⟨hsh, hQ⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
