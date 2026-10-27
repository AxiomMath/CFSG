module

public import CFSG.Fischer.Classification.Defs

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E E' : Set X}

theorem IsSymplecticType.image {Y : Type} [Group Y] (f : X →* Y) (h : IsSymplecticType E) :
    IsSymplecticType (f '' E) := by
  rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ _ ⟨z, hz, rfl⟩ hde
  have hde' : d * e ≠ e * d := fun h' => hde (by rw [← map_mul, ← map_mul, h'])
  rcases h d hd e he z hz hde' with h' | h' | h'
  · exact Or.inl (by simpa only [map_mul] using congrArg f h')
  · exact Or.inr (Or.inl (by simpa only [map_mul] using congrArg f h'))
  · exact Or.inr (Or.inr (by simpa only [map_mul] using congrArg f h'))

theorem IsSymplecticType.localImages (h : IsSymplecticType E) (d : X) :
    IsSymplecticType (LocalImages E d) := by
  rintro q1 ⟨f1, hf1, rfl⟩ q2 ⟨f2, hf2, rfl⟩ q3 ⟨f3, hf3, rfl⟩ h12
  have h12' : (f1 : X) * (f2 : X) ≠ (f2 : X) * (f1 : X) := by
    intro hc
    apply h12
    have hsub : f1 * f2 = f2 * f1 := Subtype.ext (by simpa using hc)
    simp only [← QuotientGroup.mk_mul, hsub]
  rcases h (f1 : X) hf1.1 (f2 : X) hf2.1 (f3 : X) hf3.1 h12' with hc | hc | hc
  · left
    have hsub : f3 * f1 = f1 * f3 := Subtype.ext (by simpa using hc)
    simp only [← QuotientGroup.mk_mul, hsub]
  · right; left
    have hsub : f3 * f2 = f2 * f3 := Subtype.ext (by simpa using hc)
    simp only [← QuotientGroup.mk_mul, hsub]
  · right; right
    have hsub : f3 * (f1 * f2 * f1) = f1 * f2 * f1 * f3 :=
      Subtype.ext (by simpa [mul_assoc] using hc)
    simp only [← QuotientGroup.mk_mul, hsub]

end CFSG.Fischer.Classification
