module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.Classification.Basic.WidthOne

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer

theorem s3Input : S3Input := by
  intro G _ D hH hnab
  have hab : ∀ a b : commutator G, a * b = b * a := by
    by_contra h
    push Not at h
    exact hnab h
  obtain ⟨φ, hφ⟩ := Pair.exists_mulEquiv_perm_three hH.pair hH.center hH.simple hab
  exact Or.inl ⟨3, Or.inl rfl, φ, hφ⟩

end CFSG.Fischer.Classification
