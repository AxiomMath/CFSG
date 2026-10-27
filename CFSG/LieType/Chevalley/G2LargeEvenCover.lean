module

public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverSeries

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley ExceptionalCover

theorem G2_large_even_field_central_two_cover_trivial
    {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {f : ℕ} (hf : 3 ≤ f) (hJ : LieModel J .G2 0 2 f) : η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
  · exact absurd hc (by decide)
  · exact untwisted_large_even_central_two_cover_trivial (Or.inl rfl) η hη hC h2 hf hX.2
  · exact absurd hr (by decide)
  · exact absurd hs (by decide)

end CFSG.LieType.Chevalley
