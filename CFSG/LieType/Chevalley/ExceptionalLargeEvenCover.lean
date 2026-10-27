module

public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverSeries

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley ExceptionalCover
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem ordinary_exceptional_large_even_field_central_two_cover_trivial
    {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {f : ℕ} (hf : 3 ≤ f) {t : StatedLieTag} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hJ : LieModel J t 0 2 f) : η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
  · rcases ht with rfl | rfl | rfl | rfl <;> exact absurd hc (by decide)
  · rcases ht with rfl | rfl | rfl | rfl
    · exact untwisted_large_even_central_two_cover_trivial (Or.inr (Or.inl rfl)) η hη hC h2 hf
        hX.2
    · exact untwisted_large_even_central_two_cover_trivial (Or.inr (Or.inr (Or.inl rfl))) η hη
        hC h2 hf hX.2
    · exact untwisted_large_even_central_two_cover_trivial
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) η hη hC h2 hf hX.2
    · exact untwisted_large_even_central_two_cover_trivial
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) η hη hC h2 hf hX.2
  · rcases ht with rfl | rfl | rfl | rfl <;> exact absurd hr (by decide)
  · rcases ht with rfl | rfl | rfl | rfl <;> exact absurd hs (by decide)

end CFSG.LieType.Chevalley
