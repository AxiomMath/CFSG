module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTwin
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinT

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_twin_of_shape (hres : TwinSmallInner p) {t : StatedLieTag} {k e : ℕ}
    (hsh : TwinShape t k) : T5BaseAt p f t k e id := by
  have hG2 : t ≠ .G2 := by
    rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact fun h => by cases h
  have hD4 : t ≠ .trialityD4 := by
    rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact fun h => by cases h
  exact t5BaseAt_twin_of_twinInnerAlpha hG2 hD4 fun hp2 hq hadm =>
    twinInnerAlpha_of_shape hres hp2 hq hadm hsh

end CFSG.ClassicalInvolution.Asc77
