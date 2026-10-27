module

public import CFSG.ClassicalInvolution.Asc77.AscC5O10
public import CFSG.ClassicalInvolution.Asc77.AscC5O11
public import CFSG.ClassicalInvolution.Asc77.AscC25Y6

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

variable {p f : ℕ} [Fact p.Prime]

theorem c25_11Om5_of (hM : ModelFacts p f) (hM8 : M8GFacts p f) : C25Y.C25_11Ω5 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hA0 hbad hbad' h5' h5
  have C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a :=
    ⟨hyp, haA, ha2, ha1, haz, hconj, hA0, hbad, hbad', h5, h5'⟩
  rcases C.exists_swaps hM with ⟨τ, σ, D, hτS⟩ | ⟨τ, σ, D, hτS⟩
  · exact D.false_of_comm hM (D.comm_mem_hBig hM hM8 hτS)
  · exact D.false_of_comm hM (D.comm_mem_hBig hM hM8 hτS)

end CFSG.ClassicalInvolution.Asc77.C5O
