module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualG2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualRee

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.Blueprint

theorem even_rank_two_exceptional_proper_Sylow_overgroup_residual
    {X : Type} [Group X] [Finite X] {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hX : (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (∃ f : ℕ, 3 ≤ f ∧ Odd f ∧ ReeTitsModel X .twistedF4 2 f)) :
    ResidualOvergroups X U := by
  rcases hX with ⟨_, -, hX⟩ | ⟨_, -, hX⟩ | ⟨_, -, -, hX⟩
  · obtain ⟨_, _, _, _, _, _, _, hP, _⟩ := even_rank_two_residual_G2 hX hU
    exact ⟨_, hP⟩
  · obtain ⟨_, _, _, _, _, _, _, _, hP, _⟩ := even_rank_two_residual_triality hX hU
    exact ⟨_, hP⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hP, _⟩ := even_rank_two_residual_largeRee hX hU
    exact ⟨_, hP⟩

end CFSG.QuasithinUnique.Setup.X6
