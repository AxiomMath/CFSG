module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm7a
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_12_exclude : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      dComp Ω K ≠ dstarComp Ω K → ¬ MuIsoS3 Ω W ∧ ¬ MuIsoS4 Ω W

theorem c21_12_of (h717 : L7_17 p f) (hex : C21_12_exclude p f) : C21_12 p f := by
  intro G _ _ _ Ω K K' z u J t W h
  by_cases hSig : dComp Ω K = dstarComp Ω K
  · exact Or.inl hSig
  · refine Or.inr ?_
    have hP : PartIHyp p f Ω :=
      ⟨h.std.stand.odd, h.std.stand.five, h.std.stand.hyp, h.std.stand.aEmpty⟩
    rcases h717 G Ω hP K h.std.stand.mem with heq | hW
    · exact absurd heq hSig
    · obtain ⟨h3, h4⟩ := hex G Ω K K' z u J t W h hSig
      rcases hW W h.hW with h1 | h1 | h1
      · exact absurd h1 h3
      · exact absurd h1 h4
      · exact h1

end CFSG.ClassicalInvolution.Asc77
