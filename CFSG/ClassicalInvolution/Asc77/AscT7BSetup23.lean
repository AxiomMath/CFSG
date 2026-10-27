module

public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C23_setupSetting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting p f Ω K K' z → ∀ W ∈ WSet Ω, MuIsoS4 Ω W →
      W ⊓ centerIn (Subgroup.normalizer (W : Set G)) ≠ ⊥ → z ∈ W →
        ∃ (u e g : G), Hyp23bData Ω K K' W z u e g

variable {p f}

theorem c23_setup_of (h : C23_setupSetting p f) : C23_setup p f := by
  intro G _ _ _ Ω K K' z hs W hW hS4 hne hzW
  obtain ⟨u, e, g, hd⟩ := h G Ω K K' z hs.setting W hW hS4 hne hzW
  exact ⟨u, e, g, hd.hyp23b hs⟩

end CFSG.ClassicalInvolution.Asc77
