module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

namespace S11

variable {G : Type} [Group G] [Finite G]

theorem split_of_split16 {p : ℕ} {lab : GLALabel} (h : GLASplit16 p lab) (h1 : lab.tag ≠ .triD4) (h2 : lab.tag ≠ .twB2)
    (h3 : lab.tag ≠ .twF4) : GLASplit p lab := by
  rcases h with h | ⟨h, -, -, hd⟩ | ⟨h, hd⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h, h1, hd⟩)
  · rcases h with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inl h, hd⟩))
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
  · exact Or.inr (Or.inr (Or.inr h))

theorem splitInnerDiag_of_16 {p : ℕ} {B L : Subgroup G}
    (hrk : ∀ lab : GLALabel, LabelOf L lab → lab.tag ≠ .triD4 ∧ lab.tag ≠ .twB2 ∧ lab.tag ≠ .twF4)
    (h : SplitInnerDiagMarking16 p B L) : SplitInnerDiagMarking p B L := by
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  have hLab : LabelOf L lab :=
    ⟨hL, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨h1, h2, h3⟩ := hrk lab hLab
  refine ⟨hL, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hsp, hnorm, hind⟩
  exact ⟨hs, hna, θ, split_of_split16 hsp h1 h2 h3, hnorm, hind⟩

end S11

end CFSG.LocalAnalysis.GLTheoremA
