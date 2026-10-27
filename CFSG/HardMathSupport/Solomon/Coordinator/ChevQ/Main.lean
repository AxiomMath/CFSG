module

public import CFSG.HardMathSupport.Dickson.I271.Support.Action
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Indices
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Numerics
public import CFSG.LieType.Seitz.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2

theorem l28_or_bal207_or_l34_of_d2Exc {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : IsD2SeitzException p d) :
    (p = 3 ∧ IsL2EightIndex d) ∨ Bal207Index p d ∨ (p = 3 ∧ ∃ q, d = .A 2 q ∧ IsTwoPow q 2) := by
  rcases h with ⟨hp, h1 | h2 | h3 | h4 | h5⟩ | ⟨hp, h6 | h7⟩
  · obtain ⟨q, hq2, hq3, rfl⟩ := h1
    exact Or.inl ⟨hp, by dsimp only [IsL2EightIndex]; exact ⟨rfl, hq2, hq3⟩⟩
  · obtain ⟨q, hq2, hq3, rfl⟩ := h2
    exact Or.inr (Or.inr ⟨hp, q, rfl, hq2, hq3⟩)
  · obtain ⟨q, hq2, hq3, rfl⟩ := h3
    exact Or.inr (Or.inl (by
      dsimp only [Bal207Index]; exact ⟨hp, Or.inl ⟨Or.inl ⟨hq2, hq3⟩, by decide⟩⟩))
  · obtain ⟨q, hq2, hq3, rfl | rfl⟩ := h4
    · exact Or.inr (Or.inl (by
        dsimp only [Bal207Index]; exact ⟨hp, Or.inl ⟨⟨hq2, hq3⟩, by norm_num⟩⟩))
    · exact Or.inr (Or.inl (by
        dsimp only [Bal207Index]; exact ⟨hp, Or.inl ⟨⟨hq2, hq3⟩, by norm_num⟩⟩))
  · subst h5
    exact Or.inr (Or.inl (by dsimp only [Bal207Index]; exact Or.inl hp))
  · subst h6
    exact Or.inr (Or.inl (by dsimp only [Bal207Index]; exact Or.inr hp))
  · subst h7
    exact Or.inr (Or.inl (by dsimp only [Bal207Index]; exact ⟨hp, rfl⟩))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
