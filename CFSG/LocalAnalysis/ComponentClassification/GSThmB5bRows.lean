module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma517

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

@[expose] def Row514 : Prop :=
  (Blueprint.LieModel (OddBar h.J) .PSL 2 5 1 ∨ Blueprint.LieModel (OddBar h.J) .PSL 2 7 1) ∧
    conjugate h.K h.a = h.K ∧ center (OddBar h.K) ≠ ⊥ ∧
    Blueprint.LieModel (ZStarBar h.K) .PSL 3 2 2

@[expose] def Row515 : Prop :=
  Nonempty (OddBar h.J ≃* alternatingGroup (Fin 6)) ∧ conjugate h.K h.a = h.K ∧
    Nonempty (OddBar h.K ≃* alternatingGroup (Fin 10))

@[expose] def Row516 : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
    conjugate h.K h.a = h.K ∧ (Blueprint.LieModel (ZStarBar h.K) .PSL 4 p f ∨
      Blueprint.LieModel (ZStarBar h.K) .PSU 4 p f ∨
      ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h.K) .POmegaMinus 4 p e)

theorem table517_of_rows (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (h13 : h.Elim513) (h14 : ¬ h.Row514)
    (h15 : ¬ h.Row515) (h16 : ¬ h.Row516) : h.Table517 := by
  rcases h.table hB1 hCF23 with ⟨n, hn, hJ, (⟨hKa, hK | hK⟩ | ⟨hKa, hZ, hK⟩)⟩ |
      h2 | h3 | h4 | h5 | h6 | h7
  ·
    rcases hn with rfl | rfl | rfl
    · exact absurd (Or.inl hK) (h13 hKa)
    · exact Or.inr (Or.inr (Or.inl ⟨hJ, hKa, hK⟩))
    · exact absurd (Or.inr (Or.inl hK)) (h13 hKa)
  ·
    rcases hn with rfl | rfl | rfl
    · exact absurd (Or.inr (Or.inl hK)) (h13 hKa)
    · exact absurd ⟨hJ, hKa, hK⟩ h15
    · exact absurd (Or.inr (Or.inr hK)) (h13 hKa)
  ·
    exact Or.inl ⟨hKa, hZ, Or.inl ⟨n, hn, hJ, hK⟩⟩
  ·
    exact absurd h2 h14
  ·
    exact absurd h3 (h.not_suz hB6 hCF24)
  ·
    exact absurd h4 h16
  ·
    exact Or.inr (Or.inl h5)
  ·
    obtain ⟨p, f, hp, hp2, hf, h5f, hJ, hKa, hZ, hK⟩ := h6
    exact Or.inl ⟨hKa, hZ, Or.inr ⟨p, f, hp, hp2, hf, h5f, hJ, hK⟩⟩
  ·
    exact Or.inr (Or.inr (Or.inr h7))

end Hyp52

end CFSG.ComponentClassification.GSThmB
