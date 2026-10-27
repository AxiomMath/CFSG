module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Choice
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt69

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Prop69

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_minBad {z : G} {M Q : Subgroup G} {p : ℕ} (hQ : QP z p (Op p M) Q)
    (h : ∃ X : Subgroup G, X ≤ Q ∧ X ≠ ⊥ ∧ z ∈ normalizer (X : Set G) ∧ ¬ NF z M X) :
    ∃ X : Subgroup G, MinBad z M p Q X := by
  classical
  let T : Subgroup G → Prop := fun X => X ≤ Q ∧ X ≠ ⊥ ∧ z ∈ normalizer (X : Set G) ∧ ¬ NF z M X
  have hex : ∃ n, ∃ X, T X ∧ Nat.card ↥X = n := by
    obtain ⟨X, hX⟩ := h
    exact ⟨_, X, hX, rfl⟩
  obtain ⟨X₀, hX₀, hX₀m⟩ := Nat.find_spec hex
  have hmin : ∀ Y, T Y → Nat.find hex ≤ Nat.card ↥Y := fun Y hY => Nat.find_min' hex ⟨Y, hY, rfl⟩
  by_cases hpref : ∃ Y, T Y ∧ Nat.card ↥Y = Nat.find hex ∧ ¬ Y ≤ Cen z
  · obtain ⟨Y, hY, hYm, hYc⟩ := hpref
    exact ⟨Y, hQ, hY.1, hY.2.1, hY.2.2.1, hY.2.2.2,
      fun W hWQ hW0 hWz hWN => hYm ▸ hmin W ⟨hWQ, hW0, hWz, hWN⟩, fun _ => hYc⟩
  · exact ⟨X₀, hQ, hX₀.1, hX₀.2.1, hX₀.2.2.1, hX₀.2.2.2,
      fun W hWQ hW0 hWz hWN => hX₀m ▸ hmin W ⟨hWQ, hW0, hWz, hWN⟩,
      fun ⟨Y, hYQ, hY0, hYz, hYN, hYc, hYnc⟩ =>
        absurd ⟨Y, ⟨hYQ, hY0, hYz, hYN⟩, hX₀m ▸ hYc, hYnc⟩ hpref⟩

theorem prop6_9_of (h68 : Prop6_8) (h612 : Lemma6_12) (h614 : Lemma6_14) (h615 : Lemma6_15)
    (htail : Tail6_9) : Prop6_9 := by
  intro G _ _ z k S M p hC Q hQ
  by_cases ha : ∀ X : Subgroup G, X ≤ Q → X ≠ ⊥ → z ∈ normalizer (X : Set G) → NF z M X
  · exact Or.inl ha
  right
  push Not at ha
  obtain ⟨X, hXQ, hX0, hXz, hXN⟩ := ha
  obtain ⟨X', hmin⟩ := exists_minBad hQ ⟨X, hXQ, hX0, hXz, hXN⟩
  have hE : IsCyclic ↥(Ep p M) ∧ Ep p M ≤ Cen z := by
    rcases h68 G z k S M p hC with h | h
    · exact absurd (h X' (hmin.X_le.trans (hQ.1.trans (Op_le_Fm p hC.prime M))) hmin.X_ne hmin.X_inv)
        hmin.X_not
    · exact h
  have h2 := h612 G z k S M p hC Q X' hmin
  obtain ⟨hcard, h5⟩ := h614 G z k S M p hC Q X' hmin
  have h3 := h615 G z k S M p hC Q X' hmin
  exact ⟨hE.1, hE.2, ⟨h2, hcard⟩, h3,
    htail G z k S M p hC Q hQ hE.1 hE.2 h2 hcard h3.1 h3.2.1 h3.2.2, h5⟩

theorem prop6_9_clean (h69 : Prop6_9) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    (hC : Ctx6 G z k S M p) {Q : Subgroup G} (hQ : QP z p (Op p M) Q) :
    ∀ X : Subgroup G, X ≤ Q → X ≠ ⊥ → z ∈ normalizer (X : Set G) → NF z M X := by
  rcases h69 G z k S M p hC Q hQ with h | ⟨-, -, -, -, h4, -⟩
  · exact h
  · exfalso
    have := CFSG.GH74.GLS.Stage2.Final.Thm4.three_le_pRank_S hC.ctx
    omega

end Prop69

end CFSG.GH74.GLS.Stage2.Bender.Thm1
