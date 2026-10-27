module

public import CFSG.ClassicalInvolution.Asc77.AscC25X1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected

namespace C25X

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}


theorem twinSection_cases0 (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hBelow : CITBelowU p f n) (hlt : Nat.card X < n) (hS : GenSection p f Φ)
    {A A' : Subgroup X} {z a₀ b₀ : X} (T : TwinSect0 Φ A A' z a₀ b₀) :
    (∀ L ∈ Φ, L = A ∨ L = A') ∨
      ∃ (D : OmegaLie p f Φ) (_ : D.card = 1) (i : Fin D.card),
        (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
          (D.tag i = .PSU ∧ D.rank i = 4) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
          (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4) := by
  classical
  have hΦ : HypOmegaMod p f Φ := hS.hyp
  by_cases hconn : DConnected Φ
  · left
    have hpath : ∀ N, Relation.ReflTransGen (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) A N →
        N = A ∨ N = A' := by
      intro N hN
      induction hN with
      | refl => exact Or.inl rfl
      | tail hpre hstep ih =>
        rename_i M N'
        obtain ⟨hN'Φ, hadj⟩ := hstep
        have hMΦ : M ∈ Φ := by
          rcases ih with rfl | rfl
          · exact T.hA
          · exact T.hA'
        rcases ih with rfl | rfl
        · refine Or.inr (T.nbA N' hN'Φ ?_)
          rcases hadj with h | h
          · exact h
          · exact T3.omegaNbr_symm (l6_2 p f) hp hq hΦ hN'Φ hMΦ h
        · refine Or.inl (T.nbA' N' hN'Φ ?_)
          rcases hadj with h | h
          · exact h
          · exact T3.omegaNbr_symm (l6_2 p f) hp hq hΦ hN'Φ hMΦ h
    intro L hL
    exact hpath L (hconn _ T.hA L hL)
  · right
    have hNE : ¬ DEdgeless Φ := by
      intro h
      rcases mem_kPerp_of_twin hΦ T.hA T.hA' T.hzA T.hzA' with h' | h'
      · exact T.ne h'
      · exact h _ T.hA' _ T.hA (Or.inl h')
    obtain ⟨d, ε, hd5, hd8, t', n', hortag, D, hcard, i, htag, hrank⟩ :=
      thm8SectBelow'_of_citBelow G2D4Models.ih8G2D4_unconditional hBelow hp hq X hlt Φ hS
        ⟨_, T.hA⟩ hNE hconn
    refine ⟨D, hcard, i, ?_⟩
    rw [htag, hrank]
    rcases hortag with ⟨-, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨hd7, hodd, ht, hn⟩ |
      ⟨hd8', hev, -, ht, hn⟩ | ⟨hd8', hev, -, ht, hn⟩
    · exact Or.inl ⟨ht, hn⟩
    · exact Or.inr (Or.inl ⟨ht, hn⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨ht, hn⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, by omega⟩))))

end C25X

end CFSG.ClassicalInvolution.Asc77
