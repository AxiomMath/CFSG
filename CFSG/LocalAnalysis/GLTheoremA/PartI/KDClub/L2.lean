module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.Reduce
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldAut3
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

private theorem kdClubL2_cube_mod_nine (n : ℕ) :
    n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8 := by
  have key : ∀ m, m < 9 → m ^ 3 % 9 = 0 ∨ m ^ 3 % 9 = 1 ∨ m ^ 3 % 9 = 8 := by decide
  rw [Nat.pow_mod]
  exact key _ (Nat.mod_lt _ (by norm_num))

theorem kdClubAt_l2 (F : Type) [Field F] [Fintype F] (h0 : Fintype.card F % 3 ≠ 0)
    (h1 : Fintype.card F % 9 ≠ 1) (h8 : Fintype.card F % 9 ≠ 8) :
    KDClubAt (StatedProj (StatedSL 2 F)) := by
  apply kdClubAt_of_solvable
  intro β hβ1 hβ3
  rcases CFSG.HardMathSupport.Solomon.Coordinator.l2Aut3Classification_holds F β hβ3 with
    h | h | ⟨σ, φ, γ, hφ, hβ⟩
  · exact absurd h hβ1
  · exact h
  · exfalso
    obtain ⟨F₀, _, _, hcard, _⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds F β hβ3 hβ1 σ φ γ hφ hβ
    have hc : Fintype.card F = Nat.card F₀ ^ 3 := (Nat.card_eq_fintype_card).symm.trans hcard
    have hmod := kdClubL2_cube_mod_nine (Nat.card F₀)
    rw [← hc] at hmod
    omega

end CFSG.LocalAnalysis.GLTheoremA
