module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.Order5616DegreeGap

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers

theorem seven_character_sylow_support_classical_recognition {G : Type} [Group G] [Fintype G]
    (hG : Nat.card G = 5616) (S : Sylow 2 G)
    (χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G) (hnd : [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup)
    (h1 : (χ₁ : G → ℂ) ≠ 1) (h2 : (χ₂ : G → ℂ) ≠ 1) (h3 : (χ₃ : G → ℂ) ≠ 1)
    (h4 : (χ₄ : G → ℂ) ≠ 1) (h5 : (χ₅ : G → ℂ) ≠ 1) (h6 : (χ₆ : G → ℂ) ≠ 1)
    (h7 : (χ₇ : G → ℂ) ≠ 1)
    (hdeg : ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1,
      (χ₅ : G → ℂ) 1, (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] = ![26, 27, 26, 26, 39, 12, 13])
    (hvan : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) →
      ψ ≠ (χ₃ : G → ℂ) → ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) →
      ψ ≠ (χ₇ : G → ℂ) → ∀ s ∈ (S : Subgroup G), s ≠ 1 → ψ s = 0) :
    commutator G = ⊤ ∧ Nat.card (ConjClasses G) = 12 ∧
    (irreducibles_finite G).toFinset.val.map (fun ψ => ψ 1) =
      ({1, 12, 13, 16, 16, 16, 16, 26, 26, 26, 27, 39} : Multiset ℂ) ∧
    (∀ ψ ∈ CFSG.BlocksIrr G, ψ 1 = 12 → ψ = χ₆) ∧
    (∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ (χ₆ : G → ℂ) → ∃ d : ℕ, 12 < d ∧ ψ 1 = d) ∧
    ((∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) → ∀ t : G, orderOf t = 2 →
      Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3)) →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 3 1 ∧
      ∃ J : Subgroup G, J.index = 13 ∧ (∀ g : G, (∀ x : G ⧸ J, g • x = x) → g = 1) ∧
        MulAction.IsMultiplyPretransitive G (G ⧸ J) 2 ∧
        fixedPointCount G (G ⧸ J) = 1 + (χ₆ : G → ℂ)) := by
  obtain ⟨hperf, h12, hmult, huniq, hgap⟩ :=
    seven_character_sylow_support_degree_profile hG S χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ hnd h1 h2 h3 h4 h5
      h6 h7 hdeg hvan
  refine ⟨hperf, h12, hmult, huniq, hgap, fun hinv t ht hC => ?_⟩
  have h61 : (χ₆ : G → ℂ) 1 = 12 := by simpa using congrFun hdeg 5
  obtain ⟨M, -, -, hidx, hfaith, h2t, hπ, hmodel⟩ :=
    order5616_degree_gap_classical_recognition hG hperf h12 hinv ht hC χ₆ χ₆.2 h61 hgap
  exact ⟨hmodel, M ⊔ Subgroup.centralizer ({t} : Set G), hidx, hfaith, h2t, hπ⟩

end CFSG.Semidihedral.GL2Recognition
