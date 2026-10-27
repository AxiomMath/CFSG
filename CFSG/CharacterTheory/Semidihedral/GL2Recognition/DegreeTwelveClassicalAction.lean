module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.DegreeTwelveThirteenPointAction
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.DegreeThirteenFixedPointPattern

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Semidihedral.Principal.GL2Columns

theorem card_fixedBy_of_fixedPointCount {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]
    {χ : G → ℂ} (hπ : fixedPointCount G Ω = 1 + χ) (g : G) {n : ℕ} (hn : χ g = n - 1) :
    Nat.card (MulAction.fixedBy Ω g) = n := by
  have h := congrFun hπ g
  rw [fixedPointCount, Pi.add_apply, Pi.one_apply, hn] at h
  have : (Nat.card (MulAction.fixedBy Ω g) : ℂ) = n := by rw [h]; ring
  exact_mod_cast this

theorem degree_twelve_character_produces_thirteen_point_classical_action {G : Type} [Group G]
    [Fintype G] (hG : Nat.card G = 5616) (t : G) (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3)))
    (a : G) (haC : a ∈ Subgroup.centralizer ({t} : Set G)) (ha : orderOf a = 3)
    (hCa : Nat.card (Subgroup.centralizer ({a} : Set G)) = 54)
    (P : Subgroup G) (hPa : P ≤ Subgroup.centralizer ({a} : Set G)) (hP : Nat.card P = 27)
    (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (χ : G → ℂ) (hχ : χ ∈ CFSG.BlocksIrr G) (hχ1 : χ 1 = 12)
    (hgap : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ χ → ∃ d : ℕ, 12 < d ∧ ψ 1 = d)
    (hfaith : ∀ g, χ g = 12 → g = 1)
    (h2 : ∀ g, orderOf g = 2 → χ g = 4)
    (h3 : ∀ g, orderOf g = 3 → χ g = 0 ∨ χ g = 3)
    (h489 : ∀ g, orderOf g = 4 ∨ orderOf g = 8 ∨ orderOf g = 9 → χ g = 0)
    (h6 : ∀ g, orderOf g = 6 → χ g = 1) :
    ∃ M : Subgroup G, Nonempty (M ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
      Nat.card (M ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = 12 ∧
      (M ⊔ Subgroup.centralizer ({t} : Set G)).index = 13 ∧
      (∀ g : G, (∀ x : G ⧸ (M ⊔ Subgroup.centralizer ({t} : Set G)), g • x = x) → g = 1) ∧
      MulAction.IsMultiplyPretransitive G (G ⧸ (M ⊔ Subgroup.centralizer ({t} : Set G))) 2 ∧
      fixedPointCount G (G ⧸ (M ⊔ Subgroup.centralizer ({t} : Set G))) = 1 + χ ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 3 1 := by
  obtain ⟨M, hMiso, hMC, hidx, hfaithJ, h2t, hπ⟩ :=
    degree_twelve_character_thirteen_point_action_core hG t ht hC a haC ha hCa P hPa hP hexp χ
      hχ hχ1 hgap hfaith h2 h3 h489 h6
  refine ⟨M, hMiso, hMC, hidx, hfaithJ, h2t, hπ, ?_⟩
  set J := M ⊔ Subgroup.centralizer ({t} : Set G)
  have hΩ : Nat.card (G ⧸ J) = 13 := by rw [← Subgroup.index, hidx]
  refine (degree_thirteen_fixed_point_pattern_classical_recognition hG hΩ hfaithJ h2t
    (fun g hg => card_fixedBy_of_fixedPointCount hπ g (n := 5) (by rw [h2 g hg]; norm_num))
    (fun g hg => ?_)
    (fun g hg => le_of_eq (card_fixedBy_of_fixedPointCount hπ g (n := 1) (by
      rw [h489 g (by rcases hg with hg | hg <;> simp [hg])]; norm_num)))
    (fun g hg => card_fixedBy_of_fixedPointCount hπ g (n := 2)
      (by rw [h6 g hg]; norm_num))).2.2.2.2
  rcases h3 g hg with h0 | h3'
  · exact Or.inl (card_fixedBy_of_fixedPointCount hπ g (n := 1) (by rw [h0]; norm_num))
  · exact Or.inr (card_fixedBy_of_fixedPointCount hπ g (n := 4) (by rw [h3']; norm_num))

end CFSG.Semidihedral.GL2Recognition
