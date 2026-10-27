module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsCases
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsGraph
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsForms

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

variable {n : ℕ} {F : Type} [Field F] [Finite F] {G : Type*} [Group G] {K : Subgroup G}

theorem exists_twoSubgroup_of_graph (hF : Nat.card F = 4) {r : ℕ} (hr : r = 2 ∨ r = 3)
    (hn : n = 2 * r) (ψ : SL(n, F) →* K) (hker : ψ.ker ≤ center SL(n, F)) {t : G}
    {H C : GL (Fin n) F} (hC : (C : Matrix (Fin n) (Fin n) F) = 1 ∨
      ∃ r', n = 2 * r' ∧ (C : Matrix (Fin n) (Fin n) F) = blockSwapJ n r')
    (hHC : ∀ x, t * (ψ x : G) * t⁻¹ =
      ψ ((stdSL n F H 1 0 * stdSL n F C 1 1 * (stdSL n F H 1 0)⁻¹) x)) :
    ∃ Q ≤ K ⊓ centralizer ({t} : Set G), IsPGroup 2 Q ∧ Nat.card F ^ (r * r) ≤ Nat.card Q := by
  have := charP_two_of_card_four hF
  obtain ⟨Q₀, hfix, h2, hcard⟩ := exists_twoSubgroup_fixed_graph hr hn C hC
  have hQ₁ : ∀ x ∈ Q₀.map (stdSL n F H 1 0).toMonoidHom,
      (stdSL n F H 1 0 * stdSL n F C 1 1 * (stdSL n F H 1 0)⁻¹) x = x := by
    intro x hx
    rw [← mem_fixSub, fixSub_conj]
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hfix y hy, rfl⟩
  obtain ⟨Q', hQ', hQ'2, hQ'card⟩ := exists_twoSubgroup_of_fixed hF (by omega) ψ hker hHC hQ₁
    (h2.map _)
  refine ⟨Q', hQ', hQ'2, ?_⟩
  rw [hQ'card, card_map_of_injective (MulEquiv.injective _)]
  exact hcard

theorem exists_twoSubgroup_of_linear (hF : Nat.card F = 4) {r : ℕ} (hr : r = 2 ∨ r = 3)
    (hn : n = 2 * r) (ψ : SL(n, F) →* K) (hker : ψ.ker ≤ center SL(n, F)) {t : G}
    (ht : t * t = 1) {A : GL (Fin n) F} {ε : ℕ} (hε : ε ≤ 1)
    (hA : ∀ x, t * (ψ x : G) * t⁻¹ = ψ (stdSL n F A 1 ε x)) :
    ∃ Q ≤ K ⊓ centralizer ({t} : Set G), IsPGroup 2 Q ∧ Nat.card F ^ (r * r) ≤ Nat.card Q := by
  have hn3 : 3 ≤ n := by omega
  rcases cases_of_lift hn3 hF ψ hker ht hε hA with ⟨-, ⟨g, hg, hgt⟩ | ⟨H, C, hC, hHC⟩⟩ |
      ⟨hσ, -⟩
  · exact exists_twoSubgroup_of_inner hF hn (by omega) ψ hker hg hgt
  · exact exists_twoSubgroup_of_graph hF hr hn ψ hker hC hHC
  · exact absurd rfl hσ

theorem field_ne_one_of_small (hF : Nat.card F = 4) {r : ℕ} (hr : r = 2 ∨ r = 3)
    (hn : n = 2 * r) (ψ : SL(n, F) →* K) (hker : ψ.ker ≤ center SL(n, F)) {t : G}
    (ht : t * t = 1) {A : GL (Fin n) F} {σ : F ≃+* F} {ε : ℕ} (hε : ε ≤ 1)
    (hA : ∀ x, t * (ψ x : G) * t⁻¹ = ψ (stdSL n F A σ ε x))
    (hsmall : ∀ Q ≤ K ⊓ centralizer ({t} : Set G), IsPGroup 2 Q →
      Nat.card Q < Nat.card F ^ (r * r)) : σ ≠ 1 := by
  rintro rfl
  obtain ⟨Q, hQ, hQ2, hQcard⟩ := exists_twoSubgroup_of_linear hF hr hn ψ hker ht hε hA
  exact absurd (hsmall Q hQ hQ2) (not_lt.mpr hQcard)

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
