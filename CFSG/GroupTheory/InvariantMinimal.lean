module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.UniquenessCase.UCK

variable {p : ℕ} {G V : Type} [Group G]
  [AddCommGroup V] [Module (ZMod p) V]

theorem fixV_le_comap_fixV_of_commute (ρ : Representation (ZMod p) G V) {A : Subgroup G} {b : G}
    (hb : ∀ a ∈ A, b * a = a * b) : fixV ρ A ≤ (fixV ρ A).comap (ρ b) := by
  intro v hv
  rw [Submodule.mem_comap]
  intro a ha
  have hba : ρ a * ρ b = ρ b * ρ a := by
    rw [← map_mul, ← map_mul, hb a ha]
  change ρ a (ρ b v) = ρ b v
  rw [← Module.End.mul_apply, hba, Module.End.mul_apply, hv a ha]

theorem exists_minimal_invariant_submodule [Finite G] [Finite V]
    (ρ : Representation (ZMod p) G V) {U : Submodule (ZMod p) V} (hU : U ≠ ⊥)
    (hInv : ∀ g : G, ∀ v ∈ U, ρ g v ∈ U) :
    ∃ W : Submodule (ZMod p) V, W ≤ U ∧ W ≠ ⊥ ∧ (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) ∧
      ∀ W' : Submodule (ZMod p) V, W' ≤ W → (∀ g : G, ∀ v ∈ W', ρ g v ∈ W') →
        W' = ⊥ ∨ W' = W := by
  classical
  let P : ℕ → Prop := fun n => ∃ W : Submodule (ZMod p) V,
    W ≤ U ∧ W ≠ ⊥ ∧ (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) ∧ Nat.card W = n
  have hP : ∃ n, P n := ⟨Nat.card U, U, le_rfl, hU, hInv, rfl⟩
  obtain ⟨W, hWU, hWne, hWinv, hWcard⟩ := Nat.find_spec hP
  refine ⟨W, hWU, hWne, hWinv, fun W' hW'W hInv' => ?_⟩
  by_cases hbot : W' = ⊥
  · exact Or.inl hbot
  · right
    have hle : Nat.card W ≤ Nat.card W' := by
      by_contra hlt
      push Not at hlt
      have hfind := Nat.find_min' hP ⟨W', hW'W.trans hWU, hbot, hInv', rfl⟩
      omega
    haveI : Fintype ↥W' := Fintype.ofFinite ↥W'
    haveI : Fintype ↥W := Fintype.ofFinite ↥W
    have hEqSet : (W' : Set V) = (W : Set V) :=
      Set.eq_of_subset_of_card_le hW'W (by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hle
        exact hle)
    exact SetLike.ext fun x => by
      show x ∈ (W' : Set V) ↔ x ∈ (W : Set V)
      rw [hEqSet]

end CFSG.GroupTheory

end
