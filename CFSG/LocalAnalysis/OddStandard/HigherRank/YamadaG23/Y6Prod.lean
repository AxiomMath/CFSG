module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped Pointwise

private theorem card_eq_card_image_mul' {α β : Type*} [Finite α] (f : α → β) (S : Set β)
    (hS : ∀ b, b ∈ S ↔ ∃ a, f a = b) (m : ℕ) (hm : ∀ b ∈ S, Nat.card {a // f a = b} = m) :
    Nat.card α = Nat.card S * m := by
  classical
  have hfin : Finite S := by
    have : S = Set.range f := Set.ext fun b => (hS b).trans Iff.rfl
    rw [this]; exact (Set.finite_range f).to_subtype
  have : Fintype S := Fintype.ofFinite S
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
  have e : (Σ b : β, {a // f a = b}) ≃ Σ b : S, {a // f a = b} :=
    { toFun := fun p => ⟨⟨p.1, (hS _).2 ⟨p.2.1, p.2.2⟩⟩, p.2⟩
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin' : ∀ b : S, Finite {a // f a = b} := fun _ => inferInstance
  rw [Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl (fun (b : S) _ => hm b.1 b.2),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem y6_card_prodSet {G : Type} [Group G] [Finite G] {A V : Subgroup G} {S : Set G}
    (hSA : S ⊆ A) (hSZ : ∀ s ∈ S, ∀ w ∈ A ⊓ V, s * w ∈ S) :
    Nat.card ↥S * Nat.card ↥V =
      Nat.card ↥{x : G | ∃ s ∈ S, ∃ v ∈ V, x = s * v} * Nat.card ↥(A ⊓ V) := by
  classical
  let F : ↥S × ↥V → G := fun p => p.1.1 * p.2.1
  have hrange : Set.range F = {x : G | ∃ s ∈ S, ∃ v ∈ V, x = s * v} := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩
    · rintro ⟨s, hs, v, hv, rfl⟩
      exact ⟨(⟨s, hs⟩, ⟨v, hv⟩), rfl⟩
  have hfib : ∀ b ∈ Set.range F, Nat.card {p : ↥S × ↥V // F p = b} = Nat.card ↥(A ⊓ V) := by
    rintro b ⟨p₀, rfl⟩
    have hmul : ∀ {a b c d : G}, a * b = c * d → a⁻¹ * c = b * d⁻¹ := by
      intro a b c d h
      have h1 : a⁻¹ * c * d = b := by
        calc a⁻¹ * c * d = a⁻¹ * (c * d) := by group
          _ = a⁻¹ * (a * b) := by rw [← h]
          _ = b := by group
      calc a⁻¹ * c = a⁻¹ * c * d * d⁻¹ := by group
        _ = b * d⁻¹ := by rw [h1]
    refine (Nat.card_congr ?_).symm
    refine
      { toFun := fun w =>
          ⟨(⟨p₀.1.1 * (w : G)⁻¹,
              hSZ p₀.1.1 p₀.1.2 w⁻¹ ((A ⊓ V).inv_mem w.2)⟩,
            ⟨(w : G) * p₀.2.1, V.mul_mem w.2.2 p₀.2.2⟩), ?_⟩
        invFun := fun p =>
          ⟨p.1.1.1⁻¹ * p₀.1.1,
            ⟨A.mul_mem (A.inv_mem (hSA p.1.1.2)) (hSA p₀.1.2),
              by
                rw [hmul p.2]
                exact V.mul_mem p.1.2.2 (V.inv_mem p₀.2.2)⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · show (p₀.1.1 * (w : G)⁻¹) * ((w : G) * p₀.2.1) = p₀.1.1 * p₀.2.1
      group
    · intro w
      exact Subtype.ext (by group)
    · intro p
      refine Subtype.ext ?_
      refine Prod.ext ?_ ?_
      · exact Subtype.ext (by group)
      · refine Subtype.ext ?_
        calc (p.1.1.1⁻¹ * p₀.1.1) * p₀.2.1
            = (p.1.2.1 * p₀.2.1⁻¹) * p₀.2.1 := by rw [hmul p.2]
          _ = p.1.2.1 := by group
  have hcard := card_eq_card_image_mul' F (Set.range F) (fun _ => Iff.rfl)
    (Nat.card ↥(A ⊓ V)) hfib
  rw [Nat.card_prod ↥S ↥V] at hcard
  rw [hrange] at hcard
  exact hcard

end CFSG.OddStandard.HigherRank.YamadaG23