module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.GroupAction.Defs

public section

open MulAction

namespace CFSG.GroupAction

theorem card_fix_mul_card_stabilizer {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [IsPretransitive G X] (x₀ : X) (t : G) :
    Nat.card {x : X // t • x = x} * Nat.card (stabilizer G x₀) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) *
        Nat.card {h : G // h ∈ stabilizer G x₀ ∧ IsConj t h} := by
  classical
  let P := {g : G // g⁻¹ * t * g ∈ stabilizer G x₀}
  have hsec : ∀ x : X, ∃ g : G, g • x₀ = x := fun x => exists_smul_eq G x₀ x
  choose s hs using hsec
  have memP : ∀ g : G, g⁻¹ * t * g ∈ stabilizer G x₀ ↔ t • (g • x₀) = g • x₀ := by
    intro g
    rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]
  have e1 : P ≃ {x : X // t • x = x} × stabilizer G x₀ :=
    { toFun := fun g => (⟨(g : G) • x₀, (memP g).1 g.2⟩,
        ⟨(s ((g : G) • x₀))⁻¹ * g, by
          rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hs]⟩)
      invFun := fun p => ⟨s p.1.1 * p.2, by
          have hx : (s p.1.1 * p.2) • x₀ = p.1.1 := by
            rw [mul_smul, mem_stabilizer_iff.1 p.2.2, hs]
          rw [memP, hx]
          exact p.1.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp
      right_inv := fun p => by
        rcases p with ⟨⟨x, hx⟩, ⟨h, hh⟩⟩
        have hx' : (s x * h) • x₀ = x := by
          rw [mul_smul, mem_stabilizer_iff.1 hh, hs]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · exact hx'
        · show (s ((s x * h) • x₀))⁻¹ * (s x * h) = h
          rw [hx', inv_mul_cancel_left] }
  have hsec2 : ∀ h : G, IsConj t h → ∃ g : G, g⁻¹ * t * g = h := fun h hh => by
    obtain ⟨c, hc⟩ := isConj_iff.1 hh
    exact ⟨c⁻¹, by rw [inv_inv, ← hc]⟩
  let σ : G → G := fun h => if hh : IsConj t h then Classical.choose (hsec2 h hh) else 1
  have hσ : ∀ h : G, IsConj t h → (σ h)⁻¹ * t * σ h = h := fun h hh => by
    simp only [σ, hh, ↓reduceDIte]
    exact Classical.choose_spec (hsec2 h hh)
  have conjP : ∀ g : P, IsConj t ((g : G)⁻¹ * t * g) :=
    fun g => isConj_iff.2 ⟨(g : G)⁻¹, by rw [inv_inv]⟩
  have e2 : P ≃ Subgroup.centralizer ({t} : Set G) ×
      {h : G // h ∈ stabilizer G x₀ ∧ IsConj t h} :=
    { toFun := fun g => (⟨(g : G) * (σ ((g : G)⁻¹ * t * g))⁻¹, by
          have h := hσ _ (conjP g)
          set c := σ ((g : G)⁻¹ * t * g)
          have key : (g : G) * c⁻¹ * t * ((g : G) * c⁻¹)⁻¹ = t := by
            calc (g : G) * c⁻¹ * t * ((g : G) * c⁻¹)⁻¹ = (g : G) * (c⁻¹ * t * c) * (g : G)⁻¹ :=
                  by group
              _ = (g : G) * ((g : G)⁻¹ * t * g) * (g : G)⁻¹ := by rw [h]
              _ = t := by group
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc (g : G) * c⁻¹ * t = ((g : G) * c⁻¹ * t * ((g : G) * c⁻¹)⁻¹) * ((g : G) * c⁻¹) :=
                by group
            _ = t * ((g : G) * c⁻¹) := by rw [key]⟩,
        ⟨(g : G)⁻¹ * t * g, g.2, conjP g⟩)
      invFun := fun p => ⟨(p.1 : G) * σ p.2.1, by
          have hc : (p.1 : G) * t = t * p.1 := Subgroup.mem_centralizer_singleton_iff.1 p.1.2
          have e : ((p.1 : G) * σ p.2.1)⁻¹ * t * ((p.1 : G) * σ p.2.1) =
              (σ p.2.1)⁻¹ * t * σ p.2.1 := by
            calc ((p.1 : G) * σ p.2.1)⁻¹ * t * ((p.1 : G) * σ p.2.1) =
                (σ p.2.1)⁻¹ * ((p.1 : G)⁻¹ * (t * (p.1 : G))) * σ p.2.1 := by group
              _ = (σ p.2.1)⁻¹ * ((p.1 : G)⁻¹ * ((p.1 : G) * t)) * σ p.2.1 := by rw [hc]
              _ = (σ p.2.1)⁻¹ * t * σ p.2.1 := by group
          rw [e, hσ _ p.2.2.2]
          exact p.2.2.1⟩
      left_inv := fun g => by
        apply Subtype.ext
        simp
      right_inv := fun p => by
        rcases p with ⟨⟨c, hc⟩, ⟨h, hh⟩⟩
        have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.1 hc
        have key : (c * σ h)⁻¹ * t * (c * σ h) = h := by
          calc (c * σ h)⁻¹ * t * (c * σ h) = (σ h)⁻¹ * (c⁻¹ * (t * c)) * σ h := by group
            _ = (σ h)⁻¹ * (c⁻¹ * (c * t)) * σ h := by rw [hct]
            _ = (σ h)⁻¹ * t * σ h := by group
            _ = h := hσ h hh.2
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · show c * σ h * (σ ((c * σ h)⁻¹ * t * (c * σ h)))⁻¹ = c
          rw [key, mul_inv_cancel_right]
        · exact key }
  have c1 := Nat.card_congr e1
  have c2 := Nat.card_congr e2
  rw [Nat.card_prod] at c1 c2
  rw [← c1, c2]

end CFSG.GroupAction
