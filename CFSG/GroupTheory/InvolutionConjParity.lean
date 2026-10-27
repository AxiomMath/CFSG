module

public import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GroupTheory

theorem ncard_modEq_ncard_fixedPoints {α : Type*} {S : Set α} (hS : S.Finite) {σ : α → α}
    (hmaps : ∀ x ∈ S, σ x ∈ S) (hinv : ∀ x ∈ S, σ (σ x) = x) :
    S.ncard ≡ {x | x ∈ S ∧ σ x = x}.ncard [MOD 2] := by
  classical
  let _ : Fintype S := hS.fintype
  let σ' : S → S := fun x => ⟨σ x.1, hmaps x.1 x.2⟩
  let f : Function.End S := σ'
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext x
    exact Subtype.ext (hinv x.1 x.2)
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  change Fintype.card S ≡ Fintype.card (Function.fixedPoints σ') [MOD 2] at h
  have h1 : Fintype.card S = S.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have h2 : (Function.fixedPoints σ').ncard = {x | x ∈ S ∧ σ x = x}.ncard := by
    let e : Function.fixedPoints σ' ≃ {x : α | x ∈ S ∧ σ x = x} :=
      { toFun := fun x => ⟨x.1.1, x.1.2, by
          simpa [σ'] using congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
          show σ' ⟨y.1, y.2.1⟩ = ⟨y.1, y.2.1⟩
          exact Subtype.ext y.2.2⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun y => by ext; rfl }
    exact Set.ncard_congr' e
  have h3 : Fintype.card (Function.fixedPoints σ') = {x | x ∈ S ∧ σ x = x}.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, h2]
  rwa [h1, h3] at h

theorem ncard_modEq_ncard_setOf_commute {X : Type*} [Group X] {S : Set X} (hS : S.Finite)
    {g : X} (hg : g * g = 1) (hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    S.ncard ≡ {s | s ∈ S ∧ Commute g s}.ncard [MOD 2] := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hinv : ∀ x ∈ S, g * (g * x * g⁻¹) * g⁻¹ = x := by
    intro x _
    calc g * (g * x * g⁻¹) * g⁻¹ = (g * g) * x * (g⁻¹ * g⁻¹) := by group
      _ = x := by rw [hg, hginv, hg, one_mul, mul_one]
  have h := ncard_modEq_ncard_fixedPoints hS (σ := fun s => g * s * g⁻¹) hgS hinv
  have hset : {s | s ∈ S ∧ g * s * g⁻¹ = s} = {s | s ∈ S ∧ Commute g s} := by
    ext s
    constructor
    · rintro ⟨hs, hgs⟩
      refine ⟨hs, (commute_iff_eq g s).mpr ?_⟩
      calc g * s = (g * s * g⁻¹) * g := by group
        _ = s * g := by rw [hgs]
    · rintro ⟨hs, hc⟩
      exact ⟨hs, hc.mul_inv_cancel⟩
  rwa [hset] at h

end CFSG.GroupTheory

end
