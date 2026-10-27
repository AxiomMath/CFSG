module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6AutCent
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Quasithin.SteinbergCB

@[expose] def a6c012 : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a6c013 : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 3, mem_alternatingGroup.mpr (by decide)⟩

@[expose] def alt4List : List (alternatingGroup (Fin 6)) :=
  [1, a6c012, a6c013, a6c012 * a6c012, a6c012 * a6c013, a6c013 * a6c012, a6c013 * a6c013,
    a6c012 * a6c012 * a6c013, a6c012 * a6c013 * a6c013, a6c013 * a6c012 * a6c012,
    a6c013 * a6c013 * a6c012, a6c012 * a6c013 * a6c013 * a6c012]

theorem alt4List_mul : ∀ x ∈ alt4List, ∀ y ∈ alt4List, x * y ∈ alt4List := by decide +kernel

theorem alt4List_inv : ∀ x ∈ alt4List, x⁻¹ ∈ alt4List := by decide +kernel

@[expose] def alt4in6 : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | x ∈ alt4List}
  mul_mem' := fun {x y} hx hy => alt4List_mul x hx y hy
  one_mem' := List.mem_cons_self
  inv_mem' := fun {x} hx => alt4List_inv x hx

theorem mem_alt4in6 {x : alternatingGroup (Fin 6)} : x ∈ alt4in6 ↔ x ∈ alt4List := Iff.rfl

instance : DecidablePred (· ∈ alt4in6) := fun _ => decidable_of_iff _ mem_alt4in6.symm

theorem card_alt4in6 : Nat.card alt4in6 = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem fix_alt4in6 {β : MulAut (alternatingGroup (Fin 6))} (h1 : β a6c012 = a6c012)
    (h2 : β a6c013 = a6c013) : ∀ l ∈ alt4in6, β l = l := by
  intro l hl
  rw [mem_alt4in6] at hl
  simp only [alt4List, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [map_mul, h1, h2]

theorem eq_one_or_eq_conj45 {β : MulAut (alternatingGroup (Fin 6))} (h1 : β a6c012 = a6c012)
    (h2 : β a6c013 = a6c013) : β = 1 ∨ β = conjPerm 6 (swap 4 5) := by
  have hα2 : ∀ k, conjPerm 6 (swap 4 5) (conjPerm 6 (swap 4 5) k) = k := by
    intro k
    apply Subtype.ext
    rw [conjPerm_apply, conjPerm_apply]
    simp [mul_assoc, swap_mul_self_mul]
  have hα1 : ∃ k, conjPerm 6 (swap 4 5) k ≠ k := by
    refine ⟨⟨swap 0 1 * swap 1 4, mem_alternatingGroup.mpr (by decide)⟩, fun h => ?_⟩
    have := congrArg Subtype.val h
    rw [conjPerm_apply] at this
    revert this
    decide
  have hαL : ∀ l ∈ alt4in6, conjPerm 6 (swap 4 5) l = l := by
    refine fix_alt4in6 (Subtype.ext ?_) (Subtype.ext ?_) <;> rw [conjPerm_apply] <;> decide
  exact CFSG.QuasithinUnique.DoubleA3.aut_eq_of_fixes_A4 (MulEquiv.refl _) _ hα2 hα1 alt4in6
    card_alt4in6 hαL β (fix_alt4in6 h1 h2)

@[expose] def GoodY (y : Perm (Fin 6)) : Prop :=
  ((a6c012 : Perm (Fin 6)) * y) ^ 2 = 1 ∧ y ≠ a6c012 ∧ y ≠ (a6c012 : Perm (Fin 6))⁻¹ ∧
    y.support.card = 3

instance (y : Perm (Fin 6)) : Decidable (GoodY y) := by unfold GoodY; infer_instance

@[expose] def SolY (y : Perm (Fin 6)) : Prop :=
  ∃ σ : Perm (Fin 6), σ * a6c012 * σ⁻¹ = a6c012 ∧ σ * y * σ⁻¹ = a6c013

instance (y : Perm (Fin 6)) : Decidable (SolY y) := by unfold SolY; infer_instance

theorem exists_conj_fix_c013 : ∀ y : Perm (Fin 6), GoodY y → SolY y := by decide +kernel

theorem isThreeCycle_a6c012 : (a6c012 : Perm (Fin 6)).IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide)

theorem exists_perm_of_isThreeCycle (θ : MulAut (alternatingGroup (Fin 6)))
    (hθ : ((θ a6c012 : alternatingGroup (Fin 6)) : Perm (Fin 6)).IsThreeCycle) :
    ∃ σ : Perm (Fin 6), ∀ g : alternatingGroup (Fin 6),
      ((θ g : alternatingGroup (Fin 6)) : Perm (Fin 6)) = σ * g * σ⁻¹ := by
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : Perm (Fin 6),
      σ₁ * ((θ a6c012 : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ₁⁻¹ = a6c012 :=
    isConj_iff.mp (isConj_iff_cycleType_eq.mpr (by rw [hθ, isThreeCycle_a6c012]))
  set θ₁ := θ.trans (conjPerm 6 σ₁) with hθ₁
  have hθ₁v : ∀ g, ((θ₁ g : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      σ₁ * ((θ g : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ₁⁻¹ := fun g => by
    rw [hθ₁, MulEquiv.trans_apply, conjPerm_apply]
  have h1 : θ₁ a6c012 = a6c012 := Subtype.ext (by rw [hθ₁v, hσ₁])
  set y : Perm (Fin 6) := ((θ₁ a6c013 : alternatingGroup (Fin 6)) : Perm (Fin 6)) with hy
  have hh : ∃ h : alternatingGroup (Fin 6), a6c013 = h * a6c012 * h⁻¹ :=
    ⟨⟨swap 2 3 * swap 4 5, mem_alternatingGroup.mpr (by decide)⟩, by decide⟩
  obtain ⟨h, hh⟩ := hh
  have hy3 : y.support.card = 3 := by
    have : y = (θ₁ h : Perm (Fin 6)) * a6c012 * (θ₁ h : Perm (Fin 6))⁻¹ := by
      rw [hy, hh, map_mul, map_mul, map_inv, h1]
      rfl
    rw [this, card_support_conj]
    decide
  have hsq : ((a6c012 : Perm (Fin 6)) * y) ^ 2 = 1 := by
    have h0 : (a6c012 * a6c013) ^ 2 = 1 := by decide
    have := congrArg (fun g => ((θ₁ g : alternatingGroup (Fin 6)) : Perm (Fin 6))) h0
    simpa [map_pow, map_mul, h1] using this
  have hne1 : y ≠ a6c012 := fun he => by
    have : θ₁ a6c013 = θ₁ a6c012 := Subtype.ext (by rw [h1]; exact he)
    exact absurd (θ₁.injective this) (by decide)
  have hne2 : y ≠ (a6c012 : Perm (Fin 6))⁻¹ := fun he => by
    have : θ₁ a6c013 = θ₁ a6c012⁻¹ := Subtype.ext (by rw [map_inv, h1]; exact he)
    exact absurd (θ₁.injective this) (by decide)
  obtain ⟨σ₂, hσ₂a, hσ₂b⟩ := exists_conj_fix_c013 y ⟨hsq, hne1, hne2, hy3⟩
  set θ₂ := θ₁.trans (conjPerm 6 σ₂) with hθ₂
  have hθ₂v : ∀ g, ((θ₂ g : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      σ₂ * ((θ₁ g : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ₂⁻¹ := fun g => by
    rw [hθ₂, MulEquiv.trans_apply, conjPerm_apply]
  have e1 : θ₂ a6c012 = a6c012 := Subtype.ext (by rw [hθ₂v, h1]; exact hσ₂a)
  have e2 : θ₂ a6c013 = a6c013 := Subtype.ext (by rw [hθ₂v]; exact hσ₂b)
  have key : ∀ g, ((θ g : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      (σ₂ * σ₁)⁻¹ * ((θ₂ g : alternatingGroup (Fin 6)) : Perm (Fin 6)) * (σ₂ * σ₁) := fun g => by
    rw [hθ₂v, hθ₁v]
    group
  rcases eq_one_or_eq_conj45 e1 e2 with he | he
  · exact ⟨(σ₂ * σ₁)⁻¹, fun g => by rw [key, he]; simp⟩
  · refine ⟨(σ₂ * σ₁)⁻¹ * swap 4 5, fun g => ?_⟩
    rw [key, he, conjPerm_apply]
    group

end CFSG.ComponentClassification.RankTwoAlt
