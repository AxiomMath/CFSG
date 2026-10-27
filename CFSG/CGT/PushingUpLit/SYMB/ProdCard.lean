module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open scoped Pointwise

variable {Γ : Type*} [Group Γ]

theorem le_normalizer_of_commute {C D : Subgroup Γ} (h : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) :
    C ≤ Subgroup.normalizer (D : Set Γ) := fun c hc => by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    have := h c hc d hd
    have e : c * d * c⁻¹ = d := by rw [this]; group
    rw [e]
    exact hd
  · intro hd'
    have h1 := h c hc _ hd'
    have e : c * d * c⁻¹ = d := by
      calc c * d * c⁻¹ = c⁻¹ * (c * (c * d * c⁻¹)) := by group
        _ = c⁻¹ * ((c * d * c⁻¹) * c) := by rw [h1]
        _ = d := by group
    rw [e] at hd'
    exact hd'

theorem card_sup_mul_card_inf_of_commute {C D : Subgroup Γ}
    (h : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) :
    Nat.card ↥(C ⊔ D) * Nat.card ↥(C ⊓ D) = Nat.card ↥C * Nat.card ↥D := by
  classical
  let f : ↥C × ↥D →* Γ :=
    { toFun := fun p => (p.1 : Γ) * (p.2 : Γ)
      map_one' := by simp
      map_mul' := fun p q => by
        have := h q.1 q.1.2 p.2 p.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (p.1 : Γ) * q.1 * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
          _ = p.1 * (p.2 * q.1) * q.2 := by rw [this]
          _ = (p.1 * p.2) * (q.1 * q.2) := by group }
  have hrange : f.range = C ⊔ D := by
    apply SetLike.coe_injective
    have hn : C ≤ Subgroup.normalizer (D : Set Γ) := le_normalizer_of_commute h
    rw [Subgroup.coe_mul_of_left_le_normalizer_right C D hn]
    ext x
    constructor
    · rintro ⟨⟨c, d⟩, rfl⟩
      exact ⟨c, c.2, d, d.2, rfl⟩
    · rintro ⟨c, hc, d, hd, rfl⟩
      exact ⟨(⟨c, hc⟩, ⟨d, hd⟩), rfl⟩
  have hker : Nat.card f.ker = Nat.card ↥(C ⊓ D) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.1 : Γ), p.1.1.2, by
          have h1 : (p.1.1 : Γ) * (p.1.2 : Γ) = 1 := p.2
          have : (p.1.1 : Γ) = ((p.1.2 : Γ))⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [this]
          exact D.inv_mem p.1.2.2⟩
        invFun := fun x => ⟨(⟨x.1, x.2.1⟩, ⟨x.1⁻¹, D.inv_mem x.2.2⟩), by
          show (x.1 : Γ) * x.1⁻¹ = 1
          group⟩
        left_inv := fun p => by
          have h1 : (p.1.1 : Γ) * (p.1.2 : Γ) = 1 := p.2
          have : (p.1.2 : Γ) = ((p.1.1 : Γ))⁻¹ := eq_inv_of_mul_eq_one_right h1
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            exact this.symm
        right_inv := fun x => rfl }
  have := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, Nat.card_prod] at this
  linarith

end CFSG.CGT.PushingUpLit.SYMB
