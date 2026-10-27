module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms

section Def

theorem m22_delta_conj'
    : ∀ h ∈ NativeSporadic.M22, m22Delta⁻¹ * h * m22Delta ∈ NativeSporadic.M22 :=
  inv_conj_mem _ m22_delta_normalizes m22_delta_sq

def m22AExp
    : Subgroup (Equiv.Perm (Fin 22)) where
  carrier := {x | x ∈ NativeSporadic.M22 ∨ m22Delta⁻¹ * x ∈ NativeSporadic.M22}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (mul_mem hx hy)
    · refine Or.inr ?_
      have : m22Delta⁻¹ * (x * y) = (m22Delta⁻¹ * x * m22Delta) * (m22Delta⁻¹ * y) := by group
      rw [this]
      exact mul_mem (m22_delta_conj' x hx) hy
    · refine Or.inr ?_
      rw [← mul_assoc]
      exact mul_mem hx hy
    · refine Or.inl ?_
      have : x * y = (m22Delta * m22Delta) * (m22Delta⁻¹ * (m22Delta⁻¹ * x) * m22Delta) *
          (m22Delta⁻¹ * y) := by group
      rw [this]
      exact mul_mem (mul_mem m22_delta_sq (m22_delta_conj' _ hx)) hy
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have : m22Delta⁻¹ * x⁻¹ = (m22Delta⁻¹ * (m22Delta⁻¹ * x)⁻¹ * m22Delta) *
          (m22Delta * m22Delta)⁻¹ := by group
      rw [this]
      exact mul_mem (m22_delta_conj' _ (inv_mem hx)) (inv_mem m22_delta_sq)

theorem mem_m22AExp
    {x : Equiv.Perm (Fin 22)} :
    x ∈ m22AExp ↔ x ∈ NativeSporadic.M22 ∨ m22Delta⁻¹ * x ∈ NativeSporadic.M22 := Iff.rfl

@[expose] def m22A : Subgroup (Equiv.Perm (Fin 22)) := Subgroup.closure {m22gA, m22gB, m22Delta}

theorem m22_le_A : NativeSporadic.M22 ≤ m22A := by
  rw [m22_eq]
  exact Subgroup.closure_mono fun x hx => by
    rcases hx with rfl | rfl <;> simp

theorem delta_mem_A : m22Delta ∈ m22A := Subgroup.subset_closure (by simp)

theorem m22A_eq : m22A = m22AExp := by
  apply le_antisymm
  · rw [m22A, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact mem_m22AExp.2 (Or.inl m22a.2)
    · exact mem_m22AExp.2 (Or.inl m22b.2)
    · exact mem_m22AExp.2 (Or.inr (by simp))
  · intro x hx
    rcases mem_m22AExp.1 hx with hx | hx
    · exact m22_le_A hx
    · have : x = m22Delta * (m22Delta⁻¹ * x) := by group
      rw [this]
      exact mul_mem delta_mem_A (m22_le_A hx)

theorem mem_m22A
    {x : Equiv.Perm (Fin 22)} :
    x ∈ m22A ↔ x ∈ NativeSporadic.M22 ∨ m22Delta⁻¹ * x ∈ NativeSporadic.M22 := by
  rw [m22A_eq]
  exact mem_m22AExp

theorem delta_not_mem
    : m22Delta ∉ NativeSporadic.M22 := by
  intro h
  exact m22_delta_outer m22Delta⁻¹ (inv_mem h) (fun k _ => by simp)

theorem A_norm
    {a : Equiv.Perm (Fin 22)} (ha : a ∈ m22A) :
    ∀ h ∈ NativeSporadic.M22, a * h * a⁻¹ ∈ NativeSporadic.M22 := by
  rcases mem_m22A.1 ha with ha | ha
  · exact fun h hh => mul_mem (mul_mem ha hh) (inv_mem ha)
  · intro h hh
    have e : a = m22Delta * (m22Delta⁻¹ * a) := by group
    rw [e]
    have : m22Delta * (m22Delta⁻¹ * a) * h * (m22Delta * (m22Delta⁻¹ * a))⁻¹ =
        m22Delta * ((m22Delta⁻¹ * a) * h * (m22Delta⁻¹ * a)⁻¹) * m22Delta⁻¹ := by group
    rw [this]
    exact m22_delta_normalizes _ (mul_mem (mul_mem ha hh) (inv_mem ha))

theorem A_norm'
    {a : Equiv.Perm (Fin 22)} (ha : a ∈ m22A) :
    ∀ h ∈ NativeSporadic.M22, a⁻¹ * h * a ∈ NativeSporadic.M22 := by
  intro h hh
  have := A_norm (inv_mem ha) h hh
  simpa using this

theorem mul_delta_mem_iff
    {P : Equiv.Perm (Fin 22)} :
    P * m22Delta ∈ NativeSporadic.M22 ↔ m22Delta⁻¹ * P ∈ NativeSporadic.M22 := by
  constructor
  · intro h
    have e : m22Delta⁻¹ * P =
        (m22Delta⁻¹ * (P * m22Delta) * m22Delta) * (m22Delta * m22Delta)⁻¹ := by group
    rw [e]
    exact mul_mem (m22_delta_conj' _ h) (inv_mem m22_delta_sq)
  · intro h
    have e : P * m22Delta =
        (m22Delta * m22Delta) * (m22Delta⁻¹ * (m22Delta⁻¹ * P) * m22Delta) := by group
    rw [e]
    exact mul_mem m22_delta_sq (m22_delta_conj' _ h)

theorem card_A
    : Nat.card m22A = 2 * 443520 := by
  have hmul := Subgroup.card_mul_index (NativeSporadic.M22.subgroupOf m22A)
  have hidx : (NativeSporadic.M22.subgroupOf m22A).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨m22Delta, delta_mem_A⟩, fun b => ?_⟩
    have hb := mem_m22A.1 b.2
    show Xor ((b : Equiv.Perm (Fin 22)) * m22Delta ∈ NativeSporadic.M22)
      ((b : Equiv.Perm (Fin 22)) ∈ NativeSporadic.M22)
    rw [mul_delta_mem_iff]
    rcases hb with h | h
    · refine Or.inr ⟨h, fun h' => delta_not_mem ?_⟩
      have := inv_mem (mul_mem h' (inv_mem h))
      simpa using this
    · refine Or.inl ⟨h, fun h' => delta_not_mem ?_⟩
      have := inv_mem (mul_mem h (inv_mem h'))
      simpa using this
  have hH : Nat.card (NativeSporadic.M22.subgroupOf m22A) = 443520 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe m22_le_A).toEquiv, card_M22]
  rw [hH, hidx] at hmul
  rw [← hmul]

@[expose] def aA : ↥m22A := ⟨m22gA, m22_le_A m22a.2⟩

@[expose] def bA : ↥m22A := ⟨m22gB, m22_le_A m22b.2⟩

@[expose] def dA : ↥m22A := ⟨m22Delta, delta_mem_A⟩

end Def

end CFSG.QuasithinUnique.Setup.X1
