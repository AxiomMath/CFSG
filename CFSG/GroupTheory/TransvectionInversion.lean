module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

private lemma inv_conj_eq_mul_inv_of_conj_eq_mul {u v s : G}
    (hsu : s * u * s⁻¹ = u * v) (hsv : s * v * s⁻¹ = v) :
    s⁻¹ * u * s = u * v⁻¹ := by
  have hsv' : s⁻¹ * v * s = v := by
    calc s⁻¹ * v * s = s⁻¹ * (s * v * s⁻¹) * s :=
        (congrArg (fun x => s⁻¹ * x * s) hsv).symm
      _ = v := by group
  have h : u = (s⁻¹ * u * s) * (s⁻¹ * v * s) := by
    calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
      _ = s⁻¹ * (u * v) * s := by rw [hsu]
      _ = (s⁻¹ * u * s) * (s⁻¹ * v * s) := by group
  have h' : u = (s⁻¹ * u * s) * v := by simpa [hsv'] using h
  calc s⁻¹ * u * s = (s⁻¹ * u * s) * v * v⁻¹ := by group
    _ = u * v⁻¹ := by rw [← h']

private lemma inv_conj_eq_mul_of_conj_eq_mul_inv {u v s : G}
    (hsu : s * u * s⁻¹ = u * v⁻¹) (hsv : s * v * s⁻¹ = v) :
    s⁻¹ * u * s = u * v := by
  have hsv' : s * v⁻¹ * s⁻¹ = v⁻¹ := by
    calc s * v⁻¹ * s⁻¹ = (s * v * s⁻¹)⁻¹ := by group
      _ = v⁻¹ := by rw [hsv]
  simpa using inv_conj_eq_mul_inv_of_conj_eq_mul (v := v⁻¹) hsu hsv'

private lemma conj_sq_inv_of_actions {u v s r : G} (huv : Commute u v)
    (hsu : s * u * s⁻¹ = u) (hsv : s * v * s⁻¹ = v * u)
    (hru : r * u * r⁻¹ = u * v⁻¹) (hrv : r * v * r⁻¹ = v) :
    ((s * r * s) ^ 2) * u * ((s * r * s) ^ 2)⁻¹ = u⁻¹ ∧
      ((s * r * s) ^ 2) * v * ((s * r * s) ^ 2)⁻¹ = v⁻¹ := by
  have hgu : (s * r * s) * u * (s * r * s)⁻¹ = v⁻¹ := by
    calc (s * r * s) * u * (s * r * s)⁻¹
        = s * (r * (s * u * s⁻¹) * r⁻¹) * s⁻¹ := by group
      _ = s * (r * u * r⁻¹) * s⁻¹ := by rw [hsu]
      _ = s * (u * v⁻¹) * s⁻¹ := by rw [hru]
      _ = (s * u * s⁻¹) * (s * v⁻¹ * s⁻¹) := by group
      _ = u * (s * v * s⁻¹)⁻¹ := by rw [hsu]; group
      _ = u * (v * u)⁻¹ := by rw [hsv]
      _ = v⁻¹ := by rw [mul_inv_rev]; group
  have hgv : (s * r * s) * v * (s * r * s)⁻¹ = u := by
    calc (s * r * s) * v * (s * r * s)⁻¹
        = s * (r * (s * v * s⁻¹) * r⁻¹) * s⁻¹ := by group
      _ = s * (r * (v * u) * r⁻¹) * s⁻¹ := by rw [hsv]
      _ = s * ((r * v * r⁻¹) * (r * u * r⁻¹)) * s⁻¹ := by group
      _ = s * (v * (u * v⁻¹)) * s⁻¹ := by rw [hrv, hru]
      _ = (s * v * s⁻¹) * (s * u * s⁻¹) * (s * v⁻¹ * s⁻¹) := by group
      _ = (s * v * s⁻¹) * (s * u * s⁻¹) * (s * v * s⁻¹)⁻¹ := by group
      _ = (v * u) * u * (v * u)⁻¹ := by rw [hsv, hsu]
      _ = u := by
        rw [show (v * u) * u * (v * u)⁻¹ = v * u * v⁻¹ by group]
        rw [← huv.eq]
        group
  constructor
  · calc ((s * r * s) ^ 2) * u * ((s * r * s) ^ 2)⁻¹
        = (s * r * s) * ((s * r * s) * u * (s * r * s)⁻¹) * (s * r * s)⁻¹ := by
          rw [pow_two]; group
      _ = (s * r * s) * v⁻¹ * (s * r * s)⁻¹ := by rw [hgu]
      _ = ((s * r * s) * v * (s * r * s)⁻¹)⁻¹ := by group
      _ = u⁻¹ := by rw [hgv]
  · calc ((s * r * s) ^ 2) * v * ((s * r * s) ^ 2)⁻¹
        = (s * r * s) * ((s * r * s) * v * (s * r * s)⁻¹) * (s * r * s)⁻¹ := by
          rw [pow_two]; group
      _ = (s * r * s) * u * (s * r * s)⁻¹ := by rw [hgv]
      _ = v⁻¹ := hgu

theorem exists_mem_closure_conj_eq_inv_of_transvections {u v s₁ s₂ : G} (huv : Commute u v)
    (h₁u : s₁ * u * s₁⁻¹ = u) (h₁v : s₁ * v * s₁⁻¹ = v * u ∨ s₁ * v * s₁⁻¹ = v * u⁻¹)
    (h₂v : s₂ * v * s₂⁻¹ = v)
    (h₂u : s₂ * u * s₂⁻¹ = u * v ∨ s₂ * u * s₂⁻¹ = u * v⁻¹) :
    ∃ t ∈ Subgroup.closure ({s₁, s₂} : Set G), t * u * t⁻¹ = u⁻¹ ∧ t * v * t⁻¹ = v⁻¹ := by
  have hs₁ : s₁ ∈ Subgroup.closure ({s₁, s₂} : Set G) := Subgroup.subset_closure (by simp)
  have hs₂ : s₂ ∈ Subgroup.closure ({s₁, s₂} : Set G) := Subgroup.subset_closure (by simp)
  have hs₂' : s₂⁻¹ ∈ Subgroup.closure ({s₁, s₂} : Set G) := Subgroup.inv_mem _ hs₂
  rcases h₁v with h₁v | h₁v <;> rcases h₂u with h₂u | h₂u
  ·
    have hru : s₂⁻¹ * u * s₂ = u * v⁻¹ := inv_conj_eq_mul_inv_of_conj_eq_mul h₂u h₂v
    refine ⟨(s₁ * s₂⁻¹ * s₁) ^ 2, ?_,
      conj_sq_inv_of_actions huv h₁u h₁v (by simpa using hru)
        (by
          have hcomm : Commute s₂ v := mul_inv_eq_iff_eq_mul.mp h₂v
          simpa using hcomm.inv_mul_cancel)⟩
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs₁ hs₂') hs₁) 2
  ·
    refine ⟨(s₁ * s₂ * s₁) ^ 2, ?_,
      conj_sq_inv_of_actions huv h₁u h₁v h₂u h₂v⟩
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs₁ hs₂) hs₁) 2
  ·
    have h₁u' : s₁ * u⁻¹ * s₁⁻¹ = u⁻¹ := by
      calc s₁ * u⁻¹ * s₁⁻¹ = (s₁ * u * s₁⁻¹)⁻¹ := by group
        _ = u⁻¹ := by rw [h₁u]
    have h₂u' : s₂ * u⁻¹ * s₂⁻¹ = u⁻¹ * v⁻¹ := by
      calc s₂ * u⁻¹ * s₂⁻¹ = (s₂ * u * s₂⁻¹)⁻¹ := by group
        _ = (u * v)⁻¹ := by rw [h₂u]
        _ = u⁻¹ * v⁻¹ := by rw [mul_inv_rev, huv.inv_inv.eq]
    have h := conj_sq_inv_of_actions (u := u⁻¹) (v := v) (s := s₁) (r := s₂)
      huv.inv_left h₁u' h₁v h₂u' h₂v
    refine ⟨(s₁ * s₂ * s₁) ^ 2, ?_, ?_, h.2⟩
    · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs₁ hs₂) hs₁) 2
    · have h' : (s₁ * s₂ * s₁) ^ 2 * u⁻¹ * ((s₁ * s₂ * s₁) ^ 2)⁻¹ = u := by simpa using h.1
      calc (s₁ * s₂ * s₁) ^ 2 * u * ((s₁ * s₂ * s₁) ^ 2)⁻¹
          = ((s₁ * s₂ * s₁) ^ 2 * u⁻¹ * ((s₁ * s₂ * s₁) ^ 2)⁻¹)⁻¹ := by
            rw [conj_inv (a := u⁻¹) (b := (s₁ * s₂ * s₁) ^ 2), inv_inv]
        _ = u⁻¹ := by rw [h']
  ·
    have h₁u' : s₁ * u⁻¹ * s₁⁻¹ = u⁻¹ := by
      calc s₁ * u⁻¹ * s₁⁻¹ = (s₁ * u * s₁⁻¹)⁻¹ := by group
        _ = u⁻¹ := by rw [h₁u]
    have hru : s₂⁻¹ * u * s₂ = u * v := inv_conj_eq_mul_of_conj_eq_mul_inv h₂u h₂v
    have h₂u' : s₂⁻¹ * u⁻¹ * s₂ = u⁻¹ * v⁻¹ := by
      calc s₂⁻¹ * u⁻¹ * s₂ = (s₂⁻¹ * u * s₂)⁻¹ := by group
        _ = (u * v)⁻¹ := by rw [hru]
        _ = u⁻¹ * v⁻¹ := by rw [mul_inv_rev, huv.inv_inv.eq]
    have h := conj_sq_inv_of_actions (u := u⁻¹) (v := v) (s := s₁) (r := s₂⁻¹)
      huv.inv_left h₁u' h₁v (by simpa using h₂u')
        (by
          have hcomm : Commute s₂ v := mul_inv_eq_iff_eq_mul.mp h₂v
          simpa using hcomm.inv_mul_cancel)
    refine ⟨(s₁ * s₂⁻¹ * s₁) ^ 2, ?_, ?_, h.2⟩
    · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hs₁ hs₂') hs₁) 2
    · have h' : (s₁ * s₂⁻¹ * s₁) ^ 2 * u⁻¹ * ((s₁ * s₂⁻¹ * s₁) ^ 2)⁻¹ = u := by simpa using h.1
      calc (s₁ * s₂⁻¹ * s₁) ^ 2 * u * ((s₁ * s₂⁻¹ * s₁) ^ 2)⁻¹
          = ((s₁ * s₂⁻¹ * s₁) ^ 2 * u⁻¹ * ((s₁ * s₂⁻¹ * s₁) ^ 2)⁻¹)⁻¹ := by
            rw [conj_inv (a := u⁻¹) (b := (s₁ * s₂⁻¹ * s₁) ^ 2), inv_inv]
        _ = u⁻¹ := by rw [h']

end CFSG.GroupTheory
