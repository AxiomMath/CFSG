module

public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public import Mathlib.GroupTheory.Perm.Cycle.Type
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.GroupTheory.Perm.Fin
public meta import Mathlib.GroupTheory.Perm.Support
public meta import Mathlib.GroupTheory.Perm.Cycle.Basic
public meta import Mathlib.GroupTheory.Perm.Cycle.Type
public meta import Mathlib.Logic.Equiv.Fin.Basic
public meta import Mathlib.Logic.Equiv.Option
public meta import Mathlib.Data.List.FinRange
public import CFSG.GH74.GLS.C3.Prop121.L122FinInputs
public meta import CFSG.GH74.GLS.C3.Prop121.L122FinInputs
public import Certificates.Certificate5090

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm

theorem mem_inv7 {s : Perm (Fin 7)} : s ∈ inv7 ↔ s * s = 1 ∧ s ≠ 1 ∧ sign s = 1 := by
  simp [inv7, mem_allPerms]

theorem mem_ord3 {s : Perm (Fin 7)} : s ∈ ord3 ↔ s * s * s = 1 ∧ s ≠ 1 := by
  simp [ord3, mem_allPerms]

theorem ok122_true : ok122 = true :=
  Certificates.certificate5090.1

theorem finite122 {σ a b : Perm (Fin 7)}
    (ha : a * a = 1 ∧ a ≠ 1 ∧ sign a = 1) (hb : b * b = 1 ∧ b ≠ 1 ∧ sign b = 1)
    (hab : a * b = b * a ∧ a ≠ b)
    (hρ : ∃ ρ : Perm (Fin 7), ρ * ρ * ρ = 1 ∧ ρ ≠ 1 ∧ ρ * a = a * ρ ∧ ρ * b = b * ρ)
    (hσ : σ * σ * σ = 1 ∧ σ ≠ 1)
    (hσa : σ * a * σ⁻¹ = b ∨ σ * a * σ⁻¹ = a * b)
    (hσb : σ * b * σ⁻¹ = a ∨ σ * b * σ⁻¹ = b ∨ σ * b * σ⁻¹ = a * b)
    (hτ : ∀ i j : Fin 7, i ≠ j → swap i j * a = a * swap i j → swap i j * b = b * swap i j →
      (σ * swap i j * σ⁻¹ * (swap i j)⁻¹ = 1 ∨ σ * swap i j * σ⁻¹ * (swap i j)⁻¹ = a ∨
        σ * swap i j * σ⁻¹ * (swap i j)⁻¹ = b ∨ σ * swap i j * σ⁻¹ * (swap i j)⁻¹ = a * b)) :
    σ.IsThreeCycle := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 ok122_true a (mem_inv7.2 ha)) b (mem_inv7.2 hb)
  have hC0 : (a * b = b * a ∧ a ≠ b) = True := eq_true hab
  simp only [hC0, ite_true] at h1
  obtain ⟨ρ, hρ3, hρ1, hρa, hρb⟩ := hρ
  have h2 : (ord3.any fun ρ => decide (ρ * a = a * ρ ∧ ρ * b = b * ρ)) = true :=
    List.any_eq_true.2 ⟨ρ, mem_ord3.2 ⟨hρ3, hρ1⟩, by simp [hρa, hρb]⟩
  simp only [h2, ite_true] at h1
  have h3 := List.all_eq_true.1 h1 σ (mem_ord3.2 hσ)
  have hC1 : ((σ * a * σ⁻¹ = b ∨ σ * a * σ⁻¹ = a * b) ∧
      (σ * b * σ⁻¹ = a ∨ σ * b * σ⁻¹ = b ∨ σ * b * σ⁻¹ = a * b)) = True :=
    eq_true ⟨hσa, hσb⟩
  have h4 : ((List.finRange 7).all fun i => (List.finRange 7).all fun j =>
      decide (i = j) || !(decide (swap i j * a = a * swap i j ∧ swap i j * b = b * swap i j))
        || inV a b (σ * swap i j * σ⁻¹ * (swap i j)⁻¹)) = true := by
    rw [List.all_eq_true]
    intro i _
    rw [List.all_eq_true]
    intro j _
    by_cases hij : i = j
    · simp [hij]
    · by_cases hc : swap i j * a = a * swap i j ∧ swap i j * b = b * swap i j
      · have h5 : inV a b (σ * swap i j * σ⁻¹ * (swap i j)⁻¹) = true :=
          decide_eq_true (hτ i j hij hc.1 hc.2)
        rw [h5]
        simp
      · simp [hij, hc]
  simp only [hC1, h4, ite_true] at h3
  exact card_support_eq_three_iff.1 (of_decide_eq_true h3)

theorem exists_ord3_comm_check :
    (inv7.all fun a => ord3.any fun ρ => decide (ρ * a = a * ρ)) = true :=
  Certificates.certificate5090.2

theorem exists_ord3_comm
    {a : Perm (Fin 7)} (ha : a * a = 1 ∧ a ≠ 1 ∧ sign a = 1) :
    ∃ ρ : Perm (Fin 7), ρ * ρ * ρ = 1 ∧ ρ ≠ 1 ∧ sign ρ = 1 ∧ ρ * a = a * ρ := by
  have h1 := List.all_eq_true.1 exists_ord3_comm_check a (mem_inv7.2 ha)
  obtain ⟨ρ, hρ, hc⟩ := List.any_eq_true.1 h1
  have hρ' := mem_ord3.1 hρ
  refine ⟨ρ, hρ'.1, hρ'.2, ?_, of_decide_eq_true hc⟩
  have h3 : sign ρ * sign ρ * sign ρ = 1 := by
    rw [← map_mul, ← map_mul, hρ'.1, map_one]
  rcases Int.units_eq_one_or (sign ρ) with h | h
  · exact h
  · rw [h] at h3
    exact absurd h3 (by decide)

theorem eq_one_of_cube_eq_one (d : Perm (Fin 4)) (hd : d * CFSG.GH74.GLS.C3.Layer2.Model.x4 =
    CFSG.GH74.GLS.C3.Layer2.Model.x4 * d) (h3 : d * d * d = 1) : d = 1 := by
  revert d
  decide

end CFSG.GH74.GLS.C3.Prop121
