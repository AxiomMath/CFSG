module

public import CFSG.GH74.GLS.C3.Prop121.L122Fin
public meta import CFSG.GH74.GLS.C3.Prop121.L122Fin
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
public import CFSG.GH74.GLS.C3.Prop121.Fin6ClauseInputs
public meta import CFSG.GH74.GLS.C3.Prop121.Fin6ClauseInputs
public import Certificates.Certificate5087

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm

theorem ok6c_true : ok6c = true :=
  Certificates.certificate5087.1

theorem finite_six_clause4 {τ a b : Perm (Fin 7)}
    (ha : a * a = 1 ∧ a ≠ 1 ∧ sign a = 1) (hb : b * b = 1 ∧ b ≠ 1 ∧ sign b = 1)
    (hab : a * b = b * a ∧ a ≠ b)
    (hρ : ∃ ρ : Perm (Fin 7), ρ * ρ * ρ = 1 ∧ ρ ≠ 1 ∧ ρ * a = a * ρ ∧ ρ * b = b * ρ)
    (hτ : τ * τ * τ = 1 ∧ τ ≠ 1)
    (hτa : τ * a * τ⁻¹ = b ∨ τ * a * τ⁻¹ = a * b)
    (hτb : τ * b * τ⁻¹ = a ∨ τ * b * τ⁻¹ = b ∨ τ * b * τ⁻¹ = a * b)
    (h0 : a 0 = 0 ∧ b 0 = 0 ∧ τ 0 = 0) : τ.IsThreeCycle := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 ok6c_true a (mem_inv7.2 ha)) b (mem_inv7.2 hb)
  have hC0 : (a * b = b * a ∧ a ≠ b ∧ a 0 = 0 ∧ b 0 = 0) = True :=
    eq_true ⟨hab.1, hab.2, h0.1, h0.2.1⟩
  simp only [hC0, ite_true] at h1
  obtain ⟨ρ, hρ3, hρ1, hρa, hρb⟩ := hρ
  have h2 : (ord3.any fun ρ => decide (ρ * a = a * ρ ∧ ρ * b = b * ρ)) = true :=
    List.any_eq_true.2 ⟨ρ, mem_ord3.2 ⟨hρ3, hρ1⟩, by simp [hρa, hρb]⟩
  simp only [h2, ite_true] at h1
  have h3 := List.all_eq_true.1 h1 τ (mem_ord3.2 hτ)
  have hC1 : ((τ * a * τ⁻¹ = b ∨ τ * a * τ⁻¹ = a * b) ∧
      (τ * b * τ⁻¹ = a ∨ τ * b * τ⁻¹ = b ∨ τ * b * τ⁻¹ = a * b) ∧ τ 0 = 0) = True :=
    eq_true ⟨hτa, hτb, h0.2.2⟩
  simp only [hC1, ite_true] at h3
  exact card_support_eq_three_iff.1 (of_decide_eq_true h3)

theorem exists_comm_ord3_six_check :
    ((allPerms 6).all fun σ =>
      !(decide (σ * σ * σ = 1 ∧ σ ≠ 1)) ||
        (allPerms 6).any fun k =>
          decide (k * k * k = 1 ∧ k ≠ 1 ∧ k * σ = σ * k ∧ k ≠ σ ∧ k ≠ σ⁻¹)) = true :=
  Certificates.certificate5087.2

theorem exists_comm_ord3_six
    {σ : Perm (Fin 6)} (hσ : σ * σ * σ = 1 ∧ σ ≠ 1) :
    ∃ k : Perm (Fin 6), k * k * k = 1 ∧ k ≠ 1 ∧ k * σ = σ * k ∧ k ≠ σ ∧ k ≠ σ⁻¹ := by
  have h1 := List.all_eq_true.1 exists_comm_ord3_six_check σ (mem_allPerms 6 σ)
  have h2 : decide (σ * σ * σ = 1 ∧ σ ≠ 1) = true := decide_eq_true hσ
  rw [h2] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  obtain ⟨k, -, hk⟩ := List.any_eq_true.1 h1
  exact ⟨k, of_decide_eq_true hk⟩

end CFSG.GH74.GLS.C3.Prop121
