module

public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
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
public import CFSG.GH74.GLS.C3.Prop121.CentKFinInputs
public meta import CFSG.GH74.GLS.C3.Prop121.CentKFinInputs
public import Certificates.Certificate5085

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm

theorem mem_inv6 {s : Perm (Fin 6)} : s ∈ inv6 ↔ s * s = 1 ∧ s ≠ 1 ∧ sign s = 1 := by
  simp [inv6, mem_allPerms]

theorem mem_ord3six {s : Perm (Fin 6)} : s ∈ ord3six ↔ s * s * s = 1 ∧ s ≠ 1 := by
  simp [ord3six, mem_allPerms]

theorem mem_even6 {s : Perm (Fin 6)} : s ∈ even6 ↔ sign s = 1 := by
  simp [even6, mem_allPerms]

theorem okC6_true : okC6 = true :=
  Certificates.certificate5085.1

theorem finite_cent_six {a1 a2 τ b : Perm (Fin 6)}
    (ha1 : a1 * a1 = 1 ∧ a1 ≠ 1 ∧ sign a1 = 1) (ha2 : a2 * a2 = 1 ∧ a2 ≠ 1 ∧ sign a2 = 1)
    (ha12 : a1 * a2 = a2 * a1 ∧ a1 ≠ a2) (hτ : τ * τ * τ = 1 ∧ τ ≠ 1)
    (hτa : τ * a1 * τ⁻¹ = a2 ∨ τ * a1 * τ⁻¹ = a1 * a2)
    (hτb : τ * a2 * τ⁻¹ = a1 ∨ τ * a2 * τ⁻¹ = a2 ∨ τ * a2 * τ⁻¹ = a1 * a2)
    (hb : sign b = 1) (hbτ : b * τ = τ * b) (hb1 : b ≠ 1) (hbτ1 : b ≠ τ) (hbτ2 : b ≠ τ⁻¹) :
    goodW a1 a2 (b * a2 * b⁻¹ * a1 * a2 * b) = true ∨ goodW a1 a2 (b * a1 * b⁻¹ * a1 * b) = true ∨
      goodW a1 a2 (b * a1 * a2 * b⁻¹ * a2 * b) = true := by
  have h1 : okP6 a1 a2 = true :=
    List.all_eq_true.1 (List.all_eq_true.1 okC6_true a1 (mem_inv6.2 ha1)) a2 (mem_inv6.2 ha2)
  have hC0 : (a1 * a2 = a2 * a1 ∧ a1 ≠ a2) = True := eq_true ha12
  have h1' : ord3six.all (okT6 a1 a2) = true := by
    have h := h1
    simp only [okP6, hC0, ite_true] at h
    exact h
  have h2 : okT6 a1 a2 τ = true := List.all_eq_true.1 h1' τ (mem_ord3six.2 hτ)
  have hC1 : ((τ * a1 * τ⁻¹ = a2 ∨ τ * a1 * τ⁻¹ = a1 * a2) ∧
      (τ * a2 * τ⁻¹ = a1 ∨ τ * a2 * τ⁻¹ = a2 ∨ τ * a2 * τ⁻¹ = a1 * a2)) = True :=
    eq_true ⟨hτa, hτb⟩
  have h2' : even6.all (okB6 a1 a2 τ) = true := by
    have h := h2
    simp only [okT6, hC1, ite_true] at h
    exact h
  have h3 : okB6 a1 a2 τ b = true := List.all_eq_true.1 h2' b (mem_even6.2 hb)
  have hC2 : (b * τ = τ * b ∧ b ≠ 1 ∧ b ≠ τ ∧ b ≠ τ⁻¹) = True := eq_true ⟨hbτ, hb1, hbτ1, hbτ2⟩
  have h4 : (goodW a1 a2 (b * a2 * b⁻¹ * a1 * a2 * b) = true ∨
      goodW a1 a2 (b * a1 * b⁻¹ * a1 * b) = true) ∨
      goodW a1 a2 (b * a1 * a2 * b⁻¹ * a2 * b) = true := by
    have h := h3
    simp only [okB6, hC2, ite_true, Bool.or_eq_true] at h
    exact h
  rcases h4 with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem finite_cent_five_check :
    ((allPerms 5).all fun τ =>
      !(decide (τ * τ * τ = 1 ∧ τ ≠ 1)) ||
        (allPerms 5).all fun b =>
          !(decide (sign b = 1 ∧ b * τ = τ * b)) ||
            decide (b = 1 ∨ b = τ ∨ b = τ⁻¹)) = true :=
  Certificates.certificate5085.2

theorem finite_cent_five
    {τ b : Perm (Fin 5)} (hτ : τ * τ * τ = 1 ∧ τ ≠ 1) (hb : sign b = 1)
    (hbτ : b * τ = τ * b) : b = 1 ∨ b = τ ∨ b = τ⁻¹ := by
  have h1 := List.all_eq_true.1 finite_cent_five_check τ (mem_allPerms 5 τ)
  have h2 : decide (τ * τ * τ = 1 ∧ τ ≠ 1) = true := decide_eq_true hτ
  rw [h2] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  have h3 := List.all_eq_true.1 h1 b (mem_allPerms 5 b)
  have h4 : decide (sign b = 1 ∧ b * τ = τ * b) = true := decide_eq_true ⟨hb, hbτ⟩
  rw [h4] at h3
  simp only [Bool.not_true, Bool.false_or] at h3
  exact of_decide_eq_true h3

end CFSG.GH74.GLS.C3.Prop121
