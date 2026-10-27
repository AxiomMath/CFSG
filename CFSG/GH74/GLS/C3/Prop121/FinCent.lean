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
public import CFSG.GH74.GLS.C3.Prop121.FinCentInputs
public meta import CFSG.GH74.GLS.C3.Prop121.FinCentInputs
public import Certificates.Certificate5088

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm

theorem mem_threeCyc {n : ℕ} {c : Perm (Fin n)} : c ∈ threeCyc n ↔ c.support.card = 3 := by
  simp [threeCyc, mem_allPerms]

theorem okCent5 : okCent 5 = true :=
  Certificates.certificate5088.1
theorem okCent6 : okCent 6 = true :=
  Certificates.certificate5088.2.1
theorem okCent7 : okCent 7 = true :=
  Certificates.certificate5088.2.2

theorem okCent_true
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) : okCent n = true := by
  rcases hn with rfl | rfl | rfl
  · exact okCent5
  · exact okCent6
  · exact okCent7

theorem eq_one_of_comm_alt
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7) (ρ : Perm (Fin n))
    (h : ∀ α : Perm (Fin n), sign α = 1 → ρ * α = α * ρ) : ρ = 1 := by
  by_contra hρ
  have h1 := List.all_eq_true.1 (okCent_true hn) ρ (mem_allPerms n ρ)
  have h2 : decide (ρ = 1) = false := decide_eq_false hρ
  rw [h2, Bool.false_or] at h1
  obtain ⟨c, hc, hcρ⟩ := List.any_eq_true.1 h1
  have h3 : sign c = 1 := (card_support_eq_three_iff.1 (mem_threeCyc.1 hc)).sign
  exact of_decide_eq_true hcρ (h c h3)

end CFSG.GH74.GLS.C3.Prop121
