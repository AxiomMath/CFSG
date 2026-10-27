module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.ComponentClassification.SolMax

open Subgroup

variable {X : Type*} [Group X]

theorem eq_zpowers_of_split {Q : Subgroup X} {t s q m : X} (htQ : t ∈ Q)
    (htZ : ∀ y ∈ Q, y * t = t * y) (hqQ : q ∈ Q) (hm : ∀ y ∈ Q, y * m = m * y)
    (hs : s = q * m) (hC : Q ⊓ centralizer ({s} : Set X) ≤ zpowers t) : Q = zpowers t := by
  have hcomm : ∀ y ∈ Q, y * q = q * y → y ∈ Q ⊓ centralizer ({s} : Set X) := by
    intro y hy hyq
    refine mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hs, ← mul_assoc, hyq, mul_assoc, hm y hy, mul_assoc]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hC (hcomm q hqQ rfl))
  have hqZ : ∀ y ∈ Q, y * q = q * y := by
    intro y hy
    rw [← hk]
    exact (Commute.zpow_right (htZ y hy) k).eq
  exact le_antisymm (fun y hy => hC (hcomm y hy (hqZ y hy))) (zpowers_le.mpr htQ)

theorem eq_zpowers_of_split_of_center {M Q S : Subgroup X} {t s : X} (htQ : t ∈ Q)
    (hQS : Q ≤ S) (htZ : ∀ y ∈ S, y * t = t * y)
    (hsplit : ∃ q ∈ Q, ∃ m ∈ S, m ∈ M ∧ (∀ y ∈ Q, y * m = m * y) ∧ s = q * m)
    (hC : Q ⊓ centralizer ({s} : Set X) ≤ zpowers t) : Q = zpowers t := by
  obtain ⟨q, hqQ, m, -, -, hm, hs⟩ := hsplit
  exact eq_zpowers_of_split htQ (fun y hy => htZ y (hQS hy)) hqQ hm hs hC

end CFSG.ComponentClassification.SolMax
