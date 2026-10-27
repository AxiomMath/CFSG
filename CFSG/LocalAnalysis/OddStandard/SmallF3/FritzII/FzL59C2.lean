module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C1

import Mathlib.Algebra.Group.Commute.Basic

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G]

theorem fzl59c_sup_comm {P Q : Subgroup G} (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hPQ : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) :
    ∀ x ∈ P ⊔ Q, ∀ y ∈ P ⊔ Q, x * y = y * x := by
  have h1 : ∀ y ∈ P, ∀ x ∈ P ⊔ Q, x * y = y * x := by
    intro y hy x hx
    have h : P ⊔ Q ≤ centralizer ({y} : Set G) := by
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact hP u hu y hy
      · rw [mem_centralizer_singleton_iff]
        exact (hPQ y hy u hu).symm
    exact mem_centralizer_singleton_iff.mp (h hx)
  have h2 : ∀ y ∈ Q, ∀ x ∈ P ⊔ Q, x * y = y * x := by
    intro y hy x hx
    have h : P ⊔ Q ≤ centralizer ({y} : Set G) := by
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact hPQ u hu y hy
      · rw [mem_centralizer_singleton_iff]
        exact hQ u hu y hy
    exact mem_centralizer_singleton_iff.mp (h hx)
  intro x hx y hy
  have h : P ⊔ Q ≤ centralizer ({x} : Set G) := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact (h1 u hu x hx).symm
    · rw [mem_centralizer_singleton_iff]
      exact (h2 u hu x hx).symm
  exact (mem_centralizer_singleton_iff.mp (h hy)).symm

theorem fzl59c_zpowers_comm {P : Subgroup G} {a : G} (hc : ∀ x ∈ P, x * a = a * x) :
    ∀ x ∈ P, ∀ y ∈ zpowers a, x * y = y * x := by
  intro x hx y hy
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  exact (Commute.zpow_right (hc x hx) n).eq

theorem fzl59c_zpowers_self_comm (a : G) : ∀ x ∈ zpowers a, ∀ y ∈ zpowers a, x * y = y * x := by
  intro x hx y hy
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow_self a m n).eq

structure fzl59c_Abs (Z : Subgroup G) (s t : G) : Prop where
  Z_comm : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z
  Z_sq : ∀ z ∈ Z, z ^ 2 = 1
  card_Z : Nat.card ↥Z = 4
  s_sq : s ^ 2 = 1
  t_sq : t ^ 2 = 1
  s_comm : ∀ z ∈ Z, s * z = z * s
  t_comm : ∀ z ∈ Z, t * z = z * t
  st_comm : s * t = t * s
  s_not : s ∉ Z
  t_not : t ∉ Z ⊔ zpowers s

section Chain

variable {Z : Subgroup G} {s t : G} (hA : fzl59c_Abs Z s t)
include hA

theorem fzl59c_B_comm_Z {x z : G} (hx : x ∈ Z ⊔ zpowers s) (hz : z ∈ Z) : x * z = z * x := by
  have h : Z ⊔ zpowers s ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun y hy => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]
      exact hA.Z_comm y hy z hz
    · rw [mem_centralizer_singleton_iff]
      exact hA.s_comm z hz
  exact mem_centralizer_singleton_iff.mp (h hx)

theorem fzl59c_B_comm_t {x : G} (hx : x ∈ Z ⊔ zpowers s) : x * t = t * x := by
  have h : Z ⊔ zpowers s ≤ centralizer ({t} : Set G) := by
    refine sup_le (fun y hy => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]
      exact (hA.t_comm y hy).symm
    · rw [mem_centralizer_singleton_iff]
      exact hA.st_comm
  exact mem_centralizer_singleton_iff.mp (h hx)

theorem fzl59c_B_comm : ∀ x ∈ Z ⊔ zpowers s, ∀ y ∈ Z ⊔ zpowers s, x * y = y * x :=
  fzl59c_sup_comm hA.Z_comm (fzl59c_zpowers_self_comm s)
    (fzl59c_zpowers_comm fun x hx => (hA.s_comm x hx).symm)

theorem fzl59c_F_comm : ∀ x ∈ (Z ⊔ zpowers s) ⊔ zpowers t, ∀ y ∈ (Z ⊔ zpowers s) ⊔ zpowers t,
    x * y = y * x :=
  fzl59c_sup_comm (fzl59c_B_comm hA) (fzl59c_zpowers_self_comm t)
    (fzl59c_zpowers_comm fun _ hx => fzl59c_B_comm_t hA hx)

theorem fzl59c_B_sq {x : G} (hx : x ∈ Z ⊔ zpowers s) : x ^ 2 = 1 := by
  rcases fzl59c_mem_sup_zpowers (fun h hh => hA.s_comm h hh)
      (by rw [hA.s_sq]; exact one_mem _) hx with hx | ⟨h, hh, rfl⟩
  · exact hA.Z_sq x hx
  · have hc : Commute h s := (hA.s_comm h hh).symm
    rw [hc.mul_pow, hA.Z_sq h hh, hA.s_sq, one_mul]

theorem fzl59c_F_sq {x : G} (hx : x ∈ (Z ⊔ zpowers s) ⊔ zpowers t) : x ^ 2 = 1 := by
  rcases fzl59c_mem_sup_zpowers (fun h hh => (fzl59c_B_comm_t hA hh).symm)
      (by rw [hA.t_sq]; exact one_mem _) hx with hx | ⟨h, hh, rfl⟩
  · exact fzl59c_B_sq hA hx
  · have hc : Commute h t := fzl59c_B_comm_t hA hh
    rw [hc.mul_pow, fzl59c_B_sq hA hh, hA.t_sq, one_mul]

theorem fzl59c_card_B [Finite G] : Nat.card ↥(Z ⊔ zpowers s) = 8 := by
  rw [fzl59c_card_sup_zpowers (fun h hh => hA.s_comm h hh)
    (by rw [hA.s_sq]; exact one_mem _) hA.s_not, hA.card_Z]

theorem fzl59c_card_F [Finite G] : Nat.card ↥((Z ⊔ zpowers s) ⊔ zpowers t) = 16 := by
  rw [fzl59c_card_sup_zpowers (fun h hh => (fzl59c_B_comm_t hA hh).symm)
    (by rw [hA.t_sq]; exact one_mem _) hA.t_not, fzl59c_card_B hA]

end Chain

end CFSG.OddStandard.SmallF3.FritzII
