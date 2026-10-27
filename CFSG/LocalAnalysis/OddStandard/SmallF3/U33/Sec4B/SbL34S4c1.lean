module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type*} [Group G]

theorem comm_cent_of_stab (Q : Subgroup G) (a b : G)
    (haZ : ∀ z ∈ Q ⊓ centralizer (Q : Set G), a * z * a⁻¹ = z)
    (hbZ : ∀ z ∈ Q ⊓ centralizer (Q : Set G), b * z * b⁻¹ = z)
    (ha : ∀ x ∈ Q, x⁻¹ * (a * x * a⁻¹) ∈ Q ⊓ centralizer (Q : Set G))
    (hb : ∀ x ∈ Q, x⁻¹ * (b * x * b⁻¹) ∈ Q ⊓ centralizer (Q : Set G)) :
    ∀ x ∈ Q, (a⁻¹ * b⁻¹ * a * b) * x = x * (a⁻¹ * b⁻¹ * a * b) := by
  intro x hx
  obtain ⟨za, hza, hxa⟩ :
      ∃ za ∈ Q ⊓ centralizer (Q : Set G), a * x * a⁻¹ = x * za :=
    ⟨x⁻¹ * (a * x * a⁻¹), ha x hx, by group⟩
  obtain ⟨zb, hzb, hxb⟩ :
      ∃ zb ∈ Q ⊓ centralizer (Q : Set G), b * x * b⁻¹ = x * zb :=
    ⟨x⁻¹ * (b * x * b⁻¹), hb x hx, by group⟩
  have hZc : ∀ c ∈ Q ⊓ centralizer (Q : Set G),
      ∀ c' ∈ Q ⊓ centralizer (Q : Set G), c * c' = c' * c := by
    intro c hc c' hc'
    exact (Subgroup.mem_centralizer_iff.mp hc.2 c' hc'.1).symm
  have hAB : (a * b) * x * (a * b)⁻¹ = (b * a) * x * (b * a)⁻¹ := by
    calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = (a * x * a⁻¹) * (a * zb * a⁻¹) := by rw [hxb]; group
      _ = (x * za) * zb := by rw [hxa, haZ zb hzb]
      _ = (x * zb) * za := by rw [mul_assoc, hZc za hza zb hzb, ← mul_assoc]
      _ = (b * a) * x * (b * a)⁻¹ := by
        rw [show (b * a) * x * (b * a)⁻¹ = b * (a * x * a⁻¹) * b⁻¹ by group,
          hxa, show b * (x * za) * b⁻¹ = (b * x * b⁻¹) * (b * za * b⁻¹) by group,
          hxb, hbZ za hza]
  have huxu : (a⁻¹ * b⁻¹ * a * b) * x * (a⁻¹ * b⁻¹ * a * b)⁻¹ = x := by
    calc (a⁻¹ * b⁻¹ * a * b) * x * (a⁻¹ * b⁻¹ * a * b)⁻¹
        = a⁻¹ * b⁻¹ * ((a * b) * x * (a * b)⁻¹) * (b * a) := by group
      _ = a⁻¹ * b⁻¹ * ((b * a) * x * (b * a)⁻¹) * (b * a) := by rw [hAB]
      _ = x := by group
  calc (a⁻¹ * b⁻¹ * a * b) * x
      = ((a⁻¹ * b⁻¹ * a * b) * x * (a⁻¹ * b⁻¹ * a * b)⁻¹) * (a⁻¹ * b⁻¹ * a * b) := by
        group
    _ = x * (a⁻¹ * b⁻¹ * a * b) := by rw [huxu]

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
