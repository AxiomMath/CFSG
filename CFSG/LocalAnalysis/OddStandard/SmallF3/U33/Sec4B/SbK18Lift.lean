module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G]

private lemma conj_conj {u : G} (hu2 : u * u = 1) (x : G) :
    u * (u * x * u⁻¹) * u⁻¹ = x := by
  have h1 : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, hu2, inv_one]
  calc u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) := by group
    _ = x := by rw [hu2, h1, one_mul, mul_one]

private lemma conj_mul_free {u a b : G} (hu2 : u * u = 1) :
    u * (a * (u * b * u⁻¹)) * u⁻¹ = (u * a * u⁻¹) * b := by
  calc u * (a * (u * b * u⁻¹)) * u⁻¹
      = (u * a * u⁻¹) * (u * (u * b * u⁻¹) * u⁻¹) := by group
    _ = (u * a * u⁻¹) * b := by rw [conj_conj hu2 b]

private lemma mul_four_comm {Q : Subgroup G}
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) {A B C D : G}
    (hA : A ∈ Q) (hB : B ∈ Q) (hC : C ∈ Q) (hD : D ∈ Q) :
    A * B * C * D = A * D * C * B := by
  have hBD : Commute B D := hQab B hB D hD
  have hCD : Commute C D := hQab C hC D hD
  have hBC : Commute B C := hQab B hB C hC
  calc A * B * C * D = A * B * (C * D) := by rw [mul_assoc]
    _ = A * B * (D * C) := by rw [hCD.eq]
    _ = A * D * (B * C) := by rw [Commute.mul_mul_mul_comm hBD A C]
    _ = A * D * (C * B) := by rw [hBC.eq]
    _ = A * D * C * B := by group

theorem exists_fixed_mul_of_free {Q A₀ : Subgroup G} {u n : G} (hu2 : u * u = 1)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hA₀ : A₀ ≤ Q)
    (huQ : ∀ q ∈ Q, u * q * u⁻¹ ∈ Q)
    (hdec : ∀ q ∈ Q, ∃ a ∈ A₀, ∃ b ∈ A₀, q = a * (u * b * u⁻¹))
    (hfree : ∀ a ∈ A₀, ∀ b ∈ A₀, a * (u * b * u⁻¹) = 1 → a = 1)
    (hn : n⁻¹ * (u * n * u⁻¹) ∈ Q) :
    ∃ q ∈ Q, u * (n * q) * u⁻¹ = n * q := by
  have hconj_n : u * (u * n * u⁻¹) * u⁻¹ = n := conj_conj hu2 n
  have hstep : u * (n⁻¹ * (u * n * u⁻¹)) * u⁻¹ = (u * n * u⁻¹)⁻¹ * n := by
    calc u * (n⁻¹ * (u * n * u⁻¹)) * u⁻¹
        = (u * n⁻¹ * u⁻¹) * (u * (u * n * u⁻¹) * u⁻¹) := by group
      _ = (u * n * u⁻¹)⁻¹ * n := by
            rw [show u * n⁻¹ * u⁻¹ = (u * n * u⁻¹)⁻¹ by group, hconj_n]
  have hcomm : (n⁻¹ * (u * n * u⁻¹)) * (u * (n⁻¹ * (u * n * u⁻¹)) * u⁻¹) = 1 := by
    rw [hstep]
    group
  obtain ⟨a, haA, b, hbA, hdec0⟩ := hdec (n⁻¹ * (u * n * u⁻¹)) hn
  have haQ : a ∈ Q := hA₀ haA
  have hbQ : b ∈ Q := hA₀ hbA
  have hBu : u * b * u⁻¹ ∈ Q := huQ b hbQ
  have hAu : u * a * u⁻¹ ∈ Q := huQ a haQ
  have hcomm' : (a * (u * b * u⁻¹)) * (u * (a * (u * b * u⁻¹)) * u⁻¹) = 1 := by
    rw [← hdec0]
    exact hcomm
  have hcomm'' : (a * (u * b * u⁻¹)) * ((u * a * u⁻¹) * b) = 1 := by
    rw [← conj_mul_free hu2]
    exact hcomm'
  have hE1 : a * (u * b * u⁻¹) * (u * a * u⁻¹) * b = 1 := by
    rw [mul_assoc]
    exact hcomm''
  have hprod : (a * b) * (u * (a * b) * u⁻¹) = 1 := by
    have huv : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
    rw [huv]
    calc (a * b) * ((u * a * u⁻¹) * (u * b * u⁻¹))
        = a * b * (u * a * u⁻¹) * (u * b * u⁻¹) := by group
      _ = a * (u * b * u⁻¹) * (u * a * u⁻¹) * b :=
            (mul_four_comm hQab haQ hBu hAu hbQ).symm
      _ = 1 := hE1
  have hab1 : a * b = 1 := by
    apply hfree (a * b) (A₀.mul_mem haA hbA) (a * b) (A₀.mul_mem haA hbA)
    exact hprod
  have hb_eq : b = a⁻¹ := by
    calc b = a⁻¹ * (a * b) := by group
      _ = a⁻¹ * 1 := by rw [hab1]
      _ = a⁻¹ := by group
  have hBC : (u * b * u⁻¹) * (u * a * u⁻¹) = 1 := by
    rw [hb_eq]
    group
  refine ⟨a, haQ, ?_⟩
  calc u * (n * a) * u⁻¹
      = (u * n * u⁻¹) * (u * a * u⁻¹) := by group
    _ = n * (n⁻¹ * (u * n * u⁻¹)) * (u * a * u⁻¹) := by group
    _ = n * (a * (u * b * u⁻¹)) * (u * a * u⁻¹) := by rw [hdec0]
    _ = n * a * ((u * b * u⁻¹) * (u * a * u⁻¹)) := by group
    _ = n * a * 1 := by rw [hBC]
    _ = n * a := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
