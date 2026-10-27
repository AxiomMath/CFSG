module

public import CFSG.GH74.GLS.Prop27.LocBal

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier

section Generic

variable {K : Type} [Group K] {G : Type} [Group G]

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := MulEquiv.orderOf_eq (MulAut.conj g) x
  simpa [MulAut.conj_apply] using h

theorem conj_comm_iff (g x r : G) :
    x * (g * r * g⁻¹) = (g * r * g⁻¹) * x ↔ (g⁻¹ * x * g) * r = r * (g⁻¹ * x * g) := by
  constructor
  · intro h
    have h1 : g⁻¹ * (x * (g * r * g⁻¹)) * g = g⁻¹ * ((g * r * g⁻¹) * x) * g := by rw [h]
    calc g⁻¹ * x * g * r = g⁻¹ * (x * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * x) * g := h1
      _ = r * (g⁻¹ * x * g) := by group
  · intro h
    have h1 : g * ((g⁻¹ * x * g) * r) * g⁻¹ = g * (r * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    calc x * (g * r * g⁻¹) = g * ((g⁻¹ * x * g) * r) * g⁻¹ := by group
      _ = g * (r * (g⁻¹ * x * g)) * g⁻¹ := h1
      _ = (g * r * g⁻¹) * x := by group

end Generic

section Check

variable {n : ℕ}

theorem oddCoreAt_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) (hPA : QP.originalSubgroup ≤ QA.originalSubgroup) {a m : ℕ}
    (hm : Odd m) (hcard : Nat.card QA.originalSubgroup = 2 ^ a * m) {τ : Equiv.Perm (Fin n)}
    (h : oddCoreAt m ((elemsT QA).filter fun g => decide (g * τ = τ * g))
      ((elemsT QP).filter fun c => decide (c * τ = τ * c)) = true) :
    ∀ x ∈ QA.originalSubgroup, x * τ = τ * x → x ≠ 1 → Odd (orderOf x) →
      ∃ c ∈ QP.originalSubgroup, c * τ = τ * c ∧ Even (orderOf (x * c * x⁻¹ * c⁻¹)) := by
  intro x hx hxτ hx1 hxodd
  have hpow : x ^ m = 1 := (odd_orderOf_iff_pow_eq_one _ hm hcard hx).mp hxodd
  have h2 := List.all_eq_true.1 h x (by
    rw [List.mem_filter]
    exact ⟨(mem_elemsT QA hQA x).2 hx, by simpa using hxτ⟩)
  have h3 := (bif_imp _ _).1 h2 (by simp [hx1, hpow])
  obtain ⟨c, hc, hc'⟩ := List.any_eq_true.1 h3
  rw [List.mem_filter] at hc
  have hcP : c ∈ QP.originalSubgroup := (mem_elemsT QP hQP c).1 hc.1
  have hcτ : c * τ = τ * c := by simpa using hc.2
  refine ⟨c, hcP, hcτ, ?_⟩
  have hy : x * c * x⁻¹ * c⁻¹ ∈ QA.originalSubgroup :=
    QA.originalSubgroup.mul_mem (QA.originalSubgroup.mul_mem (QA.originalSubgroup.mul_mem hx
      (hPA hcP)) (QA.originalSubgroup.inv_mem hx)) (QA.originalSubgroup.inv_mem (hPA hcP))
  have hne : (x * c * x⁻¹ * c⁻¹) ^ m ≠ 1 := by simpa using hc'
  exact Nat.not_odd_iff_even.mp fun hodd =>
    hne ((odd_orderOf_iff_pow_eq_one _ hm hcard hy).mp hodd)

end Check

end CFSG.GH74.GLS.Prop27
