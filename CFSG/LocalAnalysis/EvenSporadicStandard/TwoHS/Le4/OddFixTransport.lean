module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Defs
import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

@[expose] def OddFixAt (Y : Type*) [Group Y] (z : Y) : Prop :=
  ∀ φ : MulAut Y, (∀ x ∈ centralizer ({z} : Set Y), Odd (orderOf x) → φ x = x) → φ ^ 4 = 1

theorem OddFixAt.of_mulEquiv {Y H : Type*} [Group Y] [Group H] (ε : Y ≃* H) {z : Y}
    (h : OddFixAt H (ε z)) : OddFixAt Y z := by
  have hc : ∀ x : Y, x ∈ centralizer ({z} : Set Y) ↔ ε x ∈ centralizer ({ε z} : Set H) := by
    intro x
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact ε.injective.eq_iff.symm
  have hψ : ∀ (φ : MulAut Y) (x : Y), (MulAut.congr ε φ) (ε x) = ε (φ x) := by
    intro φ x
    simp [MulAut.congr_apply]
  intro φ hφ
  have h4 := h (MulAut.congr ε φ) (fun y hy hodd => by
    obtain ⟨x, rfl⟩ := ε.surjective y
    rw [hψ, hφ x ((hc x).2 hy) (by rwa [MulEquiv.orderOf_eq] at hodd)])
  rw [← map_pow] at h4
  exact (map_eq_one_iff _ (MulEquiv.injective _)).1 h4

theorem OddFixAt.conj {H : Type*} [Group H] {z : H} (h : OddFixAt H z) (g : H) :
    OddFixAt H (g * z * g⁻¹) := by
  refine OddFixAt.of_mulEquiv (MulAut.conj g⁻¹) ?_
  have : (MulAut.conj g⁻¹) (g * z * g⁻¹) = z := by simp; group
  rwa [this]

theorem OddFixFourth.of_mulEquiv {Y H : Type*} [Group Y] [Group H] (ε : Y ≃* H)
    (h : OddFixFourth H) : OddFixFourth Y := fun z hz =>
  OddFixAt.of_mulEquiv ε (h (ε z) (by rwa [MulEquiv.orderOf_eq]))

end CFSG.EvenSporadicStandard.TwoHS
