module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1
public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Three
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier CFSG.Certificates Certificates.Odd87F3 Certificates.Ivk8Weak CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem hhObsAt_of_pair {Y : Type} [Group Y] {p : ℕ} (hp2 : p ≠ 2) {b : MulAut Y} {u v : Y}
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u)
    (hbu : b u = u ∨ b u = v ∨ b u = u * v) (hbv : b v = u ∨ b v = v ∨ b v = u * v)
    (hne : b u ≠ u ∨ b v ≠ v) : HHObsAt p 2 Y b := by
  have hcommS : ∀ x ∈ ({u, v} : Set Y), ∀ y ∈ ({u, v} : Set Y), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact huv
    · exact huv.symm
    · rfl
  have hu' : u ∈ closure ({u, v} : Set Y) := subset_closure (by simp)
  have hv' : v ∈ closure ({u, v} : Set Y) := subset_closure (by simp)
  refine ⟨Nat.prime_two, fun h => hp2 h.symm, closure ({u, v} : Set Y), ?_, ?_, ?_, ?_⟩
  · refine isPGroup_two_closure_of_comm _ ?_ hcommS
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  · intro _ x hx y hy
    have hpair : ({u, v} : Set Y).Pairwise Commute := fun x hx y hy _ => hcommS x hx y hy
    have := Subgroup.isMulCommutative_closure hpair
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : closure ({u, v} : Set Y)) ⟨y, hy⟩)
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rcases hbu with h | h | h
        · rw [h]; exact hu'
        · rw [h]; exact hv'
        · rw [h]; exact Subgroup.mul_mem _ hu' hv'
      · rcases hbv with h | h | h
        · rw [h]; exact hu'
        · rw [h]; exact hv'
        · rw [h]; exact Subgroup.mul_mem _ hu' hv'
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  · rcases hne with h | h
    · exact ⟨u, hu', h⟩
    · exact ⟨v, hv', h⟩

theorem hhObsAt_of_equiv_pair {Y G : Type} [Group Y] [Group G] (e : Y ≃* G) {p : ℕ}
    (hp2 : p ≠ 2) {b : MulAut Y} {y₀ : Y} (hb : b = MulAut.conj y₀) {u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v = v * u)
    (hcu : e y₀ * u * (e y₀)⁻¹ = u ∨ e y₀ * u * (e y₀)⁻¹ = v ∨ e y₀ * u * (e y₀)⁻¹ = u * v)
    (hcv : e y₀ * v * (e y₀)⁻¹ = u ∨ e y₀ * v * (e y₀)⁻¹ = v ∨ e y₀ * v * (e y₀)⁻¹ = u * v)
    (hne : e y₀ * u * (e y₀)⁻¹ ≠ u ∨ e y₀ * v * (e y₀)⁻¹ ≠ v) : HHObsAt p 2 Y b := by
  have hbU : ∀ w : G, b (e.symm w) = e.symm (e y₀ * w * (e y₀)⁻¹) := by
    intro w
    rw [hb, MulAut.conj_apply]
    apply e.injective
    simp
  refine hhObsAt_of_pair hp2 (b := b) (u := e.symm u) (v := e.symm v) ?_ ?_ ?_ ?_ ?_ ?_
  · apply e.injective
    simp [hu]
  · apply e.injective
    simp [hv]
  · apply e.injective
    simp [huv]
  · rw [hbU]
    rcases hcu with h | h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (by rw [h]; simp))
  · rw [hbU]
    rcases hcv with h | h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (by rw [h]; simp))
  · rw [hbU, hbU]
    rcases hne with h | h
    · exact Or.inl fun h' => h (by simpa using congrArg e h')
    · exact Or.inr fun h' => h (by simpa using congrArg e h')

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
