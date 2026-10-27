module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm

private theorem exists_ne_ne {m : ℕ} (hm : 3 ≤ m) (a b : Fin m) :
    ∃ c : Fin m, c ≠ a ∧ c ≠ b := by
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b} : Finset (Fin m))) (t := Finset.univ)
    (Finset.card_le_two.trans_lt (by rw [Finset.card_univ, Fintype.card_fin]; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc⟩

theorem perm_center_trivial {m : ℕ} (hm : 3 ≤ m) (π : Perm (Fin m))
    (h : ∀ σ : Perm (Fin m), π * σ = σ * π) : π = 1 := by
  refine Equiv.ext fun x => ?_
  rw [Perm.one_apply]
  by_contra hx
  obtain ⟨z, hzx, hzy⟩ := exists_ne_ne hm x (π x)
  have hc := congrArg (fun f : Perm (Fin m) => f x) (h (swap x z))
  simp only [Perm.mul_apply, swap_apply_left] at hc
  rw [swap_apply_of_ne_of_ne hx hzy.symm] at hc
  exact hzx (π.injective hc)

theorem perm_aut_inner {m : ℕ} (hm : 7 ≤ m) (α : MulAut (Perm (Fin m))) :
    ∃ π : Perm (Fin m), ∀ σ : Perm (Fin m), α σ = π * σ * π⁻¹ := by
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m
    (by omega) (by omega)).2 (MulAut.characteristic (alternatingGroup (Fin m)) α)
  have hA : ∀ a ∈ alternatingGroup (Fin m), α a = π * a * π⁻¹ := by
    intro a ha
    have := congrArg (fun f : MulAut (alternatingGroup (Fin m)) =>
      ((f ⟨a, ha⟩ : alternatingGroup (Fin m)) : Perm (Fin m))) hπ
    simpa [MulAut.conjNormal_apply] using this.symm
  refine ⟨π, fun σ => ?_⟩
  have hy : (π * σ)⁻¹ * α σ * π = 1 := by
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup m (by omega)
    rw [map_one]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hmem : σ * a * σ⁻¹ ∈ alternatingGroup (Fin m) :=
      (alternatingGroup (Fin m)).normal_of_characteristic.conj_mem _ a.2 σ
    have key : α σ * (π * a * π⁻¹) * (α σ)⁻¹ = π * (σ * a * σ⁻¹) * π⁻¹ := by
      rw [← hA a a.2, ← map_inv, ← map_mul, ← map_mul]
      exact hA _ hmem
    calc (π * σ)⁻¹ * α σ * π * a * ((π * σ)⁻¹ * α σ * π)⁻¹
      _ = (π * σ)⁻¹ * (α σ * (π * a * π⁻¹) * (α σ)⁻¹) * (π * σ) := by group
      _ = (π * σ)⁻¹ * (π * (σ * a * σ⁻¹) * π⁻¹) * (π * σ) := by rw [key]
      _ = a := by group
  calc α σ
    _ = (π * σ) * ((π * σ)⁻¹ * α σ * π) * π⁻¹ := by group
    _ = π * σ * π⁻¹ := by rw [hy, mul_one]

theorem exists_swap_commute_of_sq_eq_one {m : ℕ} (hm : 2 ≤ m) (π : Perm (Fin m))
    (h : π * π = 1) : ∃ σ : Perm (Fin m), σ.IsSwap ∧ π * σ = σ * π := by
  by_cases h1 : π = 1
  · refine ⟨swap ⟨0, by omega⟩ ⟨1, by omega⟩, ⟨_, _, by simp, rfl⟩, ?_⟩
    rw [h1, one_mul, mul_one]
  · obtain ⟨x, hx⟩ : ∃ x, π x ≠ x := by
      by_contra hne
      push Not at hne
      exact h1 (Equiv.ext hne)
    have hππ : π (π x) = x := by
      simpa using congrArg (fun f : Perm (Fin m) => f x) h
    refine ⟨swap x (π x), ⟨x, π x, hx.symm, rfl⟩, ?_⟩
    rw [mul_swap_eq_swap_mul, hππ, swap_comm]

theorem injective_of_threeCycle {m : ℕ} (hm : 5 ≤ m) {H : Type*} [Group H]
    (ψ : Perm (Fin m) →* H) {c : Perm (Fin m)} (hc : c.IsThreeCycle) (h1 : ψ c ≠ 1) :
    Function.Injective ψ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hK
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin m) (by simpa using hm)
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hK)
  exact h1 (MonoidHom.mem_ker.mp (hle hc.mem_alternatingGroup))

end CFSG.EvenSmallLie.OddTranspAlt
