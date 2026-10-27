module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup

theorem conj_twist_eq {Y : Type} [Group Y] (α : MulAut Y) (y g : Y) :
    MulAut.conj y * (MulAut.conj g * α) * (MulAut.conj y)⁻¹ =
      MulAut.conj (y * g * (α y)⁻¹) * α := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

theorem exists_twisted_mem_of_index_not_dvd {Y : Type} [Group Y] [Finite Y] (α : MulAut Y)
    (hα : ∀ y, α (α (α y)) = y) (N : Subgroup Y) (hN : ∀ n ∈ N, α n ∈ N)
    (hidx : ¬ 3 ∣ N.index) (g : Y) (hg : g * α g * α (α g) = 1) :
    ∃ z : Y, z⁻¹ * g * α z ∈ N := by
  classical
  let T : Y ⧸ N → Y ⧸ N := Quotient.lift (fun z => (QuotientGroup.mk (g * α z) : Y ⧸ N))
    (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
      apply QuotientGroup.eq.2
      have : (g * α a)⁻¹ * (g * α b) = α (a⁻¹ * b) := by simp [map_mul, map_inv, mul_assoc]
      rw [this]
      exact hN _ hab')
  have hT3 : ∀ x : Y ⧸ N, T (T (T x)) = x := by
    intro x
    induction x using Quotient.inductionOn with
    | h z =>
      change (QuotientGroup.mk (g * α (g * α (g * α z))) : Y ⧸ N) = QuotientGroup.mk z
      have : g * α (g * α (g * α z)) = (g * α g * α (α g)) * z := by
        simp only [map_mul, hα, mul_assoc]
      rw [this, hg, one_mul]
  let Tσ : Equiv.Perm (Y ⧸ N) :=
    { toFun := T, invFun := fun x => T (T x), left_inv := fun x => hT3 x,
      right_inv := fun x => hT3 x }
  have hTσ3 : Tσ ^ 3 = 1 := by
    ext x
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.coe_mul, Function.comp_apply]
    exact hT3 x
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers Tσ) := by
    rintro ⟨g', k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one]
    change ((Tσ ^ k) ^ 3 : Equiv.Perm (Y ⧸ N)) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hTσ3, one_zpow]
  have hcard : ¬ 3 ∣ Nat.card (Y ⧸ N) := by
    rw [← Subgroup.index]
    exact hidx
  obtain ⟨x, hx⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card (Y ⧸ N) hcard
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 := hx ⟨Tσ, Subgroup.mem_zpowers Tσ⟩
  change T (QuotientGroup.mk z) = QuotientGroup.mk z at h1
  change (QuotientGroup.mk (g * α z) : Y ⧸ N) = QuotientGroup.mk z at h1
  refine ⟨z, ?_⟩
  have := QuotientGroup.eq.1 h1
  have h2 := inv_mem this
  simpa [mul_assoc] using h2

theorem exists_conj_mem_of_index_not_dvd {Y : Type} [Group Y] [Finite Y] (α : MulAut Y)
    (hα : ∀ y, α (α (α y)) = y) (N : Subgroup Y) (hN : ∀ n ∈ N, α n ∈ N)
    (hidx : ¬ 3 ∣ N.index) (g : Y) (hg : g * α g * α (α g) = 1) :
    ∃ y n : Y, n ∈ N ∧
      MulAut.conj y * (MulAut.conj g * α) * (MulAut.conj y)⁻¹ = MulAut.conj n * α := by
  obtain ⟨z, hz⟩ := exists_twisted_mem_of_index_not_dvd α hα N hN hidx g hg
  refine ⟨z⁻¹, z⁻¹ * g * α z, hz, ?_⟩
  rw [conj_twist_eq]
  simp

end CFSG.GH74.GLS.Stage2.Bender.Thm1
