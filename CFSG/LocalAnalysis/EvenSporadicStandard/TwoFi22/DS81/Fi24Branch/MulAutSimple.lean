module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.MulAutSimple

open Subgroup
open scoped commutatorElement

variable {U : Type*} [Group U]

@[expose] def inn (U : Type*) [Group U] : Subgroup (MulAut U) :=
  (MulAut.conj : U →* MulAut U).range

theorem conj_mem_inn (u : U) : (MulAut.conj u : MulAut U) ∈ inn U := ⟨u, rfl⟩

theorem mul_conj_mul_inv (φ : MulAut U) (u : U) :
    φ * MulAut.conj u * φ⁻¹ = MulAut.conj (φ u) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, MulAut.apply_inv_self, map_inv]

theorem center_eq_bot [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a) :
    Subgroup.center U = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center U := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem commutator_eq_top [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a) :
    commutator U = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator U) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hc : ⁅a, b⁆ ∈ commutator U := Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hab hc
  · exact h

theorem conj_injective [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : U →* MulAut U) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ Subgroup.center U := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut U => φ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  rw [center_eq_bot hna] at hmem
  exact Subgroup.mem_bot.mp hmem

instance inn_normal : (inn U).Normal where
  conj_mem := by
    rintro _ ⟨u, rfl⟩ φ
    exact ⟨φ u, (mul_conj_mul_inv φ u).symm⟩

noncomputable def innEquiv [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a) : U ≃* inn U :=
  MonoidHom.ofInjective (conj_injective hna)

theorem natCard_inn [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a) :
    Nat.card (inn U) = Nat.card U :=
  (Nat.card_congr (innEquiv hna).toEquiv).symm

theorem centralizer_inn_eq_bot [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a) :
    Subgroup.centralizer (inn U : Set (MulAut U)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_bot]
  have hc : ∀ u : U, MulAut.conj u * φ = φ * MulAut.conj u := fun u =>
    Subgroup.mem_centralizer_iff.mp hφ _ (conj_mem_inn u)
  ext u
  have h1 : MulAut.conj (φ u) = (MulAut.conj u : MulAut U) := by
    rw [← mul_conj_mul_inv φ u, ← hc u]
    group
  have h2 : φ u = u := conj_injective hna h1
  simpa using h2

theorem center_mulAut_eq_bot [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a) :
    Subgroup.center (MulAut U) = ⊥ := by
  rw [eq_bot_iff, ← centralizer_inn_eq_bot hna]
  intro φ hφ
  rw [Subgroup.mem_centralizer_iff]
  intro h _
  exact (Subgroup.mem_center_iff.mp hφ h)

theorem inn_le_of_normal [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a)
    (N : Subgroup (MulAut U)) [hN : N.Normal] (hbot : N ≠ ⊥) : inn U ≤ N := by
  have hM : ((N.comap (MulAut.conj : U →* MulAut U))).Normal := hN.comap _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MulAut.conj : U →* MulAut U)) with
    h | h
  · exfalso
    apply hbot
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    have hu : ∀ u : U, n u = u := by
      intro u
      have hc : ⁅n, MulAut.conj u⁆ ∈ N := by
        have h1 : n * (MulAut.conj u * n⁻¹ * (MulAut.conj u)⁻¹) ∈ N :=
          N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) _)
        simpa [commutatorElement_def, mul_assoc] using h1
      have h2 : ⁅n, MulAut.conj u⁆ = MulAut.conj (n u * u⁻¹) := by
        rw [commutatorElement_def, mul_assoc, map_mul, map_inv, ← mul_conj_mul_inv n u]
        group
      rw [h2] at hc
      have h3 : n u * u⁻¹ ∈ N.comap (MulAut.conj : U →* MulAut U) := hc
      rw [h, Subgroup.mem_bot] at h3
      exact mul_inv_eq_one.mp h3
    ext u
    exact hu u
  · intro φ hφ
    obtain ⟨u, rfl⟩ := hφ
    have : u ∈ N.comap (MulAut.conj : U →* MulAut U) := by rw [h]; exact mem_top u
    exact this

theorem not_isSolvable [IsSimpleGroup U] (hna : ∃ a b : U, a * b ≠ b * a) :
    ¬ Group.IsSolvable (MulAut U) := by
  intro hA
  have hU : Group.IsSolvable U :=
    Group.isSolvable_of_isSolvable_injective (conj_injective hna)
  obtain ⟨a, b, hab⟩ := hna
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hU a b)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.MulAutSimple
