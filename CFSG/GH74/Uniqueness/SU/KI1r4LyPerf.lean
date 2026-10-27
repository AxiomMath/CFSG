module

public import CFSG.GH74.Generic.S45.LAltCore

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.LyPerm

open Equiv Equiv.Perm Subgroup CFSG.GH74.Generic.S45.LAlt
open scoped commutatorElement

theorem exists_fixed_perfect_lift' {K A : Type*} [Group K] [Group A] (y : MulAut K) (π : K →* A)
    (hker : π.ker ≤ Subgroup.center K) (X : Subgroup A) (hXr : X ≤ π.range) (hX : ⁅X, X⁆ = X)
    (hy : ∀ k : K, π k ∈ X → π (y k) = π k) :
    ∃ D : Subgroup K, ⁅D, D⁆ = D ∧ (∀ k ∈ D, π k ∈ X) ∧ (∀ a ∈ X, ∃ k ∈ D, π k = a) ∧
      ∀ k ∈ D, y k = k := by
  let Xt : Subgroup K := X.comap π
  let D : Subgroup K := ⁅Xt, Xt⁆
  have hDle : D ≤ Xt := Subgroup.commutator_le_self Xt
  have hπD : D.map π = X := by
    show (⁅Xt, Xt⁆).map π = X
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq, inf_eq_right.2 hXr, hX]
  have hXt : Xt = D ⊔ π.ker := by
    show X.comap π = _
    rw [← Subgroup.comap_map_eq, hπD]
  have hDperf : ⁅D, D⁆ = D := by
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central D π.ker hker
    rw [← hXt] at h
    exact h.symm
  refine ⟨D, hDperf, fun k hk => hDle hk, fun a ha => ?_,
    fixed_of_perfect y π hker hDperf (fun k hk => hy k (hDle hk))⟩
  have : a ∈ D.map π := hπD ▸ ha
  obtain ⟨k, hk, rfl⟩ := this
  exact ⟨k, hk, rfl⟩

theorem exists_fixed_perfect_order_four_lift {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (π : K →* alternatingGroup (Fin 11)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) (hK2 : IsPGroup 2 π.ker) (hne : π.ker ≠ ⊥)
    (y : MulAut K) (σ : Perm (Fin 11))
    (hy : ∀ k : K, ((π (y k) : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
      σ * (π k : Perm (Fin 11)) * σ⁻¹)
    (hbad : BadCent σ) :
    ∃ D : Subgroup K, ⁅D, D⁆ = D ∧ (∀ k ∈ D, y k = k) ∧ ∃ k ∈ D, 4 ∣ orderOf k := by
  classical
  obtain ⟨-, X, hXle, hXperf, g', hg'X, hg'⟩ := hbad
  let ψ : K →* Perm (Fin 11) := (alternatingGroup (Fin 11)).subtype.comp π
  have hψσ : ∀ k, ψ (y k) = σ * ψ k * σ⁻¹ := fun k => hy k
  have hψker : ψ.ker = π.ker :=
    MonoidHom.ker_comp_of_injective π (alternatingGroup (Fin 11)).subtype
      (alternatingGroup (Fin 11)).subtype_injective
  have hXr : X ≤ ψ.range := by
    intro x hx
    obtain ⟨hxA, -⟩ := mem_centAlt.1 (hXle hx)
    obtain ⟨k, hk⟩ := hπ ⟨x, hxA⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hy' : ∀ k : K, ψ k ∈ X → ψ (y k) = ψ k := by
    intro k hk
    obtain ⟨-, hcomm⟩ := mem_centAlt.1 (hXle hk)
    rw [hψσ k, ← hcomm]
    group
  obtain ⟨D, hDperf, -, hDsurj, hDfix⟩ :=
    exists_fixed_perfect_lift' y ψ (hψker.le.trans hker) X hXr hXperf hy'
  obtain ⟨k, hkD, hk⟩ := hDsurj g' hg'X
  refine ⟨D, hDperf, hDfix, k, hkD, ?_⟩
  rcases hg' with hord | ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hgeq⟩
  · have h1 := orderOf_map_dvd ψ k
    rw [hk, hord] at h1
    exact h1
  · have hx : ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) = swap a b * swap c d := by
      rw [← hgeq, ← hk]
      rfl
    have hsq := sq_ne_one_of_lift_swap_mul_swap (by norm_num) π hπ hker hK2 hne hab hac had hbc hbd hcd hx
    have hker2 : Nat.card π.ker ≤ 2 :=
      CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
        (by norm_num) π hπ hker hK2
    have hnd : [a, b, c, d].Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
    have hswsq : (swap a b * swap c d) ^ 2 = 1 := by
      have hc := (Equiv.Perm.disjoint_swap_swap hnd).commute
      rw [hc.mul_pow, pow_two, pow_two, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
    have hk2ker : k ^ 2 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      apply Subtype.ext
      rw [Subgroup.coe_pow, hx, hswsq]
      rfl
    have hk4 : (k ^ 2) ^ 2 = 1 :=
      congrArg Subtype.val (sq_eq_one_of_card_le_two hker2 (⟨k ^ 2, hk2ker⟩ : π.ker))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf k = 4 := by
      have h1 : ¬ k ^ 2 ^ 1 = 1 := by simpa using hsq
      have h2 : k ^ 2 ^ (1 + 1) = 1 := by
        rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul]
        exact hk4
      simpa using orderOf_eq_prime_pow h1 h2
    rw [hord]

end CFSG.GH74.Uniqueness.SU.K.R4.LyPerm
