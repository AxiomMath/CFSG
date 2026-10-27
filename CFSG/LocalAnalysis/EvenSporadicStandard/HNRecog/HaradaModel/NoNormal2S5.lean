module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

theorem perm5_exists_conj (σ : Equiv.Perm (Fin 5)) (h : σ ≠ 1) :
    ∃ g : Equiv.Perm (Fin 5), ((g * σ * g⁻¹) * σ) ^ 8 ≠ 1 := by
  revert σ
  decide +kernel

theorem eq_bot_of_normal_isPGroup_perm5 (P : Subgroup (Equiv.Perm (Fin 5)))
    (hP : IsPGroup 2 P) (hN : P.Normal) : P = ⊥ := by
  by_contra hne
  obtain ⟨σ, hσne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hσne' : (σ : Equiv.Perm (Fin 5)) ≠ 1 := fun h => hσne (Subtype.ext h)
  obtain ⟨g, hg⟩ := perm5_exists_conj (σ : Equiv.Perm (Fin 5)) hσne'
  have hconj : g * (σ : Equiv.Perm (Fin 5)) * g⁻¹ ∈ P :=
    hN.conj_mem (σ : Equiv.Perm (Fin 5)) σ.2 g
  have hτ : (g * (σ : Equiv.Perm (Fin 5)) * g⁻¹) * (σ : Equiv.Perm (Fin 5)) ∈ P :=
    P.mul_mem hconj σ.2
  obtain ⟨k, hk⟩ := hP ⟨(g * (σ : Equiv.Perm (Fin 5)) * g⁻¹) * (σ : Equiv.Perm (Fin 5)), hτ⟩
  have hk' : ((g * (σ : Equiv.Perm (Fin 5)) * g⁻¹) * (σ : Equiv.Perm (Fin 5))) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd2 : orderOf ((g * (σ : Equiv.Perm (Fin 5)) * g⁻¹) * (σ : Equiv.Perm (Fin 5))) ∣ 2 ^ k :=
    orderOf_dvd_iff_pow_eq_one.mpr hk'
  have hdvd120 :
      orderOf ((g * (σ : Equiv.Perm (Fin 5)) * g⁻¹) * (σ : Equiv.Perm (Fin 5))) ∣ 120 := by
    have h := orderOf_dvd_natCard ((g * (σ : Equiv.Perm (Fin 5)) * g⁻¹) * (σ : Equiv.Perm (Fin 5)))
    rw [Nat.card_perm, Nat.card_fin] at h
    norm_num at h
    exact h
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hj3 : j ≤ 3 := by
    by_contra hj
    push_neg at hj
    have h16 : 2 ^ 4 ∣ 120 := by
      have h : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      rw [hjeq] at hdvd120
      exact dvd_trans h hdvd120
    exact (by norm_num : ¬ (2 ^ 4 ∣ 120)) h16
  have h8 : ((g * (σ : Equiv.Perm (Fin 5)) * g⁻¹) * (σ : Equiv.Perm (Fin 5))) ^ 8 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hjeq]
    exact pow_dvd_pow 2 hj3
  exact hg h8

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
