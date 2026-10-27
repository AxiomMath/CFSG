module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GroupTheory

open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem le_centralizer_of_card_nine_of_isPGroup {p : ℕ} (hp : p.Prime)
    (hp6 : Nat.Coprime p 6) {B E : Subgroup X} (hB : IsPGroup p B)
    (hE : Nat.card E = 9) (hBE : B ≤ Subgroup.normalizer (E : Set X)) :
    B ≤ Subgroup.centralizer (E : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro b hb
  let Z : Subgroup X := Subgroup.zpowers b
  have hZp : IsPGroup p Z := hB.to_le (Subgroup.zpowers_le.mpr hb)
  have hZN : Z ≤ Subgroup.normalizer (E : Set X) := (Subgroup.zpowers_le).mpr (hBE hb)
  letI : MulDistribMulAction ↥Z ↥E :=
    MulDistribMulAction.compHom ↥E ((E.normalizerMonoidHom).comp (Subgroup.inclusion hZN))
  have hmod := hZp.card_modEq_card_fixedPoints ↥E
  let F : Subgroup ↥E := FixedPoints.subgroup Z ↥E
  have hFcard : Nat.card (MulAction.fixedPoints Z ↥E) = Nat.card F := rfl
  rw [hE, hFcard] at hmod
  have hFdvd : Nat.card F ∣ 9 := hE ▸ Subgroup.card_subgroup_dvd_card F
  have hF9 : Nat.card F = 9 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at hFdvd
    obtain ⟨k, hk, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hFdvd
    have hp2 : p ≠ 2 := fun h2 => by
      rw [h2] at hp6
      norm_num at hp6
    have hp3 : p ≠ 3 := fun h3 => by
      rw [h3] at hp6
      norm_num at hp6
    interval_cases k
    · exfalso
      rw [hFk, pow_zero] at hmod
      have h8 : p ∣ 8 := by
        have := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
        simpa using this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h8)))
    · exfalso
      rw [hFk, pow_one] at hmod
      have h6 : p ∣ 6 := by
        have := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
        simpa using this
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hp6 h6)
    · rw [hFk]
      norm_num
  have htop : F = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hF9, hE]
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hcF : (⟨c, hc⟩ : ↥E) ∈ F := htop ▸ Subgroup.mem_top _
  have h1 := (FixedPoints.mem_subgroup Z ↥E ⟨c, hc⟩).mp hcF ⟨b, Subgroup.mem_zpowers b⟩
  have h2 : b * c * b⁻¹ = c := by
    have := congrArg Subtype.val h1
    simpa [MulAction.compHom_smul_def,
      Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  calc c * b = (b * c * b⁻¹) * b := by rw [h2]
    _ = b * c := by group

end CFSG.GroupTheory

end