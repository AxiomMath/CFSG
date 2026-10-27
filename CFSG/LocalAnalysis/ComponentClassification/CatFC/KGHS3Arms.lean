module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Config

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup CFSG.Blueprint.NativeSporadic


theorem HSType.card_quotient_center {Y : Type} [Group Y] (hY : HSType Y) :
    Nat.card (Y ⧸ center Y) = 44352000 := by
  obtain ⟨e⟩ := hY.2
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.HS.card_HS

theorem HSType.dvd_card_self {Y : Type} [Group Y] [Finite Y] (hY : HSType Y) :
    44352000 ∣ Nat.card Y := by
  have h1 : Nat.card (Y ⧸ center Y) ∣ Nat.card Y := Subgroup.card_quotient_dvd_card _
  rwa [hY.card_quotient_center] at h1

theorem HSType.dvd_card {S : Type} [Group S] [Finite S] {K : Subgroup S} (hK : HSType ↥K) :
    44352000 ∣ Nat.card S :=
  hK.dvd_card_self.trans (Subgroup.card_subgroup_dvd_card K)

theorem kgHS3_cyclic {S : Type} [Group S] {p : ℕ} (e : S ≃* Multiplicative (ZMod p))
    (K : Subgroup S) (hK : CFSG.IsQuasisimple ↥K) : False := by
  obtain ⟨a, b, hab⟩ := hK.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply e.injective
  simp only [Subgroup.coe_mul, map_mul]
  exact mul_comm _ _

theorem kgHS3_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) (h3 : (Nat.card S).factorization 3 ≤ 4)
    (K : Subgroup S) (hK : HSType ↥K) : False := by
  have hcard : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv]
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hdvd := hK.dvd_card
  by_cases h12 : 12 ≤ n
  ·
    have h1 : (12 : ℕ).factorial ∣ n.factorial := Nat.factorial_dvd_factorial h12
    have h2 : 3 ^ 5 ∣ n.factorial := (by decide : 3 ^ 5 ∣ (12 : ℕ).factorial).trans h1
    have h3' : 2 ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
    have h4 : n.factorial = 2 * (n.factorial / 2) := (Nat.mul_div_cancel' h3').symm
    have h5 : 3 ^ 5 ∣ n.factorial / 2 := by
      have : 3 ^ 5 ∣ 2 * (n.factorial / 2) := h4 ▸ h2
      exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
    have h6 : 3 ^ 5 ∣ Nat.card S := hcard ▸ h5
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos.ne').mp h6
    omega
  · have h11 : n.factorial ≤ (11 : ℕ).factorial := Nat.factorial_le (by omega)
    have hle : Nat.card S ≤ 19958400 := by
      rw [hcard]
      have : (11 : ℕ).factorial = 39916800 := by decide
      omega
    have := Nat.le_of_dvd hpos hdvd
    omega

end CFSG.ComponentClassification.CatFC.KGHS3
