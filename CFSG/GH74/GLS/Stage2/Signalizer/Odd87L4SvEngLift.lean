module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NatMod
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3S4Pgrp

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

theorem card_specialLinear_four {F : Type} [Field F] [Finite F] :
    Nat.card SL(4, F) = Nat.card F ^ 6 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) *
      (Nat.card F ^ 4 - 1) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_four, Nat.card_eq_fintype_card (α := F)]
  generalize Fintype.card F = q at hq ⊢
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h4 : q ≤ q ^ 4 := by
    nlinarith [pow_pos (show 0 < q by omega) 2, pow_pos (show 0 < q by omega) 3]
  have h5 : q ^ 2 ≤ q ^ 4 := by nlinarith [pow_pos (show 0 < q by omega) 2]
  have h6 : q ^ 3 ≤ q ^ 4 := by nlinarith [pow_pos (show 0 < q by omega) 3]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have h7 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h7]
  zify [h1, h2, h3, h4, h5, h6, show 1 ≤ q by omega]
  ring

theorem l4_exists_lift {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Subgroup (projectiveSL 4 F)} (hX : IsPGroup p ↥X) :
    ∃ X₀ : Subgroup SL(4, F), IsPGroup p ↥X₀ ∧ X₀.map (proj 4 F) = X ∧
      ∀ g : SL(4, F), proj 4 F g ∈ normalizer (X : Set (projectiveSL 4 F)) →
        g ∈ normalizer (X₀ : Set SL(4, F)) := by
  have hker : (proj 4 F).ker ≤ Subgroup.center SL(4, F) :=
    (ker_proj 4 F).le.trans (scalars_le_center 4 F)
  have hcop : Nat.Coprime p (Nat.card (proj 4 F).ker) := by
    have hp : p.Prime := Fact.out
    have h4 : Nat.Coprime p 4 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (n := 2) (by simpa using h)))
    have hcard : Nat.card (proj 4 F).ker = Nat.gcd 4 (Nat.card F - 1) := by
      rw [ker_proj, card_scalars_eq_gcd F (by norm_num : 1 ≤ 4)]
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) h4
  obtain ⟨P, hP, hPY, hPX⟩ := NatMod.exists_lift_isPGroup (proj 4 F) (proj_surjective 4 F) hX
  refine ⟨P, hP, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hPY hg
    · intro hx
      obtain ⟨g, hg, hgx⟩ := hPX x hx
      exact ⟨g, hg, hgx⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact NatMod.conj_mem_of_mem_normalizer hP hPY hPX hker hcop hg hh
    · intro hh
      have := NatMod.conj_mem_of_mem_normalizer hP hPY hPX hker hcop (c := g⁻¹)
        (by rw [map_inv]; exact inv_mem hg) hh
      simpa [mul_assoc] using this


theorem card_specialLinear_four_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Nat.card SL(4, F) = 12130560 := by
  rw [card_specialLinear_four, hF]
  norm_num

theorem prime_eq_five_or_thirteen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : p ∣ 12130560) : p = 5 ∨ p = 13 := by
  have h12 : (12130560 : ℕ) = 2 ^ 8 * 3 ^ 6 * 5 * 13 := by norm_num
  rw [h12] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)) hp2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)) hp3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)

theorem l4_cyclic_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {X₀ : Subgroup SL(4, F)} (hX : IsPGroup p ↥X₀) :
    IsCyclic ↥X₀ := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hdvd : Nat.card X₀ ∣ 12130560 :=
    card_specialLinear_four_three hF ▸ Subgroup.card_subgroup_dvd_card X₀
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have h1 : Nat.card X₀ = 1 := by simpa using hn
    have : Subsingleton X₀ := (Nat.card_eq_one_iff_unique.1 h1).1
    infer_instance
  have hpd : p ∣ 12130560 := (dvd_pow_self p hn0.ne').trans (hn ▸ hdvd)
  have h513 := prime_eq_five_or_thirteen hp hp2 hp3 hpd
  have hn1 : n = 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have hsq : p ^ 2 ∣ 12130560 := (pow_dvd_pow p h2).trans (hn ▸ hdvd)
    rcases h513 with rfl | rfl <;> norm_num at hsq
  exact isCyclic_of_prime_card (by rw [hn, hn1, pow_one])

theorem commutator_centralizes_of_cyclic {G : Type*} [Group G] {X₀ : Subgroup G} [IsCyclic ↥X₀]
    {a b : G} (ha : a ∈ normalizer (X₀ : Set G)) (hb : b ∈ normalizer (X₀ : Set G)) :
    ∀ y ∈ X₀, y * ⁅a, b⁆ = ⁅a, b⁆ * y := by
  intro y hy
  have hH : ∀ h ∈ normalizer (X₀ : Set G), ∀ y ∈ X₀, h * y * h⁻¹ ∈ X₀ := fun h hh y hy =>
    (Subgroup.mem_normalizer_iff.1 hh y).1 hy
  exact (comm_mul_comm_of_cyclic X₀ (normalizer (X₀ : Set G)) hH ha hb hy).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
