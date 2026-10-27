module

public import CFSG.CharacterTheory.Semidihedral.CentralizerResidual
public import CFSG.CharacterTheory.Semidihedral.Principal.TensorGapBound
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.Open CFSG.TwoRankLowerBound.Helpers

universe u w

namespace RotationCongruence

theorem index_ne_two_of_isPerfect {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (H : Subgroup G) : H.index ≠ 2 := by
  intro hindex
  have : H.Normal := Subgroup.normal_of_index_eq_two hindex
  have hcard : Nat.card (G ⧸ H) = 2 := by
    simpa only [Subgroup.index_eq_card] using hindex
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hcard
  let : IsMulCommutative (G ⧸ H) := inferInstance
  have hsub : Subsingleton (G ⧸ H) := inferInstance
  have hone : Nat.card (G ⧸ H) = 1 := by
    let : Subsingleton (G ⧸ H) := hsub
    exact Nat.card_unique
  omega

theorem character_eq_of_isConj {G : Type*} [Group G] (θ : FiniteComplexRepresentation G)
    {x y : G} (h : IsConj x y) : θ.character x = θ.character y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact (Representation.char_conj _ x c).symm

theorem sum_character_subgroup_eq {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (θ : FiniteComplexRepresentation.{u, w} G) :
    ∃ m : ℕ, ∑ x : H, θ.character x = (Nat.card H : ℂ) * m := by
  obtain ⟨b⟩ := finiteIrreducibleCharacterBasis_exists (G := ↥H)
  obtain ⟨p0, hp0⟩ := finiteIrreducibleCharacterBasis_contains_irreducible b
    (principalFiniteComplexRepresentation ↥H) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hp0
  obtain ⟨m, hm⟩ := characterPairing_basis_natural b
    (inflatedFiniteComplexRepresentation H.subtype θ) p0
  refine ⟨m, ?_⟩
  unfold characterPairing at hm
  rw [hp0] at hm
  simp only [Pi.one_apply, mul_one] at hm
  have hcard : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [← hm, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  rfl

theorem sum_range_two_mul_ite_even (K : ℕ) (a b : ℂ) :
    ∑ i ∈ Finset.range (2 * K), (if Even i then a else b) = K * a + K * b := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : Even (2 * K) := even_two_mul K
    have h2 : ¬ Even (2 * K + 1) := by
      rw [Nat.not_even_iff_odd]
      exact odd_two_mul_add_one K
    rw [ite_eq_left h1, ite_eq_right h2]
    push_cast
    ring

theorem sum_range_two_mul_neg_one_pow (K : ℕ) :
    ∑ i ∈ Finset.range (2 * K), ((-1 : ℂ) ^ i) = 0 := by
  have h := sum_range_two_mul_ite_even K 1 (-1)
  rw [show (K : ℂ) * 1 + K * -1 = 0 by ring] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.even_or_odd i with hi | hi
  · rw [hi.neg_one_pow, ite_eq_left hi]
  · rw [hi.neg_one_pow, ite_eq_right (Nat.not_even_iff_odd.mpr hi)]

section Sylow

variable {G : Type u} [Group G] [Fintype G]

theorem sylow_character_sum_eq {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* (S : Subgroup G)) (hG : ∀ H : Subgroup G, H.index ≠ 2)
    (θ : FiniteComplexRepresentation.{u, w} G) :
    ∑ x : (S : Subgroup G), θ.character x =
      ∑ i ∈ Finset.range (modulus n), θ.character ((f (r n) : G) ^ i) +
        ((modulus n / 2 : ℕ) : ℂ) * θ.character ((f (r n) : G) ^ (modulus n / 2)) +
        ((modulus n / 2 : ℕ) : ℂ) * θ.character ((f (r n) : G) ^ (modulus n / 4)) := by
  have hn3 : 3 ≤ n := by omega
  let ι := FocalFusion.ambientHom n (S : Subgroup G) f
  have hι : ∀ y, ι y = (f y : G) := fun y => rfl
  have h12 : ∑ x : (S : Subgroup G), θ.character x =
      ∑ c : Fin (modulus n) × Fin 2, θ.character (ι (r n ^ c.1.val * s n ^ c.2.val)) := by
    refine (Fintype.sum_equiv ((boundedCoordinateEquiv n hn3).symm.trans f.toEquiv) _ _
      (fun c => ?_)).symm
    rw [Equiv.trans_apply, boundedCoordinateEquiv_symm_apply]
    rfl
  rw [h12, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, mul_one, pow_one]
  rw [Finset.sum_add_distrib, add_assoc]
  congr 1
  · rw [Fin.sum_univ_eq_sum_range (fun i => θ.character (ι (r n ^ i)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, hι]
  have ht : (f (z n) : G) = (f (r n) : G) ^ (modulus n / 2) := by
    rw [z, map_pow, Subgroup.coe_pow, modulus_div_two n hn3]
  have hv : (f (r n ^ (2 ^ (n - 3))) : G) = (f (r n) : G) ^ (modulus n / 4) := by
    rw [map_pow, Subgroup.coe_pow, modulus_div_four n hn]
  have hrefl : ∀ i : ℕ, θ.character (ι (r n ^ i * s n)) =
      if Even i then θ.character ((f (r n) : G) ^ (modulus n / 2))
      else θ.character ((f (r n) : G) ^ (modulus n / 4)) := by
    intro i
    split_ifs with hi
    · obtain ⟨j, rfl⟩ := hi
      have hc : IsConj (s n) (r n ^ (j + j) * s n) := by
        have h := even_outside_conjugate n hn (j : ℤ)
        rwa [show (2 : ℤ) * j = ((j + j : ℕ) : ℤ) by push_cast; ring, zpow_natCast] at h
      have hz := InvolutionFusion.supplied_s_isConj_z n hn S f hG
      rw [← character_eq_of_isConj θ (ι.map_isConj hc), ← ht]
      exact character_eq_of_isConj θ hz
    · obtain ⟨j, rfl⟩ := Nat.not_even_iff_odd.mp hi
      have hc : IsConj (r n * s n) (r n ^ (2 * j + 1) * s n) := by
        have h := odd_outside_conjugate n hn (j : ℤ)
        rwa [show (2 : ℤ) * j + 1 = ((2 * j + 1 : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast] at h
      have hfour := CentralizerResidual.ambient_order_four_fusion n hn S f hG
      rw [← character_eq_of_isConj θ (ι.map_isConj hc), ← hv]
      exact character_eq_of_isConj θ hfour
  rw [Fin.sum_univ_eq_sum_range (fun i => θ.character (ι (r n ^ i * s n)))]
  rw [Finset.sum_congr rfl fun i _ => hrefl i]
  have hM : modulus n = 2 * (modulus n / 2) := by
    rw [modulus_div_two n hn3, modulus_eq_two_mul_half (by omega)]
  rw [hM, sum_range_two_mul_ite_even, ← hM]

end Sylow

theorem sum_range_split_zero_half {M : ℕ} (hM : 4 ≤ M) (F : ℕ → ℂ) :
    ∑ i ∈ Finset.range M, F i =
      F 0 + F (M / 2) + ∑ i ∈ ((Finset.range M).erase 0).erase (M / 2), F i := by
  have h0 : 0 ∈ Finset.range M := Finset.mem_range.mpr (by omega)
  have h2 : M / 2 ∈ (Finset.range M).erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  rw [← Finset.add_sum_erase _ _ h0, ← Finset.add_sum_erase _ _ h2, add_assoc]

theorem card_erase_zero_half {M : ℕ} (hM : 4 ≤ M) :
    (((Finset.range M).erase 0).erase (M / 2)).card = M - 2 := by
  have h0 : 0 ∈ Finset.range M := Finset.mem_range.mpr (by omega)
  have h2 : M / 2 ∈ (Finset.range M).erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  rw [Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h0, Finset.card_range]
  omega

theorem sum_neg_one_pow_erase_zero_half {M : ℕ} (hM : 4 ≤ M) (hMeven : Even M)
    (hhalf : Even (M / 2)) :
    ∑ i ∈ ((Finset.range M).erase 0).erase (M / 2), (-1 : ℂ) ^ i = -2 := by
  have hsplit := sum_range_split_zero_half hM (fun i => (-1 : ℂ) ^ i)
  have hzero : ∑ i ∈ Finset.range M, (-1 : ℂ) ^ i = 0 := by
    obtain ⟨K, hK⟩ := hMeven
    rw [hK, ← two_mul]
    exact sum_range_two_mul_neg_one_pow K
  rw [hzero, pow_zero, hhalf.neg_one_pow] at hsplit
  linear_combination -hsplit

theorem not_modEq_of_mem_erase_zero_half {M i : ℕ}
    (hi : i ∈ ((Finset.range M).erase 0).erase (M / 2)) :
    ¬ (i : ℤ) ≡ 0 [ZMOD M] ∧ ¬ (i : ℤ) ≡ ((M / 2 : ℕ) : ℤ) [ZMOD M] := by
  simp only [Finset.mem_erase, Finset.mem_range] at hi
  obtain ⟨hhalf, hzero, hlt⟩ := hi
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : (i : ℤ) ≡ ((0 : ℕ) : ℤ) [ZMOD M] := by simpa using h
    exact hzero (Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h') hlt (by omega))
  · exact hhalf (Nat.ModEq.eq_of_lt_of_lt (Int.natCast_modEq_iff.mp h) hlt (by omega))

theorem padicValNat_two_mul_odd (k : ℕ) : padicValNat 2 (2 * (2 * k + 1)) = 1 := by
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by omega)]

theorem exists_odd_eq_two_pow_padicValNat {a : ℕ} (ha : a ≠ 0) :
    ∃ w : ℕ, a = 2 ^ padicValNat 2 a * w ∧ ¬ 2 ∣ w := by
  obtain ⟨w, hw⟩ := pow_padicValNat_dvd (p := 2) (n := a)
  refine ⟨w, hw, fun hd => pow_succ_padicValNat_not_dvd (p := 2) ha ?_⟩
  rw [pow_succ]
  nth_rw 2 [hw]
  exact mul_dvd_mul_left _ hd

theorem eq_sub_one_odd_multiple_half {n q : ℕ} (hn : 4 ≤ n) (hq : 3 ≤ q) (hqodd : Odd q)
    (hqM : 2 ^ padicValNat 2 (q ^ 2 - 1) = modulus n) {e : ℤ} (he1 : q % 4 = 1 → e = 1)
    (he3 : q % 4 = 3 → e = -1) :
    ∃ u : ℤ, e * q - 1 = (half n : ℤ) * (2 * u + 1) := by
  have hv : padicValNat 2 (q ^ 2 - 1) = n - 1 := by
    rw [modulus] at hqM
    exact Nat.pow_right_injective le_rfl hqM
  have hq1 : 1 ≤ q := by omega
  have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have h := Nat.sq_sub_sq q 1
    rwa [one_pow] at h
  have hq0 : q - 1 ≠ 0 := by omega
  have hq0' : q + 1 ≠ 0 := by omega
  rw [hfac, padicValNat.mul hq0' hq0] at hv
  obtain ⟨k, hk⟩ := hqodd
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have he := he1 (by omega)
    have hplus : padicValNat 2 (q + 1) = 1 := by
      rw [show q + 1 = 2 * (2 * j + 1) by omega]
      exact padicValNat_two_mul_odd j
    have hminus : padicValNat 2 (q - 1) = n - 2 := by omega
    obtain ⟨w, hw, hwodd⟩ := exists_odd_eq_two_pow_padicValNat hq0
    rw [hminus] at hw
    obtain ⟨u, hu⟩ : ∃ u, w = 2 * u + 1 := ⟨w / 2, by omega⟩
    refine ⟨u, ?_⟩
    have hcast : (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hq1, Nat.cast_one]
    rw [he, one_mul, hcast, hw, hu, half]
    push_cast
    ring
  · have he := he3 (by omega)
    have hminus : padicValNat 2 (q - 1) = 1 := by
      rw [show q - 1 = 2 * (2 * j + 1) by omega]
      exact padicValNat_two_mul_odd j
    have hplus : padicValNat 2 (q + 1) = n - 2 := by omega
    obtain ⟨w, hw, hwodd⟩ := exists_odd_eq_two_pow_padicValNat hq0'
    rw [hplus] at hw
    obtain ⟨u, hu⟩ : ∃ u, w = 2 * u + 1 := ⟨w / 2, by omega⟩
    refine ⟨-(u : ℤ) - 1, ?_⟩
    have hcast : (-1 : ℤ) * q - 1 = -((q + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [he, hcast, hw, hu, half]
    push_cast
    ring

end RotationCongruence

open RotationCongruence

theorem perfect_semidihedral_rotation_values_full_sylow_degree_congruences
    {G : Type u} [Group G] [Fintype G] [Group.IsPerfect G] {n : ℕ} (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* (S : Subgroup G)) (r t : G)
    (hr : r = f (Semidihedral.r n)) (ht : t = r ^ (modulus n / 2)) (q : ℕ) (hq : 3 ≤ q)
    (hqodd : Odd q) (hqM : 2 ^ padicValNat 2 (q ^ 2 - 1) = modulus n) (e : ℤ)
    (he1 : q % 4 = 1 → e = 1) (he3 : q % 4 = 3 → e = -1)
    (θ₁ θ₂ θ₃ : FiniteComplexRepresentation.{u, w} G) (δ₁ δ₂ δ₃ : ℤ)
    (_hδ₁ : δ₁ = 1 ∨ δ₁ = -1) (_hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (_hδ₃ : δ₃ = 1 ∨ δ₃ = -1)
    (h₁t : θ₁.character t = ((δ₁ * e * q : ℤ) : ℂ))
    (h₂t : θ₂.character t = ((-δ₂ * e * q : ℤ) : ℂ))
    (h₃t : θ₃.character t = ((-δ₃ : ℤ) : ℂ))
    (h₁r : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] →
      ¬ v ≡ ((modulus n / 2 : ℕ) : ℤ) [ZMOD modulus n] → θ₁.character (r ^ v) = δ₁)
    (h₂r : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] →
      ¬ v ≡ ((modulus n / 2 : ℕ) : ℤ) [ZMOD modulus n] →
        θ₂.character (r ^ v) = -δ₂ * (-1 : ℂ) ^ v)
    (h₃r : ∀ v : ℤ, ¬ v ≡ 0 [ZMOD modulus n] →
      ¬ v ≡ ((modulus n / 2 : ℕ) : ℤ) [ZMOD modulus n] →
        θ₃.character (r ^ v) = -δ₃ * (-1 : ℂ) ^ v) :
    (Module.finrank ℂ θ₁.vector : ℤ) ≡ δ₁ * (2 - e * q) [ZMOD 2 * modulus n] ∧
      (Module.finrank ℂ θ₂.vector : ℤ) ≡ -δ₂ * e * q [ZMOD 2 * modulus n] ∧
      (Module.finrank ℂ θ₃.vector : ℤ) ≡ δ₃ * (modulus n - 1) [ZMOD 2 * modulus n] := by
  have hn3 : 3 ≤ n := by omega
  have hG : ∀ H : Subgroup G, H.index ≠ 2 := index_ne_two_of_isPerfect
  obtain ⟨P, hM, hP⟩ : ∃ P : ℕ, modulus n = 8 * P ∧ 0 < P := by
    refine ⟨2 ^ (n - 4), ?_, pow_pos (by norm_num) _⟩
    rw [modulus, show n - 1 = (n - 4) + 3 by omega, pow_add]
    ring
  have hM2 : modulus n / 2 = 4 * P := by omega
  have hM4 : modulus n / 4 = 2 * P := by omega
  have hhalf : half n = 4 * P := by rw [← modulus_div_two n hn3, hM2]
  have hScard : (Nat.card (S : Subgroup G) : ℂ) = 2 * (modulus n : ℂ) := by
    rw [← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n hn3, modulus]
    norm_cast
    rw [← pow_succ']
    congr 1
    omega
  set E := ((Finset.range (modulus n)).erase 0).erase (modulus n / 2) with hEdef
  have hsum : ∀ (θ : FiniteComplexRepresentation.{u, w} G) (B Esum : ℂ),
      θ.character (r ^ (modulus n / 4)) = B → ∑ i ∈ E, θ.character (r ^ i) = Esum →
      ∃ m : ℕ, (Module.finrank ℂ θ.vector : ℂ) + θ.character t + Esum +
        ((modulus n / 2 : ℕ) : ℂ) * θ.character t + ((modulus n / 2 : ℕ) : ℂ) * B =
          2 * (modulus n : ℂ) * m := by
    intro θ B Esum hB hEsum
    obtain ⟨m, hm⟩ := sum_character_subgroup_eq (S : Subgroup G) θ
    refine ⟨m, ?_⟩
    rw [hScard] at hm
    rw [← hm, sylow_character_sum_eq hn S f hG θ, sum_range_split_zero_half (by omega), ← hr,
      pow_zero, ← ht, hEsum, hB]
    have h1 : θ.character 1 = (Module.finrank ℂ θ.vector : ℂ) := Representation.char_one _
    rw [h1]
  have hquarter : modulus n / 4 ∈ E := by
    simp only [hEdef, Finset.mem_erase, Finset.mem_range]
    omega
  have hquarterNot := not_modEq_of_mem_erase_zero_half hquarter
  have hquarterEven : (-1 : ℂ) ^ (((modulus n / 4 : ℕ) : ℤ)) = 1 := by
    rw [zpow_natCast, hM4]
    exact (even_two_mul P).neg_one_pow
  have hEeven : Even (modulus n / 2) := ⟨2 * P, by omega⟩
  have hMeven : Even (modulus n) := ⟨4 * P, by omega⟩
  have hneg : ∑ i ∈ E, (-1 : ℂ) ^ i = -2 :=
    sum_neg_one_pow_erase_zero_half (by omega) hMeven hEeven
  have hB₁ : θ₁.character (r ^ (modulus n / 4)) = δ₁ := by
    rw [← zpow_natCast]
    exact h₁r _ hquarterNot.1 hquarterNot.2
  have hE₁ : ∑ i ∈ E, θ₁.character (r ^ i) = ((modulus n - 2 : ℕ) : ℂ) * δ₁ := by
    rw [Finset.sum_congr rfl fun i hi => (by
      have h := not_modEq_of_mem_erase_zero_half hi
      rw [← zpow_natCast]
      exact h₁r _ h.1 h.2 : θ₁.character (r ^ i) = δ₁), Finset.sum_const,
      card_erase_zero_half (by omega), nsmul_eq_mul]
  have hB₂ : θ₂.character (r ^ (modulus n / 4)) = -δ₂ := by
    rw [← zpow_natCast, h₂r _ hquarterNot.1 hquarterNot.2, hquarterEven, mul_one]
  have hE₂ : ∑ i ∈ E, θ₂.character (r ^ i) = 2 * δ₂ := by
    rw [Finset.sum_congr rfl fun i hi => (by
      have h := not_modEq_of_mem_erase_zero_half hi
      rw [← zpow_natCast, h₂r _ h.1 h.2, zpow_natCast] :
        θ₂.character (r ^ i) = -δ₂ * (-1 : ℂ) ^ i), ← Finset.mul_sum, hneg]
    ring
  have hB₃ : θ₃.character (r ^ (modulus n / 4)) = -δ₃ := by
    rw [← zpow_natCast, h₃r _ hquarterNot.1 hquarterNot.2, hquarterEven, mul_one]
  have hE₃ : ∑ i ∈ E, θ₃.character (r ^ i) = 2 * δ₃ := by
    rw [Finset.sum_congr rfl fun i hi => (by
      have h := not_modEq_of_mem_erase_zero_half hi
      rw [← zpow_natCast, h₃r _ h.1 h.2, zpow_natCast] :
        θ₃.character (r ^ i) = -δ₃ * (-1 : ℂ) ^ i), ← Finset.mul_sum, hneg]
    ring
  obtain ⟨m₁, hm₁⟩ := hsum θ₁ _ _ hB₁ hE₁
  obtain ⟨m₂, hm₂⟩ := hsum θ₂ _ _ hB₂ hE₂
  obtain ⟨m₃, hm₃⟩ := hsum θ₃ _ _ hB₃ hE₃
  rw [h₁t, hM2, show modulus n - 2 = 8 * P - 2 by omega, hM] at hm₁
  rw [h₂t, hM2, hM] at hm₂
  rw [h₃t, hM2, hM] at hm₃
  have hP2 : 2 ≤ 8 * P := by omega
  have eq1 : (Module.finrank ℂ θ₁.vector : ℤ) + δ₁ * e * q + (8 * P - 2) * δ₁ +
      4 * P * (δ₁ * e * q) + 4 * P * δ₁ = 2 * (8 * P) * m₁ := by
    have e' : (((Module.finrank ℂ θ₁.vector : ℤ) + δ₁ * e * q + (8 * P - 2) * δ₁ +
        4 * P * (δ₁ * e * q) + 4 * P * δ₁ : ℤ) : ℂ) = ((2 * (8 * P) * m₁ : ℤ) : ℂ) := by
      push_cast [Nat.cast_sub hP2] at hm₁ ⊢
      linear_combination hm₁
    exact_mod_cast e'
  have eq2 : (Module.finrank ℂ θ₂.vector : ℤ) + -δ₂ * e * q + 2 * δ₂ +
      4 * P * (-δ₂ * e * q) + 4 * P * -δ₂ = 2 * (8 * P) * m₂ := by
    have e' : (((Module.finrank ℂ θ₂.vector : ℤ) + -δ₂ * e * q + 2 * δ₂ +
        4 * P * (-δ₂ * e * q) + 4 * P * -δ₂ : ℤ) : ℂ) = ((2 * (8 * P) * m₂ : ℤ) : ℂ) := by
      push_cast at hm₂ ⊢
      linear_combination hm₂
    exact_mod_cast e'
  have eq3 : (Module.finrank ℂ θ₃.vector : ℤ) + -δ₃ + 2 * δ₃ + 4 * P * -δ₃ + 4 * P * -δ₃ =
      2 * (8 * P) * m₃ := by
    have e' : (((Module.finrank ℂ θ₃.vector : ℤ) + -δ₃ + 2 * δ₃ + 4 * P * -δ₃ +
        4 * P * -δ₃ : ℤ) : ℂ) = ((2 * (8 * P) * m₃ : ℤ) : ℂ) := by
      push_cast at hm₃ ⊢
      linear_combination hm₃
    exact_mod_cast e'
  obtain ⟨u, hu⟩ := eq_sub_one_odd_multiple_half hn hq hqodd hqM he1 he3
  rw [hhalf] at hu
  push_cast at hu
  rw [hM]
  push_cast
  refine ⟨(Int.modEq_iff_dvd).mpr ⟨-m₁ + δ₁ + P * δ₁ * (2 * u + 1), ?_⟩,
    (Int.modEq_iff_dvd).mpr ⟨-m₂ - δ₂ * (u + 1) - P * δ₂ * (2 * u + 1), ?_⟩,
    (Int.modEq_iff_dvd).mpr ⟨-m₃, ?_⟩⟩
  · linear_combination -eq1 + 4 * P * δ₁ * hu
  · linear_combination -eq2 - (2 + 4 * P) * δ₂ * hu
  · linear_combination -eq3

end CFSG.Semidihedral.Principal
