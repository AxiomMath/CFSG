module

public import CFSG.ClassicalInvolution.Orders.Basic
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
public import CFSG.Open.Defs
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.ClassicalInvolution

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank

section Arith

theorem cast_prod_pow_sub_one' {q : ℕ} (hq : 1 ≤ q) (s : Finset ℕ) (g : ℕ → ℕ) :
    ((∏ i ∈ s, (q ^ g i - 1) : ℕ) : ℤ) = ∏ i ∈ s, ((q : ℤ) ^ g i - 1) := by
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  rfl

theorem odd_pow_mod_four {q : ℕ} (hq : Odd q) (n : ℕ) : q ^ n % 4 = 1 ∨ q ^ n % 4 = 3 := by
  have := Nat.odd_iff.1 (hq.pow (n := n))
  omega

theorem pow_mod_four_of_even {q : ℕ} (hq : Odd q) {n : ℕ} (hn : Even n) : q ^ n % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : q ^ 2 % 4 = 1 := by
    obtain ⟨s, rfl⟩ := hq
    have : (2 * s + 1) ^ 2 = 4 * (s * s + s) + 1 := by ring
    omega
  rw [← two_mul, pow_mul, Nat.pow_mod, h1]
  simp

theorem pow_mod_four_of_odd {q : ℕ} (hq : Odd q) {n : ℕ} (hn : Odd n) : q ^ n % 4 = q % 4 := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : (q ^ 2) % 4 = 1 := by
    have := pow_mod_four_of_even hq (n := 2) even_two
    exact this
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, h1]
  simp

theorem isSquare_neg_one_pow_iff {K : Type*} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q)
    (hq : Odd q) (n : ℕ) : IsSquare ((-1 : K) ^ n) ↔ q ^ n % 4 = 1 := by
  have := Fintype.ofFinite K
  have hc : Fintype.card K = q := by rw [← Nat.card_eq_fintype_card, hK]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, pow_mod_four_of_even hq hn]
    exact iff_of_true ⟨1, by simp⟩ rfl
  · rw [hn.neg_one_pow, pow_mod_four_of_odd hq hn, FiniteField.isSquare_neg_one_iff, hc]
    have := Nat.odd_iff.1 hq
    omega

theorem isSquare_mul_iff_of_not_isSquare {K : Type*} [Field K] [Finite K] {ν x : K}
    (hν : ¬ IsSquare ν) (hx : x ≠ 0) : IsSquare (x * ν) ↔ ¬ IsSquare x := by
  classical
  have := Fintype.ofFinite K
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact ⟨0, by simp⟩)
  have hxν : x * ν ≠ 0 := mul_ne_zero hx hν0
  rw [← quadraticChar_one_iff_isSquare hxν, map_mul, quadraticChar_neg_one_iff_not_isSquare.2 hν]
  constructor
  · intro h hsq
    rw [(quadraticChar_one_iff_isSquare hx).2 hsq] at h
    norm_num at h
  · intro h
    rcases quadraticChar_dichotomy hx with h1 | h1
    · exact absurd ((quadraticChar_one_iff_isSquare hx).1 h1) h
    · rw [h1]; norm_num

theorem gcd_four_of_mod_zero {m : ℕ} (h : m % 4 = 0) : Nat.gcd 4 m = 4 := by
  rw [Nat.gcd_rec, h]
  simp

theorem gcd_four_of_mod_two {m : ℕ} (h : m % 4 = 2) : Nat.gcd 4 m = 2 := by
  rw [Nat.gcd_rec, h]
  norm_num

end Arith

section Proj

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} [Finite K] [Invertible (2 : K)]

theorem four_mul_card_projElementary_mul (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {s : ℕ}
    (hs : Nat.card ((scalars K V).subgroupOf (elementaryGroup Q)) = s) :
    4 * (Nat.card (ProjElementary Q) * s) = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  obtain ⟨hO, -⟩ := orthogonalGroup_index_four hQ h₁₂ h₁₃ h₂₃
  have hE := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((scalars K V).subgroupOf (elementaryGroup Q))
  rw [hs] at hE
  rw [hO, hE]

end Proj

section Models

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem card_statedProj_statedOmega_quadPlus_eq_ordD (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {n : ℕ} (hn : 4 ≤ n) :
    Nat.card (StatedProj (StatedOmega (StatedQuadPlus n K))) = ordD n (p ^ f) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_eq_prime_pow hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hodd : Odd (p ^ f) := odd_of_card_eq_prime_pow hp hp2 rfl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hE := commutator_orthogonalGroup_quadPlus (K := K) (n := m + 1) (by omega)
  rw [Nat.card_congr (statedProjEquiv (coe_quadPlus (m + 1) K) hE).toEquiv]
  have hpair01 : (plusPair K (⟨0, by omega⟩ : Fin (m + 1))).Orth (plusPair K ⟨1, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have hpair02 : (plusPair K (⟨0, by omega⟩ : Fin (m + 1))).Orth (plusPair K ⟨2, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have hpair12 : (plusPair K (⟨1, by omega⟩ : Fin (m + 1))).Orth (plusPair K ⟨2, by omega⟩) :=
    plusPair_orth (by simp [Fin.ext_iff])
  have hv : ∃ v, quadPlus (m + 1) K v ≠ 0 :=
    ⟨(plusPair K (⟨0, by omega⟩ : Fin (m + 1))).e + (1 : K) • (plusPair K ⟨0, by omega⟩).f, by
      rw [map_hypPair_add_smul]; exact one_ne_zero⟩
  have hO := card_orthogonalGroup_quadPlus_of_two_ne_zero h2 m
  rw [hK] at hO
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hOA : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) K)) =
      2 * ((p ^ f) ^ ((m + 1) * m) * ((p ^ f) ^ (m + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 m, ((p ^ f) ^ (2 * i) - 1)) := by
    apply Nat.cast_injective (R := ℤ)
    rw [hO]
    push_cast [Nat.cast_sub (Nat.one_le_pow (m + 1) (p ^ f) (by omega)),
      cast_prod_pow_sub_one' hq1]
    rw [mul_comm (m + 1) m]
    ring
  have hsq := isSquare_neg_one_pow_iff hK hodd (m + 1)
  have hneg := neg_mem_elementaryGroup_quadPlus_iff h2 (n := m + 1) (by omega)
  rw [ordD, Nat.add_sub_cancel]
  rcases odd_pow_mod_four hodd (m + 1) with hmod | hmod
  · have hneg' := hneg.2 (hsq.2 hmod)
    have hs := card_scalars_subgroupOf_elementaryGroup_of_neg_mem h2 hv hneg'
    have h4 := four_mul_card_projElementary_mul (nondegenerate_polarBilin_quadPlus (m + 1) K)
      hpair01 hpair02 hpair12 hs
    rw [hOA] at h4
    have hgcd : Nat.gcd 4 ((p ^ f) ^ (m + 1) - 1) = 4 := by
      have : ((p ^ f) ^ (m + 1) - 1) % 4 = 0 := by
        have := Nat.one_le_pow (m + 1) (p ^ f) (by omega)
        omega
      exact gcd_four_of_mod_zero this
    rw [hgcd]
    refine (Nat.div_eq_of_eq_mul_left (by norm_num) ?_).symm
    linarith
  · have hneg' : (LinearEquiv.neg K : (Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K]
        (Fin (m + 1) ⊕ Fin (m + 1) → K)) ∉ elementaryGroup (quadPlus (m + 1) K) := fun h =>
      by have := hsq.1 (hneg.1 h); omega
    have hs := card_scalars_subgroupOf_elementaryGroup_of_neg_not_mem hv hneg'
    have h4 := four_mul_card_projElementary_mul (nondegenerate_polarBilin_quadPlus (m + 1) K)
      hpair01 hpair02 hpair12 hs
    rw [hOA] at h4
    have hgcd : Nat.gcd 4 ((p ^ f) ^ (m + 1) - 1) = 2 := by
      have : ((p ^ f) ^ (m + 1) - 1) % 4 = 2 := by
        have := Nat.one_le_pow (m + 1) (p ^ f) (by omega)
        omega
      exact gcd_four_of_mod_two this
    rw [hgcd]
    refine (Nat.div_eq_of_eq_mul_left (by norm_num) ?_).symm
    linarith

theorem card_statedProj_statedOmega_quadMinus_eq_ordTwistedD (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (StatedProj (StatedOmega (StatedQuadMinus n K b c))) = ordTwistedD n (p ^ f) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_eq_prime_pow hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hodd : Odd (p ^ f) := odd_of_card_eq_prime_pow hp hp2 rfl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hE := commutator_orthogonalGroup_quadMinus (K := K) (n := m + 1) (b := b) (c := c)
    (by omega) hirr
  rw [Nat.card_congr (statedProjEquiv (coe_quadMinus (m + 1) K b c) hE).toEquiv]
  have hpair01 : (minusPair K b c (⟨0, by omega⟩ : Fin (m + 1 - 1))).Orth
      (minusPair K b c ⟨1, by omega⟩) := minusPair_orth (by simp [Fin.ext_iff])
  have hpair02 : (minusPair K b c (⟨0, by omega⟩ : Fin (m + 1 - 1))).Orth
      (minusPair K b c ⟨2, by omega⟩) := minusPair_orth (by simp [Fin.ext_iff])
  have hpair12 : (minusPair K b c (⟨1, by omega⟩ : Fin (m + 1 - 1))).Orth
      (minusPair K b c ⟨2, by omega⟩) := minusPair_orth (by simp [Fin.ext_iff])
  have hv : ∃ v, quadMinus (m + 1) K b c v ≠ 0 :=
    ⟨planeVec₀ (m + 1) K, by rw [quadMinus_planeVec₀]; exact one_ne_zero⟩
  have hO := card_orthogonalGroup_quadMinus_of_two_ne_zero h2 hirr m
  rw [hK] at hO
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hOA : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) K b c)) =
      2 * ((p ^ f) ^ ((m + 1) * (m + 1 - 1)) * ((p ^ f) ^ (m + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 (m + 1 - 1), ((p ^ f) ^ (2 * i) - 1)) := by
    apply Nat.cast_injective (R := ℤ)
    rw [hO]
    push_cast [cast_prod_pow_sub_one' hq1]
    rw [mul_comm (m + 1) m]
    ring
  have hν : ¬ IsSquare (b ^ 2 - 4 * c) := by
    rintro ⟨r, hr⟩
    apply hirr ((r - b) / 2)
    field_simp
    linear_combination -hr
  have hsq : IsSquare ((-1 : K) ^ (m + 1 - 1) * (4 * c - b ^ 2)) ↔ (p ^ f) ^ (m + 1) % 4 = 3 := by
    have h1 : (-1 : K) ^ (m + 1 - 1) * (4 * c - b ^ 2) = (-1) ^ (m + 1) * (b ^ 2 - 4 * c) := by
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    rw [h1, isSquare_mul_iff_of_not_isSquare hν (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)),
      isSquare_neg_one_pow_iff hK hodd]
    rcases odd_pow_mod_four hodd (m + 1) with h | h <;> simp [h]
  have hneg := neg_mem_elementaryGroup_quadMinus_iff h2 hirr (n := m + 1) hn
  rw [ordTwistedD]
  rcases odd_pow_mod_four hodd (m + 1) with hmod | hmod
  · have hneg' : (LinearEquiv.neg K : (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) ≃ₗ[K]
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K)) ∉
        elementaryGroup (quadMinus (m + 1) K b c) := fun h => by
      have := hsq.1 (hneg.1 h); omega
    have hs := card_scalars_subgroupOf_elementaryGroup_of_neg_not_mem hv hneg'
    have h4 := four_mul_card_projElementary_mul (nondegenerate_polarBilin_quadMinus_of_finite
      (m + 1) K hirr) hpair01 hpair02 hpair12 hs
    rw [hOA] at h4
    have hgcd : Nat.gcd 4 ((p ^ f) ^ (m + 1) + 1) = 2 := by
      have : ((p ^ f) ^ (m + 1) + 1) % 4 = 2 := by omega
      exact gcd_four_of_mod_two this
    rw [hgcd]
    refine (Nat.div_eq_of_eq_mul_left (by norm_num) ?_).symm
    linarith
  · have hneg' := hneg.2 (hsq.2 hmod)
    have hs := card_scalars_subgroupOf_elementaryGroup_of_neg_mem h2 hv hneg'
    have h4 := four_mul_card_projElementary_mul (nondegenerate_polarBilin_quadMinus_of_finite
      (m + 1) K hirr) hpair01 hpair02 hpair12 hs
    rw [hOA] at h4
    have hgcd : Nat.gcd 4 ((p ^ f) ^ (m + 1) + 1) = 4 := by
      have : ((p ^ f) ^ (m + 1) + 1) % 4 = 0 := by omega
      exact gcd_four_of_mod_zero this
    rw [hgcd]
    refine (Nat.div_eq_of_eq_mul_left (by norm_num) ?_).symm
    linarith

theorem card_statedProj_statedOmega_quadOdd_eq_ordBC (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (StatedProj (StatedOmega (StatedQuadOdd n K))) = ordBC n (p ^ f) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_eq_prime_pow hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hodd : Odd (p ^ f) := odd_of_card_eq_prime_pow hp hp2 rfl
  have hE := commutator_orthogonalGroup_quadOdd (K := K) (n := n) h2 hn
  rw [Nat.card_congr (statedProjEquiv (coe_quadOdd n K) hE).toEquiv]
  have hpair01 : (oddPair K (⟨0, by omega⟩ : Fin n)).Orth (oddPair K ⟨1, by omega⟩) :=
    oddPair_orth (by simp [Fin.ext_iff])
  have hpair02 : (oddPair K (⟨0, by omega⟩ : Fin n)).Orth (oddPair K ⟨2, by omega⟩) :=
    oddPair_orth (by simp [Fin.ext_iff])
  have hpair12 : (oddPair K (⟨1, by omega⟩ : Fin n)).Orth (oddPair K ⟨2, by omega⟩) :=
    oddPair_orth (by simp [Fin.ext_iff])
  have hv : ∃ v, quadOdd n K v ≠ 0 :=
    ⟨(oddPair K (⟨0, by omega⟩ : Fin n)).e + (1 : K) • (oddPair K ⟨0, by omega⟩).f, by
      rw [map_hypPair_add_smul]; exact one_ne_zero⟩
  have hs := card_scalars_subgroupOf_elementaryGroup_of_neg_not_mem hv
    (neg_not_mem_elementaryGroup_quadOdd h2 hn)
  have h4 := four_mul_card_projElementary_mul (nondegenerate_polarBilin_quadOdd n K h2)
    hpair01 hpair02 hpair12 hs
  have hO := card_orthogonalGroup_quadOdd_of_two_ne_zero h2 n
  rw [hK] at hO
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hOA : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K)) =
      2 * ((p ^ f) ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, ((p ^ f) ^ (2 * i) - 1)) := by
    apply Nat.cast_injective (R := ℤ)
    rw [hO]
    push_cast [cast_prod_pow_sub_one' hq1]
    rw [pow_two]
    ring
  rw [hOA] at h4
  rw [ordBC, gcd_two_sub_one_of_odd hodd]
  refine (Nat.div_eq_of_eq_mul_left (by norm_num) ?_).symm
  linarith

end Models

end CFSG.ClassicalInvolution
