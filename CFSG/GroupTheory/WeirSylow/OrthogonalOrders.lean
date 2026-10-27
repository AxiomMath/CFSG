module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.GroupTheory.WeirSylow.Symplectic
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount

public section

namespace CFSG.GroupTheory.WeirSylow

open Module Finset QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadMinus quadOdd)
open CFSG.Assembly.LowTwoRank (StatedSp)

variable {K : Type} [Field K] [Finite K]

theorem charP_two_of_two_eq_zero (h2 : (2 : K) = 0) : CharP K 2 := by
  have hp := CharP.char_is_prime K (ringChar K)
  refine ringChar.of_eq ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ?_)
  exact (ringChar.spec K 2).1 (by exact_mod_cast h2)

theorem natCard_orthogonalGroup_quadPlus (m : ℕ) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) K)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - 1) *
        ∏ i ∈ Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
  simp_rw [← pow_mul]
  by_cases h2 : (2 : K) = 0
  · have := charP_two_of_two_eq_zero h2
    exact (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus m).2
  · exact CFSG.ClassicalInvolution.card_orthogonalGroup_quadPlus_of_two_ne_zero h2 m

theorem natCard_orthogonalGroup_quadMinus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (m : ℕ) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
        ∏ i ∈ Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
  simp_rw [← pow_mul]
  by_cases h2 : (2 : K) = 0
  · have := charP_two_of_two_eq_zero h2
    exact (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus m hirr).2
  · exact CFSG.ClassicalInvolution.card_orthogonalGroup_quadMinus_of_two_ne_zero h2 hirr m

theorem natCard_orthogonalGroup_quadOdd (h2 : (2 : K) ≠ 0) (n : ℕ) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (n ^ 2) * ∏ i ∈ Icc 1 n, (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
  simp_rw [← pow_mul]
  exact CFSG.ClassicalInvolution.card_orthogonalGroup_quadOdd_of_two_ne_zero h2 n

omit [Finite K] in
theorem natCard_orthogonalGroup_congr {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}
    (e : Q.IsometryEquiv Q') :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q') :=
  Nat.card_congr (TauCeti.QuadraticMap.orthogonalGroupCongr e).toEquiv

theorem not_isPlusType_quadMinus {n : ℕ} (hn : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : ¬ IsPlusType (quadMinus n K b c) := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨e⟩ := nonempty_isometry_quadPlus (n := m + 1)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr)
    (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin, Nat.add_sub_cancel]
      ring) h
  have hcard := congrArg (fun k : ℕ => (k : ℤ)) (natCard_orthogonalGroup_congr e)
  rw [natCard_orthogonalGroup_quadPlus, natCard_orthogonalGroup_quadMinus hirr] at hcard
  have hq : (1 : ℤ) < Nat.card K := by exact_mod_cast Finite.one_lt_card
  have hP : ∏ i ∈ Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i hi => by
      have : (1 : ℤ) < ((Nat.card K : ℤ) ^ 2) ^ i :=
        one_lt_pow₀ (one_lt_pow₀ hq two_ne_zero) (by have := (Finset.mem_Icc.1 hi).1; omega)
      omega
  have hq0 : (2 : ℤ) * (Nat.card K : ℤ) ^ (m * (m + 1)) ≠ 0 :=
    mul_ne_zero two_ne_zero (pow_ne_zero _ (by omega))
  have := mul_right_cancel₀ hP hcard
  have := mul_left_cancel₀ hq0 this
  omega

theorem nonempty_isometry_of_not_isPlusType {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hn : 1 ≤ n) (hdim : finrank K V = 2 * n) (h : ¬ IsPlusType Q) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : Nonempty (Q.IsometryEquiv (quadMinus n K b c)) := by
  rcases exists_isometry_quadPlus_or_quadMinus Q hQ hn hdim with he | ⟨b', c', hirr', he⟩
  · obtain ⟨e⟩ := he
    exact absurd ((isPlusType_congr e).2 (isPlusType_quadPlus K n)) h
  · obtain ⟨e⟩ := he
    obtain ⟨ι⟩ := binForm_isometry hirr hirr'
    exact ⟨e.trans ((quadMinusIsometry n b' c').trans
      (((QuadraticMap.IsometryEquiv.refl _).prod ι).trans (quadMinusIsometry n b c).symm))⟩

theorem nonempty_isometry_of_isPlusType_iff {V V' : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (hQ : (polarBilin Q).Nondegenerate)
    (hQ' : (polarBilin Q').Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n)
    (hdim' : finrank K V' = 2 * n) (h : IsPlusType Q ↔ IsPlusType Q') :
    Nonempty (Q.IsometryEquiv Q') := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton V := Module.finrank_zero_iff.1 (by rw [hdim])
    have : Subsingleton V' := Module.finrank_zero_iff.1 (by rw [hdim'])
    refine ⟨⟨⟨⟨⟨fun _ => 0, fun _ _ => Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩,
      fun _ => 0, fun x => Subsingleton.elim _ _, fun x => Subsingleton.elim _ _⟩, fun x => ?_⟩⟩
    change Q' 0 = Q x
    rw [Subsingleton.elim x 0, QuadraticMap.map_zero, QuadraticMap.map_zero]
  by_cases hp : IsPlusType Q
  · obtain ⟨e⟩ := nonempty_isometry_quadPlus hQ hdim hp
    obtain ⟨e'⟩ := nonempty_isometry_quadPlus hQ' hdim' (h.1 hp)
    exact ⟨e.trans e'.symm⟩
  · rcases exists_isometry_quadPlus_or_quadMinus Q hQ hn hdim with he | ⟨b, c, hirr, he⟩
    · obtain ⟨e⟩ := he
      exact absurd ((isPlusType_congr e).2 (isPlusType_quadPlus K n)) hp
    · obtain ⟨e⟩ := he
      obtain ⟨e'⟩ := nonempty_isometry_of_not_isPlusType hQ' hn hdim' (fun h' => hp (h.2 h'))
        hirr
      exact ⟨e.trans e'.symm⟩

theorem natCard_orthogonalGroup_of_type {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {m : ℕ}
    (hdim : finrank K V = 2 * (m + 1)) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ ¬ IsPlusType Q)) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
  rcases hε with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · obtain ⟨e⟩ := nonempty_isometry_quadPlus hQ hdim h
    rw [natCard_orthogonalGroup_congr e, natCard_orthogonalGroup_quadPlus]
  · rcases exists_isometry_quadPlus_or_quadMinus Q hQ (by omega) hdim with he | ⟨b, c, hirr, he⟩
    · obtain ⟨e⟩ := he
      exact absurd ((isPlusType_congr e).2 (isPlusType_quadPlus K _)) h
    · obtain ⟨e⟩ := he
      rw [natCard_orthogonalGroup_congr e, natCard_orthogonalGroup_quadMinus hirr, sub_neg_eq_add]

theorem natCard_orthogonalGroup_odd {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h2 : ringChar K ≠ 2) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank K V = 2 * n + 1) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (n ^ 2) * ∏ i ∈ Icc 1 n, (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_smul_isometry_quadOdd h2 Q hQ hdim
  have h2' : (2 : K) ≠ 0 := fun h => h2 (by
    have := charP_two_of_two_eq_zero h
    exact ringChar.eq K 2)
  rw [← orthogonalGroup_smul Q hd, natCard_orthogonalGroup_congr e,
    natCard_orthogonalGroup_quadOdd h2']

variable {p : ℕ} [hp : Fact p.Prime]

theorem factorization_eq_sum_of_cast_eq {N : ℕ} {u c : ℤ} {k : ℕ} (hc : 2 ≤ |c|)
    (hN : (N : ℤ) = u * ∏ i ∈ Icc 1 k, (c ^ i - 1)) (hu : ¬ (p : ℤ) ∣ u) :
    N.factorization p = ∑ i ∈ Icc 1 k, padicValInt p (c ^ i - 1) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (dvd_zero _)
  have hne : ∀ i ∈ Icc 1 k, c ^ i - 1 ≠ 0 := fun i hi =>
    pow_sub_one_ne_zero hc (by have := (mem_Icc.1 hi).1; omega)
  rw [factorization_eq_padicValInt, hN, padicValInt.mul hu0 (prod_ne_zero_iff.2 hne),
    padicValInt.eq_zero_of_not_dvd hu, zero_add, padicValInt_prod hne]

omit [Field K] [Finite K] in
theorem two_le_abs_sq (hq : 1 < Nat.card K) : 2 ≤ |((Nat.card K : ℤ) ^ 2)| := by
  rw [abs_of_nonneg (by positivity)]
  have : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq
  nlinarith

omit [Field K] [Finite K] in
theorem not_dvd_pow_natCard (hpK : ¬ p ∣ Nat.card K) (k : ℕ) :
    ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ k := fun h =>
  hpK (by exact_mod_cast (Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow h)

theorem not_dvd_two (hp1 : Odd p) : ¬ (p : ℤ) ∣ 2 := fun h => by
  have h3 : p ≤ 2 := by exact_mod_cast Int.le_of_dvd (by norm_num) h
  have := hp.out.two_le
  have : p = 2 := by omega
  exact (Nat.not_even_iff_odd.2 hp1) (this ▸ even_two)

theorem factorization_card_statedSp_eq_sum (hpK : ¬ p ∣ Nat.card K) (k : ℕ) :
    (Nat.card (StatedSp k K)).factorization p =
      ∑ i ∈ Icc 1 k, padicValInt p (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
  factorization_eq_sum_of_cast_eq (two_le_abs_sq Finite.one_lt_card) (natCard_statedSp_cast K k)
    (not_dvd_pow_natCard hpK _)

theorem factorization_card_orthogonalGroup_odd (hp1 : Odd p) (hpK : ¬ p ∣ Nat.card K)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (h2 : ringChar K ≠ 2)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank K V = 2 * n + 1) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
      (Nat.card (StatedSp n K)).factorization p := by
  rw [factorization_card_statedSp_eq_sum hpK]
  refine factorization_eq_sum_of_cast_eq (two_le_abs_sq Finite.one_lt_card)
    (natCard_orthogonalGroup_odd h2 hQ hdim) fun h => ?_
  rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h with h | h
  · exact not_dvd_two hp1 h
  · exact not_dvd_pow_natCard hpK _ h

theorem factorization_card_orthogonalGroup_even (hp1 : Odd p) (hpK : ¬ p ∣ Nat.card K)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hn : 1 ≤ n) (hdim : finrank K V = 2 * n)
    {ε : ℤ} (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ ¬ IsPlusType Q)) :
    (¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ n + ε →
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
        (Nat.card (StatedSp n K)).factorization p) ∧
    (¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ n - ε →
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
        (Nat.card (StatedSp (n - 1) K)).factorization p) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcard := natCard_orthogonalGroup_of_type hQ hdim hε
  have hpZ := Nat.prime_iff_prime_int.mp hp.out
  have hc2 := two_le_abs_sq (K := K) Finite.one_lt_card
  have hεpm : ε = 1 ∨ ε = -1 := by rcases hε with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hu₀ : ¬ (p : ℤ) ∣ 2 * (Nat.card K : ℤ) ^ (m * (m + 1)) := fun h => by
    rcases hpZ.dvd_or_dvd h with h | h
    · exact not_dvd_two hp1 h
    · exact not_dvd_pow_natCard hpK _ h
  have hne : ∀ i ∈ Icc 1 m, ((Nat.card K : ℤ) ^ 2) ^ i - 1 ≠ 0 := fun i hi =>
    pow_sub_one_ne_zero hc2 (by have := (mem_Icc.1 hi).1; omega)
  have hqε : (Nat.card K : ℤ) ^ (m + 1) - ε ≠ 0 := by
    intro h
    have hq : (1 : ℤ) < Nat.card K := by exact_mod_cast Finite.one_lt_card
    have : (1 : ℤ) < (Nat.card K : ℤ) ^ (m + 1) := one_lt_pow₀ hq (by omega)
    rcases hεpm with rfl | rfl <;> omega
  have hval : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q)).factorization p =
      padicValInt p ((Nat.card K : ℤ) ^ (m + 1) - ε) +
        ∑ i ∈ Icc 1 m, padicValInt p (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
    have hu0 : (2 : ℤ) * (Nat.card K : ℤ) ^ (m * (m + 1)) ≠ 0 := fun h => hu₀ (h ▸ dvd_zero _)
    rw [factorization_eq_padicValInt, hcard, padicValInt.mul (mul_ne_zero hu0 hqε)
      (prod_ne_zero_iff.2 hne), padicValInt.mul hu0 hqε, padicValInt.eq_zero_of_not_dvd hu₀,
      zero_add, padicValInt_prod hne]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hval, factorization_card_statedSp_eq_sum hpK, Finset.sum_Icc_succ_top (by omega),
      padicValInt_sub_eq_sq_sub_one hεpm h, ← pow_mul, ← pow_mul, mul_comm (m + 1) 2, add_comm]
  · rw [hval, padicValInt.eq_zero_of_not_dvd h, zero_add, Nat.add_sub_cancel,
      factorization_card_statedSp_eq_sum hpK]

end CFSG.GroupTheory.WeirSylow
