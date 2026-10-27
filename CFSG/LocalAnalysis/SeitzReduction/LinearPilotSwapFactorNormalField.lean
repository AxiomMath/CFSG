module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalPairs

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Arith

@[expose] def unitaryFactor (q j : ℕ) : ℕ := if Even j then q ^ j - 1 else q ^ j + 1

@[expose] def unitaryCofactor (q j : ℕ) : ℕ := if Even j then q ^ j + 1 else q ^ j - 1

theorem sub_one_mul_add_one (x : ℕ) : (x - 1) * (x + 1) = x ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring_nf
  omega

theorem unitaryFactor_mul_unitaryCofactor (q j : ℕ) :
    unitaryFactor q j * unitaryCofactor q j = (q ^ j - 1) * (q ^ j + 1) := by
  unfold unitaryFactor unitaryCofactor
  split_ifs
  · rfl
  · ring

theorem coprime_add_one_of_dvd_sub_one {d x : ℕ} (hd : Odd d) (hx : 1 ≤ x) (h : d ∣ x - 1) :
    Nat.Coprime d (x + 1) := by
  obtain ⟨k, hk⟩ := h
  have h2 : x + 1 = 2 + k * d := by rw [mul_comm]; omega
  rw [h2, Nat.coprime_add_mul_right_right]
  exact Nat.coprime_two_right.2 hd

theorem coprime_sub_one_of_dvd_add_one {d x : ℕ} (hd : Odd d) (hx : 1 ≤ x) (h : d ∣ x + 1) :
    Nat.Coprime d (x - 1) := by
  have hc : Nat.gcd d (x - 1) ∣ 2 := by
    have h1 : Nat.gcd d (x - 1) ∣ x + 1 := (Nat.gcd_dvd_left _ _).trans h
    have h2 : Nat.gcd d (x - 1) ∣ x - 1 := Nat.gcd_dvd_right _ _
    rw [show x + 1 = (x - 1) + 2 by omega] at h1
    exact (Nat.dvd_add_right h2).1 h1
  have hodd : Odd (Nat.gcd d (x - 1)) := hd.of_dvd_nat (Nat.gcd_dvd_left _ _)
  rcases (Nat.dvd_prime Nat.prime_two).1 hc with h | h
  · exact h
  · rw [h] at hodd
    exact absurd hodd (by decide)

variable {q : ℕ}

theorem add_one_dvd_unitaryFactor (q j : ℕ) : q + 1 ∣ unitaryFactor q j := by
  unfold unitaryFactor
  split_ifs with hj
  · obtain ⟨i, rfl⟩ := hj
    have h1 : q + 1 ∣ q ^ 2 - 1 := by
      rw [← sub_one_mul_add_one]
      exact Dvd.intro_left _ rfl
    refine h1.trans ?_
    rw [show q ^ (i + i) = (q ^ 2) ^ i by rw [← pow_mul]; ring_nf]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  · have hj' : Odd j := Nat.not_even_iff_odd.1 hj
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 hj'

theorem coprime_add_one_unitaryCofactor (hq : Even q) (hq2 : 2 ≤ q) (j : ℕ) :
    Nat.Coprime (q + 1) (unitaryCofactor q j) := by
  have hodd : Odd (q + 1) := hq.add_one
  have hpos : 1 ≤ q ^ j := Nat.one_le_pow _ _ (by omega)
  unfold unitaryCofactor
  split_ifs with hj
  · refine coprime_add_one_of_dvd_sub_one hodd hpos ?_
    have h := add_one_dvd_unitaryFactor q j
    unfold unitaryFactor at h
    simpa only [hj, ↓reduceIte] using h
  · refine coprime_sub_one_of_dvd_add_one hodd hpos ?_
    have h := add_one_dvd_unitaryFactor q j
    unfold unitaryFactor at h
    simpa only [hj, ↓reduceIte] using h

theorem prod_sq_pow_sub_one (s : Finset ℕ) :
    ∏ j ∈ s, ((q ^ 2) ^ j - 1) = (∏ j ∈ s, (q ^ j - 1)) * ∏ j ∈ s, (q ^ j + 1) ∧
      ∏ j ∈ s, ((q ^ 2) ^ j - 1) =
        (∏ j ∈ s, unitaryFactor q j) * ∏ j ∈ s, unitaryCofactor q j := by
  have h : ∀ j, (q ^ 2) ^ j - 1 = (q ^ j - 1) * (q ^ j + 1) := fun j => by
    rw [sub_one_mul_add_one, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨?_, ?_⟩
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => h j
  · rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [h, unitaryFactor_mul_unitaryCofactor]

theorem pow_card_dvd_prod {s t : Finset ℕ} (hts : t ⊆ s) {x : ℕ → ℕ} {d : ℕ}
    (hd : ∀ j ∈ t, d ∣ x j) : d ^ t.card ∣ ∏ j ∈ s, x j := by
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset t s x hts)
  rw [← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ _ hd

end Arith

section Contradictions

variable {q n : ℕ}

theorem prod_unitaryFactor_split (s : Finset ℕ) :
    ∏ j ∈ s, unitaryFactor q j = (∏ j ∈ s.filter Even, (q ^ j - 1)) *
      ∏ j ∈ s.filter (fun j => ¬ Even j), (q ^ j + 1) := by
  rw [← Finset.prod_filter_mul_prod_filter_not s Even]
  congr 1
  · exact Finset.prod_congr rfl fun j hj => by
      simp only [unitaryFactor, (Finset.mem_filter.1 hj).2, ↓reduceIte]
  · exact Finset.prod_congr rfl fun j hj => by
      simp only [unitaryFactor, (Finset.mem_filter.1 hj).2, ↓reduceIte]

theorem false_of_field_field_arith (hq : Even q) (hq2 : 2 ≤ q) (hn : 4 ≤ n) {N P P' s s' PK sK : ℕ}
    (hs : s ∣ q - 1) (hs' : s' ∣ q - 1)
    (hP : P * s = q ^ N * ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1))
    (hP' : P' * s' = q ^ N * ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1))
    (hPK : PK * sK = q ^ (2 * N) * (∏ j ∈ Finset.Icc 2 n, (q ^ j - 1)) *
      ∏ j ∈ Finset.Icc 2 n, (q ^ j + 1))
    (hdvd : P * P' ∣ PK) : False := by
  set V := ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1) with hV
  set V' := ∏ j ∈ Finset.Icc 2 n, (q ^ j + 1) with hV'
  have hV0 : V ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj => by
    have : 2 ≤ q ^ j := le_trans hq2 (Nat.le_self_pow (by have := (Finset.mem_Icc.1 hj).1; omega) q)
    omega
  have hq0 : q ^ N ≠ 0 := pow_ne_zero _ (by omega)
  have h1 : P * s * (P' * s') * sK ∣ PK * sK * (s * s') := by
    have := mul_dvd_mul (mul_dvd_mul_right hdvd sK) (dvd_refl (s * s'))
    calc P * s * (P' * s') * sK = P * P' * sK * (s * s') := by ring
      _ ∣ PK * sK * (s * s') := this
  rw [hP, hP', hPK] at h1
  have h2 : V * sK ∣ V' * (s * s') := by
    have h3 : (q ^ N * V) * (q ^ N * V) * sK = (q ^ (2 * N) * V) * (V * sK) := by ring
    have h4 : q ^ (2 * N) * V * V' * (s * s') = (q ^ (2 * N) * V) * (V' * (s * s')) := by ring
    rw [h3, h4] at h1
    exact (mul_dvd_mul_iff_left (mul_ne_zero (pow_ne_zero _ (by omega)) hV0)).1 h1
  have hVd : V ∣ V' * (s * s') := (Dvd.intro sK rfl).trans h2
  have hq24 : q = 2 ∨ 4 ≤ q := by
    obtain ⟨k, hk⟩ := hq
    omega
  rcases hq24 with rfl | hq4
  ·
    have hs1 : s = 1 := Nat.dvd_one.1 (by simpa using hs)
    have hs1' : s' = 1 := Nat.dvd_one.1 (by simpa using hs')
    rw [hs1, hs1', mul_one, mul_one] at hVd
    have h7 : 7 ∣ V := (show 7 ∣ 2 ^ 3 - 1 by norm_num).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨by norm_num, by omega⟩))
    have h7' := h7.trans hVd
    rw [hV', Prime.dvd_finsetProd_iff (by norm_num : Nat.Prime 7).prime] at h7'
    obtain ⟨j, -, hj⟩ := h7'
    have hmod : 2 ^ j % 7 = 2 ^ (j % 3) % 7 := by
      conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul]
      rw [Nat.mul_mod, Nat.pow_mod]
      norm_num
    rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with h | h | h <;>
      rw [h] at hmod <;> norm_num at hmod <;> omega
  ·
    have hodd : Odd (q - 1) := by
      obtain ⟨k, hk⟩ := hq
      exact ⟨k - 1, by omega⟩
    have hsub : ({2, 3, 4} : Finset ℕ) ⊆ Finset.Icc 2 n := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rw [Finset.mem_Icc]
      omega
    have hcube : (q - 1) ^ 3 ∣ V := by
      have := pow_card_dvd_prod hsub (x := fun j => q ^ j - 1) (d := q - 1)
        (fun j _ => Nat.sub_one_dvd_pow_sub_one q j)
      simpa using this
    have hcop : Nat.Coprime ((q - 1) ^ 3) V' := by
      refine Nat.Coprime.pow_left _ (Nat.Coprime.prod_right fun j _ => ?_)
      exact coprime_add_one_of_dvd_sub_one hodd (Nat.one_le_pow _ _ (by omega))
        (Nat.sub_one_dvd_pow_sub_one q j)
    have h5 : (q - 1) ^ 3 ∣ s * s' := hcop.dvd_of_dvd_mul_left (hcube.trans hVd)
    have h6 : (q - 1) ^ 3 ∣ (q - 1) ^ 2 := h5.trans (by rw [sq]; exact mul_dvd_mul hs hs')
    have h7 := Nat.le_of_dvd (pow_pos (by omega) 2) h6
    have h8 : (q - 1) ^ 2 * 3 ≤ (q - 1) ^ 3 := by
      rw [pow_succ]
      exact Nat.mul_le_mul_left _ (by omega)
    have h9 : 0 < (q - 1) ^ 2 := pow_pos (by omega) 2
    omega

theorem false_of_graphField_graphField_arith (hq : Even q) (hq2 : 2 ≤ q) (hn : 4 ≤ n)
    {N P P' s s' PK sK : ℕ} (hs : s ∣ q + 1) (hs' : s' ∣ q + 1)
    (hP : P * s = q ^ N * ∏ j ∈ Finset.Icc 2 n, unitaryFactor q j)
    (hP' : P' * s' = q ^ N * ∏ j ∈ Finset.Icc 2 n, unitaryFactor q j)
    (hPK : PK * sK = q ^ (2 * N) * (∏ j ∈ Finset.Icc 2 n, unitaryFactor q j) *
      ∏ j ∈ Finset.Icc 2 n, unitaryCofactor q j)
    (hdvd : P * P' ∣ PK) : False := by
  set U := ∏ j ∈ Finset.Icc 2 n, unitaryFactor q j with hU
  set W := ∏ j ∈ Finset.Icc 2 n, unitaryCofactor q j with hW
  have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj => by
    have h2 : 2 ≤ q ^ j :=
      le_trans hq2 (Nat.le_self_pow (by have := (Finset.mem_Icc.1 hj).1; omega) q)
    unfold unitaryFactor
    split_ifs <;> omega
  have h1 : P * s * (P' * s') * sK ∣ PK * sK * (s * s') := by
    have := mul_dvd_mul (mul_dvd_mul_right hdvd sK) (dvd_refl (s * s'))
    calc P * s * (P' * s') * sK = P * P' * sK * (s * s') := by ring
      _ ∣ PK * sK * (s * s') := this
  rw [hP, hP', hPK] at h1
  have h2 : U * sK ∣ W * (s * s') := by
    have h3 : (q ^ N * U) * (q ^ N * U) * sK = (q ^ (2 * N) * U) * (U * sK) := by ring
    have h4 : q ^ (2 * N) * U * W * (s * s') = (q ^ (2 * N) * U) * (W * (s * s')) := by ring
    rw [h3, h4] at h1
    exact (mul_dvd_mul_iff_left (mul_ne_zero (pow_ne_zero _ (by omega)) hU0)).1 h1
  have hUd : U ∣ W * (s * s') := (Dvd.intro sK rfl).trans h2
  have hsub : ({2, 3, 4} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rw [Finset.mem_Icc]
    omega
  have hcube : (q + 1) ^ 3 ∣ U := by
    have := pow_card_dvd_prod hsub (x := fun j => unitaryFactor q j) (d := q + 1)
      (fun j _ => add_one_dvd_unitaryFactor q j)
    simpa using this
  have hcop : Nat.Coprime ((q + 1) ^ 3) W :=
    Nat.Coprime.pow_left _
      (Nat.Coprime.prod_right fun j _ => coprime_add_one_unitaryCofactor hq hq2 j)
  have h5 : (q + 1) ^ 3 ∣ s * s' := hcop.dvd_of_dvd_mul_left (hcube.trans hUd)
  have h6 : (q + 1) ^ 3 ∣ (q + 1) ^ 2 := h5.trans (by rw [sq]; exact mul_dvd_mul hs hs')
  have h7 := Nat.le_of_dvd (pow_pos (by omega) 2) h6
  have h8 : (q + 1) ^ 2 * 3 ≤ (q + 1) ^ 3 := by
    rw [pow_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  have h9 : 0 < (q + 1) ^ 2 := pow_pos (by omega) 2
  omega

theorem false_of_field_graphField_arith (hq : Even q) (hq2 : 2 ≤ q) (hn : 4 ≤ n)
    {N P P' s s' PK sK : ℕ} (hs : s ∣ q - 1) (hs' : s' ∣ q + 1)
    (hP : P * s = q ^ N * ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1))
    (hP' : P' * s' = q ^ N * ∏ j ∈ Finset.Icc 2 n, unitaryFactor q j)
    (hPK : PK * sK = q ^ (2 * N) * (∏ j ∈ Finset.Icc 2 n, (q ^ j - 1)) *
      ∏ j ∈ Finset.Icc 2 n, (q ^ j + 1))
    (hdvd : P * P' ∣ PK) : False := by
  set S := Finset.Icc 2 n with hS
  set V := ∏ j ∈ S, (q ^ j - 1) with hV
  set U := ∏ j ∈ S, unitaryFactor q j with hU
  set V' := ∏ j ∈ S, (q ^ j + 1) with hV'
  have hpos : ∀ j ∈ S, 2 ≤ q ^ j := fun j hj =>
    le_trans hq2 (Nat.le_self_pow (by have := (Finset.mem_Icc.1 hj).1; omega) q)
  have hV0 : V ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj => by have := hpos j hj; omega
  have h1 : P * s * (P' * s') * sK ∣ PK * sK * (s * s') := by
    have := mul_dvd_mul (mul_dvd_mul_right hdvd sK) (dvd_refl (s * s'))
    calc P * s * (P' * s') * sK = P * P' * sK * (s * s') := by ring
      _ ∣ PK * sK * (s * s') := this
  rw [hP, hP', hPK] at h1
  have h2 : U * sK ∣ V' * (s * s') := by
    have h3 : (q ^ N * V) * (q ^ N * U) * sK = (q ^ (2 * N) * V) * (U * sK) := by ring
    have h4 : q ^ (2 * N) * V * V' * (s * s') = (q ^ (2 * N) * V) * (V' * (s * s')) := by ring
    rw [h3, h4] at h1
    exact (mul_dvd_mul_iff_left (mul_ne_zero (pow_ne_zero _ (by omega)) hV0)).1 h1
  have hUd : U ∣ V' * (s * s') := (Dvd.intro sK rfl).trans h2
  set Em := ∏ j ∈ S.filter Even, (q ^ j - 1) with hEm
  set Ep := ∏ j ∈ S.filter Even, (q ^ j + 1) with hEp
  set Op := ∏ j ∈ S.filter (fun j => ¬ Even j), (q ^ j + 1) with hOp
  have hUs : U = Em * Op := prod_unitaryFactor_split S
  have hV's : V' = Ep * Op := (Finset.prod_filter_mul_prod_filter_not S Even _).symm
  have hO0 : Op ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => by omega
  rw [hUs, hV's] at hUd
  have hEd : Em ∣ Ep * (s * s') := by
    have h3 : Ep * Op * (s * s') = Op * (Ep * (s * s')) := by ring
    rw [h3, mul_comm Em] at hUd
    exact (mul_dvd_mul_iff_left hO0).1 hUd
  have hsub : ({2, 4} : Finset ℕ) ⊆ S.filter Even := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rw [Finset.mem_filter, hS, Finset.mem_Icc]
    rcases hj with rfl | rfl
    · exact ⟨⟨le_rfl, by omega⟩, ⟨1, rfl⟩⟩
    · exact ⟨⟨by norm_num, hn⟩, ⟨2, rfl⟩⟩
  have hdE : ∀ j ∈ S.filter Even, q + 1 ∣ q ^ j - 1 := fun j hj => by
    have h := add_one_dvd_unitaryFactor q j
    simpa only [unitaryFactor, (Finset.mem_filter.1 hj).2, ↓reduceIte] using h
  have hsq : (q + 1) ^ 2 ∣ Em := by
    have := pow_card_dvd_prod hsub (x := fun j => q ^ j - 1) (d := q + 1)
      (fun j hj => hdE j (hsub hj))
    simpa using this
  have hodd : Odd (q + 1) := hq.add_one
  have hcopE : Nat.Coprime (q + 1) Ep := Nat.Coprime.prod_right fun j hj =>
    coprime_add_one_of_dvd_sub_one hodd (Nat.one_le_pow _ _ (by omega)) (hdE j hj)
  have hcops : Nat.Coprime (q + 1) s :=
    Nat.Coprime.coprime_dvd_right hs (coprime_sub_one_of_dvd_add_one hodd (by omega) dvd_rfl)
  have hcop : Nat.Coprime ((q + 1) ^ 2) (Ep * s) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.mul_right hcopE hcops)
  have h5 : (q + 1) ^ 2 ∣ s' := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [show Ep * s * s' = Ep * (s * s') by ring]
    exact hsq.trans hEd
  have h6 := Nat.le_of_dvd (by omega) (h5.trans hs')
  have h7 : (q + 1) * 3 ≤ (q + 1) ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

end Contradictions

section Orders

open CFSG.ClassicalGroups.UnitaryFlag (unitarySU unitaryPSU)

variable {n : ℕ}

theorem card_projectiveSL_normal_form {F : Type} [Field F] [Finite F] (hn : 1 ≤ n) :
    Nat.card (projectiveSL n F) * Nat.card (scalars n F) =
      Nat.card F ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (Nat.card F ^ j - 1) ∧
      Nat.card (scalars n F) ∣ Nat.card F - 1 := by
  refine ⟨?_, card_scalars_dvd hn⟩
  rw [← card_SL_eq hn]
  exact ((scalars n F).card_eq_card_quotient_mul_card_subgroup).symm

theorem card_unitarySU_eq_nat {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)
    (hn : 1 ≤ n) :
    Nat.card (unitarySU 2 a K n) =
      (2 ^ a) ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, unitaryFactor (2 ^ a) j := by
  have hZ := (card_unitarySU_and_factorization h hn).1
  have h1 : ∀ j, ((unitaryFactor (2 ^ a) j : ℕ) : ℤ) = (((2 ^ a : ℕ) : ℤ) ^ j - (-1) ^ j) := by
    intro j
    have hpos : 1 ≤ (2 ^ a) ^ j := Nat.one_le_pow _ _ (by positivity)
    unfold unitaryFactor
    split_ifs with hj
    · rw [Nat.cast_sub hpos, hj.neg_one_pow]
      push_cast
      ring
    · rw [(Nat.not_even_iff_odd.1 hj).neg_one_pow]
      push_cast
      ring
  apply Nat.cast_injective (R := ℤ)
  rw [hZ]
  push_cast [h1]
  rfl

end Orders

section Residual

open CFSG.ClassicalGroups.UnitaryFlag (unitarySU unitaryPSU)

variable {n : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem fieldTypeCore_normal_form (hn : 1 ≤ n) {a : ℕ} {θ : MulAut (projectiveSL n K)}
    (hθ : FieldTypeCore n (a + a) K θ) :
    (∃ s, s ∣ 2 ^ a - 1 ∧ Nat.card (perfectCore (fixedSubgroup θ)) * s =
      (2 ^ a) ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, ((2 ^ a) ^ j - 1)) ∨
    (∃ s, s ∣ 2 ^ a + 1 ∧ Nat.card (perfectCore (fixedSubgroup θ)) * s =
      (2 ^ a) ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, unitaryFactor (2 ^ a) j) := by
  obtain ⟨-, hdata⟩ := hθ
  have ha : (a + a) / 2 = a := by omega
  rcases hdata with ⟨K₀, _, _, hK₀, hcard⟩ | ⟨h, hcard⟩
  · left
    rw [ha] at hK₀
    obtain ⟨h1, h2⟩ := card_projectiveSL_normal_form (F := K₀) hn
    rw [hK₀] at h1 h2
    exact ⟨_, h2, by rw [hcard, h1]⟩
  · right
    refine ⟨Nat.gcd n (2 ^ a + 1), Nat.gcd_dvd_right _ _, ?_⟩
    have e1 := card_unitaryPSU_mul h hn
    rw [card_unitarySU_eq_nat h hn] at e1
    rw [show (2 : ℕ) ^ ((a + a) / 2) = 2 ^ a by rw [ha]] at e1
    rw [hcard, e1]

theorem fieldTypePairExclusion (hn : 4 ≤ n) {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    FieldTypePairExclusion n f K := by
  intro θ₁ θ₂ hF₁ hF₂ hdvd
  obtain ⟨a, ha⟩ := hF₁.1
  have ha1 : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    subst this
    have h1 : Nat.card K = 1 := by rw [hK, ha]; rfl
    exact absurd h1 (Finite.one_lt_card_iff_nontrivial.2 inferInstance).ne'
  subst ha
  set q₀ := 2 ^ a with hq₀
  have hq : Even q₀ := (Nat.even_pow' (by omega)).2 even_two
  have hq2 : 2 ≤ q₀ := by
    rw [hq₀]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
  obtain ⟨hPK, -⟩ := card_projectiveSL_normal_form (F := K) (by omega : 1 ≤ n)
  rw [hK, show (2 : ℕ) ^ (a + a) = q₀ ^ 2 by rw [hq₀, ← pow_mul]; ring_nf] at hPK
  obtain ⟨hVV, hUW⟩ := prod_sq_pow_sub_one (q := q₀) (Finset.Icc 2 n)
  have hpow : (q₀ ^ 2) ^ (n * (n - 1) / 2) = q₀ ^ (2 * (n * (n - 1) / 2)) := by rw [← pow_mul]
  have hPK₁ := hPK
  rw [hVV, hpow, ← mul_assoc] at hPK₁
  have hPK₂ := hPK
  rw [hUW, hpow, ← mul_assoc] at hPK₂
  rcases fieldTypeCore_normal_form (by omega) hF₁ with ⟨s, hs, h₁⟩ | ⟨s, hs, h₁⟩ <;>
    rcases fieldTypeCore_normal_form (by omega) hF₂ with ⟨s', hs', h₂⟩ | ⟨s', hs', h₂⟩
  · exact false_of_field_field_arith hq hq2 hn hs hs' h₁ h₂ hPK₁ hdvd
  · exact false_of_field_graphField_arith hq hq2 hn hs hs' h₁ h₂ hPK₁ hdvd
  · exact false_of_field_graphField_arith hq hq2 hn hs' hs h₂ h₁ hPK₁ (by rwa [mul_comm])
  · exact false_of_graphField_graphField_arith hq hq2 hn hs hs' h₁ h₂ hPK₂ hdvd

end Residual

end CFSG.SeitzReduction.LinearPilot
