module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Common
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Outer
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUOrder
public import CFSG.RankThree.PartOne.KC.UnitaryGoodAct
public import CFSG.RankThree.PartOne.SEITZ3.NatArith
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieOddFactor
public import CFSG.NumberTheory.OddPowAddSubOne
public import CFSG.Algebra.FiniteFieldFrobeniusPower
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormDeterminant
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

variable {F : Type} [Field F] {n p f : ℕ}

private theorem prod_PSU_ne_zero {Q n : ℕ} (hQ : 1 < Q) :
    (∏ i ∈ Finset.Icc 2 n, (if Even i then Q ^ i - 1 else Q ^ i + 1)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  split_ifs with he
  · exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by simp at hi; omega) hQ)
  · positivity

private theorem ordProj_lieOrderNumerator_PSU_pow {Q p n : ℕ} (hQ : 3 ≤ Q) (hQodd : Odd Q)
    (hpodd : Odd p) :
    ordProj[2] (lieOrderNumerator .PSU n (Q ^ p)) =
      ordProj[2] (lieOrderNumerator .PSU n Q) := by
  have hQ1 : 1 < Q := by omega
  have hp1 : p ≠ 0 := by rintro rfl; norm_num at hpodd
  have h1 : ordProj[2] (lieOrderNumerator .PSU n (Q ^ p)) =
      ∏ i ∈ Finset.Icc 2 n,
        ordProj[2] (if Even i then (Q ^ p) ^ i - 1 else (Q ^ p) ^ i + 1) := by
    rw [show lieOrderNumerator .PSU n (Q ^ p) =
        (Q ^ p) ^ (n * (n - 1) / 2) *
          ∏ i ∈ Finset.Icc 2 n,
            (if Even i then (Q ^ p) ^ i - 1 else (Q ^ p) ^ i + 1) from rfl]
    rw [Nat.ordProj_mul (a := (Q ^ p) ^ (n * (n - 1) / 2))
      (b := ∏ i ∈ Finset.Icc 2 n,
        (if Even i then (Q ^ p) ^ i - 1 else (Q ^ p) ^ i + 1)) 2
      (pow_ne_zero _ (by positivity)) (prod_PSU_ne_zero (Nat.one_lt_pow hp1 hQ1)),
      ordProj_two_eq_one_of_odd ((hQodd.pow).pow), one_mul, ordProj_two_prod]
    exact fun i hi => by
      split_ifs with he
      · exact Nat.sub_ne_zero_of_lt
          (Nat.one_lt_pow (by simp at hi; omega) (Nat.one_lt_pow hp1 hQ1))
      · positivity
  have h2 : ordProj[2] (lieOrderNumerator .PSU n Q) =
      ∏ i ∈ Finset.Icc 2 n,
        ordProj[2] (if Even i then Q ^ i - 1 else Q ^ i + 1) := by
    rw [show lieOrderNumerator .PSU n Q =
        Q ^ (n * (n - 1) / 2) *
          ∏ i ∈ Finset.Icc 2 n, (if Even i then Q ^ i - 1 else Q ^ i + 1) from rfl]
    rw [Nat.ordProj_mul (a := Q ^ (n * (n - 1) / 2))
      (b := ∏ i ∈ Finset.Icc 2 n, (if Even i then Q ^ i - 1 else Q ^ i + 1)) 2
      (pow_ne_zero _ (by positivity)) (prod_PSU_ne_zero hQ1),
      ordProj_two_eq_one_of_odd (hQodd.pow), one_mul, ordProj_two_prod]
    exact fun i hi => by
      split_ifs with he
      · exact Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by simp at hi; omega) hQ1)
      · positivity
  rw [h1, h2]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
  have hQi3 : 3 ≤ Q ^ i := by
    calc 3 ≤ Q := hQ
      _ = Q ^ 1 := (pow_one _).symm
      _ ≤ Q ^ i := Nat.pow_le_pow_right (by omega) (by omega)
  by_cases he : Even i
  · simp only [he, ↓reduceIte]
    rw [show (Q ^ p) ^ i = (Q ^ i) ^ p by rw [← pow_mul, ← pow_mul, mul_comm]]
    exact CFSG.SeitzReduction.RankOne.LieOdd.ordProj_pow_odd_sub_one hQi3 (hQodd.pow) hpodd
  · simp only [he, ↓reduceIte]
    rw [show (Q ^ p) ^ i = (Q ^ i) ^ p by rw [← pow_mul, ← pow_mul, mul_comm]]
    exact CFSG.SeitzReduction.RankOne.LieOdd.ordProj_pow_odd_add_one (hQodd.pow) hpodd

private theorem ordProj_card_primeFormP_eq_of_pow {K₀ K : Type} [Field K₀] [Field K]
    {q₀ q f₀ f n p : ℕ} (h₀ : UnitaryFieldData q₀ f₀ K₀) (h : UnitaryFieldData q f K)
    (hn : n = 3 ∨ n = 4) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hq₀2 : q₀ ≠ 2) (hQ : q ^ f = (q₀ ^ f₀) ^ p) :
    ordProj[2] (Nat.card (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
      ordProj[2] (Nat.card (primeFormP h₀
        ((1 : GL (Fin n) K₀) : Matrix (Fin n) (Fin n) K₀))) := by
  haveI : Finite K := h.finite
  haveI : Finite K₀ := h₀.finite
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hqodd : Odd q := h.prime.odd_of_ne_two hq2
  have hq₀odd : Odd q₀ := h₀.prime.odd_of_ne_two hq₀2
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  set Q := q ^ f with hQdef
  set Q₀ := q₀ ^ f₀ with hQ₀def
  have hQodd : Odd Q := hqodd.pow
  have hQ₀odd : Odd Q₀ := hq₀odd.pow
  have hQ3 : 3 ≤ Q := by
    have h1 : 3 ≤ q := by have := h.prime.two_le; omega
    calc 3 ≤ q := h1
      _ = q ^ 1 := (pow_one _).symm
      _ ≤ q ^ f := Nat.pow_le_pow_right (by omega) h.one_le
  have hQ₀3 : 3 ≤ Q₀ := by
    have h1 : 3 ≤ q₀ := by have := h₀.prime.two_le; omega
    calc 3 ≤ q₀ := h1
      _ = q₀ ^ 1 := (pow_one _).symm
      _ ≤ q₀ ^ f₀ := Nat.pow_le_pow_right (by omega) h₀.one_le
  have hQp : Q = Q₀ ^ p := hQ
  have hnum : ordProj[2] (lieOrderNumerator .PSU n Q) =
      ordProj[2] (lieOrderNumerator .PSU n Q₀) := by
    rw [hQp]
    exact ordProj_lieOrderNumerator_PSU_pow (n := n) hQ₀3 hQ₀odd hpodd
  have hd2 : ordProj[2] (Nat.gcd n (Q + 1)) = ordProj[2] (Nat.gcd n (Q₀ + 1)) := by
    rcases hn with rfl | rfl
    · have h1 : ¬ 2 ∣ Nat.gcd 3 (Q + 1) := by
        intro h2
        have := h2.trans (Nat.gcd_dvd_left 3 (Q + 1))
        omega
      have h2 : ¬ 2 ∣ Nat.gcd 3 (Q₀ + 1) := by
        intro h2
        have := h2.trans (Nat.gcd_dvd_left 3 (Q₀ + 1))
        omega
      rw [Nat.factorization_eq_zero_of_not_dvd h1,
        Nat.factorization_eq_zero_of_not_dvd h2]
    ·
      have hQ4 : Q % 4 = Q₀ % 4 := by
        have h4mod : Q ≡ Q₀ [MOD 4] := by
          rw [hQp]
          obtain ⟨k, rfl⟩ := hpodd
          have h8 : 4 ∣ Q₀ ^ 2 - 1 :=
            (by norm_num : 4 ∣ 8).trans (Nat.eight_dvd_sq_sub_one_of_odd hQ₀odd)
          have hsq : Q₀ ^ 2 ≡ 1 [MOD 4] :=
            (Nat.modEq_iff_dvd' (Nat.one_le_pow 2 Q₀ (by omega))).mpr h8 |>.symm
          rw [pow_succ, pow_mul]
          simpa using (hsq.pow k).mul (Nat.ModEq.refl Q₀)
        exact h4mod
      have hdiv4 : 4 ∣ Q + 1 ↔ 4 ∣ Q₀ + 1 := by
        have h : (Q + 1) % 4 = (Q₀ + 1) % 4 := by
          conv_lhs => rw [Nat.add_mod]
          rw [hQ4]
          conv_rhs => rw [Nat.add_mod]
        rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, h]
      have hgn : Nat.gcd 4 (Q + 1) = if 4 ∣ Q + 1 then 4 else 2 :=
        CFSG.NumberTheory.gcd_four_add_one hQodd
      have hgn₀ : Nat.gcd 4 (Q₀ + 1) = if 4 ∣ Q₀ + 1 then 4 else 2 :=
        CFSG.NumberTheory.gcd_four_add_one hQ₀odd
      rw [hgn, hgn₀]
      by_cases hh : 4 ∣ Q + 1
      · rw [if_pos hh, if_pos (hdiv4.mp hh)]
      · rw [if_neg hh, if_neg (fun h0 => hh (hdiv4.mpr h0))]
  have hP' : Nat.card (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
      Nat.gcd n (q ^ f + 1) = lieOrderNumerator .PSU n (q ^ f) :=
    CFSG.HardMathSupport.Lang.Coordinator.card_primeFormP_one_mul_gcd (n := n) h hn1
  rw [hQdef.symm] at hP'
  have hP : Nat.card (primeFormP h (1 : Matrix (Fin n) (Fin n) K)) *
      Nat.gcd n (Q + 1) = lieOrderNumerator .PSU n Q := by
    simpa only [Units.val_one] using hP'
  have hP₀' : Nat.card (primeFormP h₀ ((1 : GL (Fin n) K₀) : Matrix (Fin n) (Fin n) K₀)) *
      Nat.gcd n (q₀ ^ f₀ + 1) = lieOrderNumerator .PSU n (q₀ ^ f₀) :=
    CFSG.HardMathSupport.Lang.Coordinator.card_primeFormP_one_mul_gcd (n := n) h₀ hn1
  rw [hQ₀def.symm] at hP₀'
  have hP₀ : Nat.card (primeFormP h₀ (1 : Matrix (Fin n) (Fin n) K₀)) *
      Nat.gcd n (Q₀ + 1) = lieOrderNumerator .PSU n Q₀ := by
    simpa only [Units.val_one] using hP₀'
  have hPne : Nat.card (primeFormP h ((1 : Matrix (Fin n) (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) ≠ 0 := Nat.card_pos.ne'
  have hP₀ne : Nat.card (primeFormP h₀ ((1 : Matrix (Fin n) (Fin n) K₀) :
      Matrix (Fin n) (Fin n) K₀)) ≠ 0 := Nat.card_pos.ne'
  have hdne : Nat.gcd n (Q + 1) ≠ 0 := (Nat.gcd_pos_of_pos_right _ (by omega)).ne'
  have hd₀ne : Nat.gcd n (Q₀ + 1) ≠ 0 := (Nat.gcd_pos_of_pos_right _ (by omega)).ne'
  have hmain : ordProj[2] (Nat.card (primeFormP h ((1 : Matrix (Fin n) (Fin n) K) :
      Matrix (Fin n) (Fin n) K))) * ordProj[2] (Nat.gcd n (Q + 1)) =
      ordProj[2] (Nat.card (primeFormP h₀ ((1 : Matrix (Fin n) (Fin n) K₀) :
        Matrix (Fin n) (Fin n) K₀))) * ordProj[2] (Nat.gcd n (Q₀ + 1)) := by
    rw [← Nat.ordProj_mul 2 hPne hdne, ← Nat.ordProj_mul 2 hP₀ne hd₀ne, hP, hP₀, hnum]
  rw [hd2] at hmain
  exact Nat.mul_right_cancel (pow_pos (by norm_num) _) hmain

private theorem commutator_mem_inner_of_d (h : UnitaryFieldData p f F) {σ : F ≃+* F}
    {Q j : ℕ} (hσ : ∀ x : F, σ x = x ^ (Q ^ j)) (hQ : 1 ≤ Q)
    (hd : (p ^ f + 1).gcd n ∣ Q ^ j - 1)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ p ^ f = 2))
    (γ : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))
    (hγ : γ ∈ primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    ⁅primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A,
        γ * primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ * γ⁻¹⁆ ∈
      inner (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  haveI : (primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).Normal :=
    primeFormD_normal_of_ne (h := h) (n := n) hn hne
  haveI : (inner (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))).Normal :=
    CFSG.Fischer.innerAut_normal
  have hmem : γ⁻¹ * primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A * γ ∈
      primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    (inferInstance :
      (primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).Normal).conj_mem' _
      (MonoidHom.mem_range.mpr ⟨A, rfl⟩) γ
  obtain ⟨A', hA'⟩ := MonoidHom.mem_range.mp hmem
  have hconj :=
    conjugate_commutatorElement
      (γ⁻¹ * primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A * γ)
      (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) γ
  rw [show γ * (γ⁻¹ *
      primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A * γ) * γ⁻¹ =
      primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A by group] at hconj
  rw [← hconj, ← hA',
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.commutator_primeFormConjHom_fieldHom]
  exact (inferInstance : (inner (primeFormP h ((1 : GL (Fin n) F) :
    Matrix (Fin n) (Fin n) F))).Normal)
    |>.conj_mem _
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom_mul_glAut_inv_mem_inner
        h hσ hQ hd A') γ

theorem i2020UniOuter : I2020UniOuter := by
  intro p q hp hp2 hq hq2 hqp f K _ h n hn hn4 β hβp hβ
  classical
  haveI := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (GL (Fin n) K) := Finite.of_injective (fun g : GL (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  haveI : Finite (primeFormP h (idGram K n)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hnq : ¬(n = 3 ∧ q ^ f = 2) := by
    rintro ⟨-, h2⟩
    have := hqodd.pow (n := f)
    rw [h2] at this
    exact absurd this (by decide)
  obtain ⟨-, -, -, -, huniq, hfac, -⟩ :=
    unitary_prime_form_full_semilinear_realization h isPrimeFormGram_one hn hnq
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn hnq β with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hβp, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    obtain ⟨φ, ⟨A, hA⟩, -⟩ := huniq β
    have hφ : φ = σ := by rw [hσdef, hA, hfac]
    apply hβ A
    rw [hA, hφ, hσ1, map_one, mul_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hβ1 : β ≠ 1 := fun h1 => hσ1 (by rw [hσdef, h1, map_one])
  obtain ⟨hpf, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hnq hp hp2
      (Ne.symm hqp) β (orderOf_eq_prime hβp hβ1) σ hσdef.symm hσord
  have hβeq : β = primeFormConjHom h (idGram K n) M *
      primeFormFieldHom h isPrimeFormGram_one σ *
      (primeFormConjHom h (idGram K n) M)⁻¹ := by
    rw [← hM]
    group
  set γ : MulAut (primeFormP h (idGram K n)) := primeFormConjHom h (idGram K n) M with hγdef
  have hγ : γ ∈ primeFormD h (idGram K n) := MonoidHom.mem_range.mpr ⟨M, rfl⟩
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσord
  set h₀ : UnitaryFieldData q (f / p) (CFSG.LieType.Chevalley.fixSubfield σ) :=
    fixSubfield_unitaryFieldData h hp hp2 hσord with hh₀
  have hq₀ : ¬(n = 3 ∧ q ^ (f / p) = 2) := by
    rintro ⟨-, h2⟩
    have := hqodd.pow (n := f / p)
    rw [h2] at this
    exact absurd this (by decide)
  haveI : IsSimpleGroup (primeFormP h₀ (idGram (CFSG.LieType.Chevalley.fixSubfield σ) n)) :=
    isSimpleGroup_primeFormP_one h₀ hn hq₀
  let J₀ : Subgroup (primeFormP h (idGram K n)) := (subfieldPSU h h₀ hbar n).range
  have hJ₀C : J₀ ≤ fixSubgroup (primeFormFieldHom h isPrimeFormGram_one σ) :=
    range_subfieldPSU_le h n h₀ hbar
  have hcomm₁ : ⁅fixSubgroup (primeFormFieldHom h isPrimeFormGram_one σ),
      fixSubgroup (primeFormFieldHom h isPrimeFormGram_one σ)⁆ ≤ J₀ :=
    CFSG.LocalAnalysis.GLTheoremA.S2019.commutator_fixSubgroup_primeFormFieldHom_le h n h₀ hbar
  have hJ₀s : IsSimpleGroup ↥J₀ :=
    (MonoidHom.ofInjective (subfieldPSU_injective h h₀ hbar n (by omega))).symm.isSimpleGroup
  let J₁ : Subgroup (primeFormP h (idGram K n)) := J₀.map γ.toMonoidHom
  have hJ₁C : J₁ ≤ fixSubgroup β := by
    rw [hβeq, CFSG.LocalAnalysis.GLTheoremA.S2019.fixSubgroup_conj]
    exact Subgroup.map_mono hJ₀C
  have hJ₁s : IsSimpleGroup ↥J₁ := by
    change IsSimpleGroup ↥(J₀.map γ.toMonoidHom)
    exact (J₀.equivMapOfInjective γ.toMonoidHom γ.injective).symm.isSimpleGroup
  have hcomm₁' : ⁅fixSubgroup β, fixSubgroup β⁆ ≤ J₁ := by
    rw [hβeq, CFSG.LocalAnalysis.GLTheoremA.S2019.fixSubgroup_conj,
      ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcomm₁
  haveI : IsSimpleGroup (primeFormP h (idGram K n)) :=
    isSimpleGroup_primeFormP_one h hn hnq
  have hZ : Subgroup.center (primeFormP h (idGram K n)) = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
      (fun hc => not_commute_primeFormP_one h hn hnq hc.is_comm.comm)
  have hf2 : 1 ≤ 2 * f := by have hf1 : 1 ≤ f := h.one_le; omega
  have hpf2 : p ∣ 2 * f := dvd_mul_of_dvd_right hpf 2
  obtain ⟨j, hQ3, hQodd, hσform⟩ :=
    CFSG.FiniteField.exists_pow_apply_eq_of_orderOf_eq_prime
      (F := K) hq hq2 hf2 h.card hp hp2 hpf2 σ hσord
  set Q := q ^ (2 * f / p) with hQdef
  have hQeq : Q = (q ^ (f / p)) ^ 2 := by
    rw [hQdef]
    have hf_eq : f = p * (f / p) := by
      rw [mul_comm]
      exact (Nat.div_mul_cancel hpf).symm
    have h2f : 2 * f = p * (2 * (f / p)) := by
      calc 2 * f = 2 * (p * (f / p)) := by conv_lhs => rw [hf_eq]
        _ = p * (2 * (f / p)) := by ring
    rw [h2f, Nat.mul_div_cancel_left _ hp.pos, mul_comm 2, pow_mul]
  have hdvd : (q ^ f + 1).gcd n ∣ Q ^ j - 1 := by
    have hdvdq : (q ^ f + 1).gcd n ∣ q ^ f + 1 := Nat.gcd_dvd_left _ _
    have hqr : q ^ f = (q ^ (f / p)) ^ p := by
      have hf_eq : f = p * (f / p) := by
        rw [mul_comm]
        exact (Nat.div_mul_cancel hpf).symm
      conv_lhs => rw [hf_eq]
      rw [mul_comm p, pow_mul]
    have hdvdR : (q ^ f + 1).gcd n ∣ q ^ (f / p) + 1 := by
      refine CFSG.NumberTheory.dvd_add_one_of_dvd_odd_pow_add_one ?_ (hp.odd_of_ne_two hp2) ?_ ?_
      · rcases (show n = 3 ∨ n = 4 by omega) with rfl | rfl
        · exact Or.inl (Nat.gcd_dvd_right _ _)
        · exact Or.inr (Nat.gcd_dvd_right _ _)
      · exact hqodd.pow
      · simpa only [hqr] using hdvdq
    have hdvdQ : (q ^ f + 1).gcd n ∣ Q - 1 := by
      rw [hQeq]
      refine hdvdR.trans ?_
      have hr1 : 1 ≤ q ^ (f / p) := Nat.one_le_pow _ _ hq.pos
      rw [CFSG.RankThree.PartOne.SEITZ3.sq_sub_one_eq_mul hr1]
      exact dvd_mul_right _ _
    exact hdvdQ.trans (Nat.sub_one_dvd_pow_sub_one _ _)
  have hD : ∀ α : MulAut (primeFormP h (idGram K n)),
      ⁅α, β⁆ ∈ primeFormD h (idGram K n) :=
    fun α => CFSG.RankThree.PartOne.KCUnitaryModel.commutator_mem_primeFormD_of_ne
      (h := h) hn hnq α β
  have hDβ : ∀ d ∈ primeFormD h (idGram K n),
      ⁅d, β⁆ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h (idGram K n)) := by
    intro d hd
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hd
    rw [hβeq]
    exact commutator_mem_inner_of_d h hσform (by omega) hdvd hn hnq γ hγ A
  intro J hJ _
  have hJperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle : J ≤ J₁ := by
    rw [← hJperf]
    exact (Subgroup.commutator_mono hJ.1 hJ.1).trans hcomm₁'
  have hsn : IsSubnormal J J₁ := by
    have h1 := hJ.2.1.inf_of_le hJ₁C
    rwa [inf_eq_left.2 hJle] at h1
  have hJne : J ≠ ⊥ := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJ
  have hJeq : J = J₁ := (hsn.eq_bot_or_eq_of_isSimpleGroup hJ₁s).resolve_left hJne
  rw [hJeq]
  have hJ₁card : Nat.card J₁ = Nat.card J₀ := Subgroup.card_map_of_injective γ.injective
  have hJ₀card : Nat.card J₀ =
      Nat.card (primeFormP h₀ (idGram (CFSG.LieType.Chevalley.fixSubfield σ) n)) := by
    exact (Nat.card_congr (MonoidHom.ofInjective
      (subfieldPSU_injective h h₀ hbar n (by omega))).toEquiv).symm
  have hcardK : Nat.card K = q ^ (2 * f) := h.card
  have hcardK₀ : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = q ^ (2 * (f / p)) := h₀.card
  have hQord : q ^ f = (q ^ (f / p)) ^ p := by
    have hf_eq : f = p * (f / p) := by
      rw [mul_comm]
      exact (Nat.div_mul_cancel hpf).symm
    conv_lhs => rw [hf_eq]
    rw [mul_comm p, pow_mul]
  have hord : ordProj[2] (Nat.card J₁) =
      ordProj[2] (Nat.card (primeFormP h (idGram K n))) := by
    rw [hJ₁card, hJ₀card]
    have h := (ordProj_card_primeFormP_eq_of_pow h₀ h
      (by omega : n = 3 ∨ n = 4) hp hp2 hq2 hq2 hQord).symm
    simpa only [idGram] using h
  have hsyl : (Nat.card J₁).factorization 2 =
      (Nat.card (primeFormP h (idGram K n))).factorization 2 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hord
  haveI : (primeFormD h (idGram K n)).Normal := primeFormD_normal_of_ne (h := h) hn hnq
  exact i2020FixCentAt_of_sylow hZ (primeFormD h (idGram K n)) hD hDβ hJ₁C hsyl

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
