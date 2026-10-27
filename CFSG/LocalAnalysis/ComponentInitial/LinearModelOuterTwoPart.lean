module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearArithmetic

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Finset LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank

theorem ordProj_two_eq_one_of_odd {m : ℕ} (hm : Odd m) : ordProj[2] m = 1 := by
  rw [Nat.factorization_eq_zero_of_not_dvd (fun h => by rcases hm with ⟨k, rfl⟩; omega),
    pow_zero]

theorem ordProj_two_two_pow (k : ℕ) : ordProj[2] (2 ^ k) = 2 ^ k := by
  rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

theorem ordProj_two_prod {ι : Type*} (s : Finset ι) (g : ι → ℕ) (hg : ∀ i ∈ s, g i ≠ 0) :
    ordProj[2] (∏ i ∈ s, g i) = ∏ i ∈ s, ordProj[2] (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha,
      Nat.ordProj_mul 2 (hg a (mem_insert_self a s))
        (prod_ne_zero_iff.mpr fun i hi => hg i (mem_insert_of_mem hi)),
      ih fun i hi => hg i (mem_insert_of_mem hi)]

theorem ordProj_two_le_of_dvd {m k : ℕ} (hk : k ≠ 0) (h : m ∣ k) : ordProj[2] m ≤ ordProj[2] k :=
  Nat.le_of_dvd (Nat.ordProj_pos _ _) (Nat.ordProj_dvd_ordProj_of_dvd hk h 2)

theorem card_scalars_eq_gcd (K : Type*) [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (scalars n K) = Nat.gcd n (Nat.card K - 1) := by
  let φ : (powMonoidHom n : Kˣ →* Kˣ).ker → scalars n K := fun c =>
    ⟨scalarElement (c : Kˣ) c.2, scalarElement_mem_scalars _ _⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun c c' h => ?_, fun A => ?_⟩
    · have h0 := congrArg (fun A : scalars n K =>
        ((A : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h
      simp only [φ] at h0
      exact Subtype.ext (Units.ext h0)
    · obtain ⟨c, hc, hA⟩ := A.2
      exact ⟨⟨c, hc⟩, Subtype.ext (Subtype.ext hA.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), IsCyclic.card_powMonoidHom_ker, Nat.card_units,
    Nat.gcd_comm]

theorem linear_model_outer_two_part_bound (T : Type) [Group T] (n p f : ℕ)
    (h : StatedClassicalModel T .PSL n p f) :
    Nat.card T = (p ^ f) ^ (n * (n - 1) / 2) * (∏ j ∈ Icc 2 n, ((p ^ f) ^ j - 1)) /
        Nat.gcd n (p ^ f - 1) ∧
      4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) ∧
      (n = 2 → Nat.card (Outer T) ∣ f * Nat.gcd n (p ^ f - 1)) ∧
      (3 ≤ n → Nat.card (Outer T) ∣ 2 * f * Nat.gcd n (p ^ f - 1)) := by
  obtain ⟨⟨hp, hf, hn, h22, h23⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  set q := p ^ f with hq
  set N := n * (n - 1) / 2 with hN
  set P := ∏ j ∈ Icc 2 n, (q ^ j - 1) with hP
  set d := Nat.gcd n (q - 1) with hd
  let e' : T ≃* projectiveSL n K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  obtain ⟨-, hSL, -, -, hPcard, -⟩ := linear_order p q hK hn
  have hZ : Nat.card (scalars n K) = d := by rw [card_scalars_eq_gcd K (by omega), hK]
  have hcardT : Nat.card T = Nat.card (projectiveSL n K) := Nat.card_congr e'.toEquiv
  have hcardO : Nat.card (Outer T) = Nat.card (Outer (projectiveSL n K)) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv
  have hord : Nat.card T = q ^ N * P / d := by rw [hcardT, hPcard, hSL, hZ]
  have hout2 : n = 2 → Nat.card (Outer T) ∣ f * d := by
    rintro rfl
    exact (linear_two_outer_order_divisor hp K hK).2 T
      ⟨e'.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm⟩
  have hout3 : 3 ≤ n → Nat.card (Outer T) ∣ 2 * f * d := fun h3 => by
    rw [hcardO]
    exact UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound hp hf h3 hK
  suffices hpair : 4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) from
    ⟨hord, hpair.1, hpair.2, hout2, hout3⟩
  have hp2le := hp.two_le
  have hq2 : 2 ≤ q := le_trans hp2le (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
  have hd0 : d ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  have hqj : ∀ j ∈ Icc 2 n, 2 ≤ q ^ j := fun j hj => le_trans hq2 (by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ j := Nat.pow_le_pow_right (by omega) (by simp at hj; omega))
  have hfac0 : ∀ j ∈ Icc 2 n, q ^ j - 1 ≠ 0 := fun j hj => by have := hqj j hj; omega
  have hP0 : P ≠ 0 := prod_ne_zero_iff.mpr hfac0
  have hqN0 : q ^ N ≠ 0 := pow_ne_zero _ (by omega)
  have : Finite (projectiveSL n K) := inferInstance
  have hT0 : Nat.card T ≠ 0 := by rw [hcardT]; exact Nat.card_pos.ne'
  have hdvd : d ∣ q ^ N * P := by
    rw [← hZ, ← hSL]
    exact Subgroup.card_subgroup_dvd_card _
  have hmul : Nat.card T * d = q ^ N * P := by rw [hord]; exact Nat.div_mul_cancel hdvd
  have h2adic : ordProj[2] (Nat.card T) * ordProj[2] d = ordProj[2] (q ^ N) * ordProj[2] P := by
    rw [← Nat.ordProj_mul 2 hT0 hd0, hmul, Nat.ordProj_mul 2 hqN0 hP0]
  have hPprod : ordProj[2] P = ∏ j ∈ Icc 2 n, ordProj[2] (q ^ j - 1) :=
    ordProj_two_prod _ _ hfac0
  have hfbounds := (lie_order_two_adic_arithmetic).2.2 f hf
  have hf2pos : 0 < ordProj[2] f := Nat.ordProj_pos f 2
  have hd2pos : 0 < ordProj[2] d := Nat.ordProj_pos d 2
  have h2 : ordProj[2] 2 = 2 := ordProj_two_two_pow 1
  rcases eq_or_ne p 2 with rfl | hp2
  ·
    have hqeven : Even q := (Nat.even_pow' (by omega)).mpr even_two
    have hP1 : ordProj[2] P = 1 := by
      rw [hPprod]
      refine prod_eq_one fun j hj => ordProj_two_eq_one_of_odd ?_
      have hqje : Even (q ^ j) := (Nat.even_pow' (by simp at hj; omega)).mpr hqeven
      exact Nat.Even.sub_odd (by have := hqj j hj; omega) hqje odd_one
    have hd1 : ordProj[2] d = 1 := by
      refine ordProj_two_eq_one_of_odd (Odd.of_dvd_nat ?_ (Nat.gcd_dvd_right n (q - 1)))
      exact Nat.Even.sub_odd (by omega) hqeven odd_one
    have ha : ordProj[2] (Nat.card T) = 2 ^ (f * N) := by
      rw [hd1, mul_one, hP1, mul_one, hq, ← pow_mul, ordProj_two_two_pow] at h2adic
      exact h2adic
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · have hN1 : N = 1 := by norm_num [hN]
      have hf2 : 2 ≤ f := by
        by_contra hlt
        apply h22
        rw [hq, show f = 1 by omega, pow_one]
      have ho := ordProj_two_le_of_dvd (mul_ne_zero (by omega) hd0) (hout2 rfl)
      rw [Nat.ordProj_mul 2 (by omega) hd0, hd1, mul_one] at ho
      rw [ha, hN1, mul_one]
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      exact ⟨h4, lt_of_le_of_lt ho hfbounds.1⟩
    · have hN3 : 3 ≤ N := by
        rw [hN]
        have : 6 ≤ n * (n - 1) := le_trans (by norm_num : 6 ≤ 3 * 2) (Nat.mul_le_mul h3 (by omega))
        omega
      have ho := ordProj_two_le_of_dvd (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) hd0)
        (hout3 h3)
      rw [Nat.ordProj_mul 2 (mul_ne_zero (by norm_num) (by omega)) hd0, hd1, mul_one,
        Nat.ordProj_mul 2 (by norm_num) (by omega), h2] at ho
      have hle : 2 ^ (3 * f) ≤ 2 ^ (f * N) :=
        Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm 3 f]; exact Nat.mul_le_mul_left f hN3)
      have h8 : 8 ≤ 2 ^ (3 * f) := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [ha]
      exact ⟨by omega, by omega⟩
  ·
    have hqodd : Odd q := (hp.odd_of_ne_two hp2).pow
    have hqN1 : ordProj[2] (q ^ N) = 1 := ordProj_two_eq_one_of_odd hqodd.pow
    rw [hqN1, one_mul] at h2adic
    have h8 := ((lie_order_two_adic_arithmetic).1 p f hp hp2 hf).2
    rw [← hq] at h8
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · have hd2 : d = 2 := by
        rw [hd]
        refine Nat.gcd_eq_left ?_
        exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one)
      have hP2 : P = q ^ 2 - 1 := by rw [hP, Icc_self, prod_singleton]
      rw [hd2, h2, hP2] at h2adic
      have ho := ordProj_two_le_of_dvd (mul_ne_zero (by omega) hd0) (hout2 rfl)
      rw [Nat.ordProj_mul 2 (by omega) hd0, hd2, h2] at ho
      exact ⟨by omega, by omega⟩
    · have hprod := (lie_order_two_adic_arithmetic).2.1 p f n hp hp2 hf h3 1 (Or.inl rfl)
      have hgcd : Int.gcd (n : ℤ) (((p ^ f : ℕ) : ℤ) - 1) = d := by
        rw [hd, ← Int.gcd_natCast_natCast, Nat.cast_sub (by omega), Nat.cast_one]
      have hfac : ∀ j ∈ Icc 2 n, ordProj[2] ((((p ^ f : ℕ) : ℤ) ^ j - 1 ^ j).natAbs) =
          ordProj[2] (q ^ j - 1) := by
        intro j hj
        have hle : 1 ≤ q ^ j := by have := hqj j hj; omega
        congr 1
        rw [one_pow, ← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_sub hle, Int.natAbs_natCast]
      rw [hgcd, prod_congr rfl hfac, ← hPprod] at hprod
      have ho := ordProj_two_le_of_dvd (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) hd0)
        (hout3 h3)
      rw [Nat.ordProj_mul 2 (mul_ne_zero (by norm_num) (by omega)) hd0,
        Nat.ordProj_mul 2 (by norm_num) (by omega), h2] at ho
      have key : 8 * ordProj[2] d * ordProj[2] f ≤ ordProj[2] (Nat.card T) := by
        have hmul' : ordProj[2] d * (8 * ordProj[2] d * ordProj[2] f) ≤
            ordProj[2] d * ordProj[2] (Nat.card T) := by
          rw [mul_comm (ordProj[2] d) (ordProj[2] (Nat.card T)), h2adic]
          calc ordProj[2] d * (8 * ordProj[2] d * ordProj[2] f) =
              ordProj[2] d ^ 2 * (8 * ordProj[2] f) := by ring
            _ ≤ ordProj[2] d ^ 2 * ordProj[2] (q ^ 2 - 1) := Nat.mul_le_mul_left _ h8
            _ ≤ ordProj[2] P := hprod
        exact Nat.le_of_mul_le_mul_left hmul' hd2pos
      have h1 : 2 * ordProj[2] f * ordProj[2] d < 8 * ordProj[2] d * ordProj[2] f := by
        nlinarith
      exact ⟨by nlinarith, lt_of_le_of_lt ho (lt_of_lt_of_le h1 key)⟩

end CFSG.LocalAnalysis.ComponentInitial
