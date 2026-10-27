module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.ComponentClassification.CatLeaf CFSG.Assembly.LowTwoRank

theorem dvd_lieOrderDivisor_cases {t : StatedLieTag} {n q p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hd : p ∣ lieOrderDivisor t n q) :
    (t = .PSL ∧ p ∣ n ∧ p ∣ q - 1) ∨ (t = .PSU ∧ p ∣ n ∧ p ∣ q + 1) := by
  cases t
  · exact Or.inl ⟨rfl, Nat.dvd_gcd_iff.mp hd⟩
  · exact Or.inr ⟨rfl, Nat.dvd_gcd_iff.mp hd⟩
  all_goals
    exfalso
    simp only [lieOrderDivisor] at hd
    first
      | exact absurd (Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))) (by omega)
      | exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)

private theorem not_dvd_of_dvd_sub_one {p x : ℕ} (hp : p.Prime) (hx : 1 ≤ x) (h : p ∣ x - 1) :
    ¬ p ∣ x := by
  intro hpx
  have h1 : p ∣ x - (x - 1) := Nat.dvd_sub hpx h
  have h2 : x - (x - 1) = 1 := by omega
  rw [h2] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

private theorem not_dvd_of_dvd_add_one {p x : ℕ} (hp : p.Prime) (h : p ∣ x + 1) : ¬ p ∣ x := by
  intro hpx
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpx).mp h))

private theorem pow_dvd_pow_sub_one {p x m : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hx : 2 ≤ x)
    (hm : m ≠ 0) (hpx : p ∣ x - 1) : p ^ (1 + m.factorization p) ∣ x ^ m - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hnx : ¬ p ∣ x := not_dvd_of_dvd_sub_one hp (by omega) hpx
  have hlte := padicValNat.pow_sub_pow hodd (by omega : 1 < x) hpx hnx hm
  rw [one_pow] at hlte
  have hne : x ^ m - 1 ≠ 0 := by
    have : 1 < x ^ m := Nat.one_lt_pow hm (by omega)
    omega
  have hv : 1 ≤ padicValNat p (x - 1) := one_le_padicValNat_of_dvd (by omega) hpx
  rw [Nat.factorization_def m hp]
  exact (padicValNat_dvd_iff_le hne).2 (by omega)

private theorem pow_dvd_pow_add_one {p x m : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hm : Odd m)
    (hpx : p ∣ x + 1) : p ^ (1 + m.factorization p) ∣ x ^ m + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hnx : ¬ p ∣ x := not_dvd_of_dvd_add_one hp hpx
  have hlte := padicValNat.pow_add_pow hodd hpx hnx hm
  rw [one_pow] at hlte
  have hne : x ^ m + 1 ≠ 0 := Nat.add_one_ne_zero _
  have hv : 1 ≤ padicValNat p (x + 1) := one_le_padicValNat_of_dvd (Nat.add_one_ne_zero x) hpx
  rw [Nat.factorization_def m hp]
  exact (padicValNat_dvd_iff_le hne).2 (by omega)

private theorem dvd_sq_sub_one {p q : ℕ} (hpq : p ∣ q + 1) : p ∣ q ^ 2 - 1 := by
  have h := Nat.pow_two_sub_pow_two q 1
  rw [one_pow] at h
  rw [h]
  exact Dvd.dvd.mul_right hpq _

private theorem dvd_pow_sub_one_of_dvd_sub_one {p q i : ℕ} (h : p ∣ q - 1) : p ∣ q ^ i - 1 := by
  have := Nat.sub_dvd_pow_sub_pow q 1 i
  rw [one_pow] at this
  exact h.trans this

private theorem dvd_psu_factor {p q i : ℕ} (hpq : p ∣ q + 1) :
    p ∣ (if Even i then q ^ i - 1 else q ^ i + 1) := by
  by_cases he : Even i
  · rw [if_pos he]
    obtain ⟨m, hm⟩ := he
    have h := dvd_pow_sub_one_of_dvd_sub_one (i := m) (dvd_sq_sub_one hpq)
    rwa [← pow_mul, show 2 * m = i by omega] at h
  · rw [if_neg he]
    have h := Odd.nat_add_dvd_pow_add_pow q 1 (Nat.not_even_iff_odd.mp he)
    rw [one_pow] at h
    exact hpq.trans h

private theorem pow_dvd_psu_factor {p q n : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hq : 2 ≤ q)
    (hn : n ≠ 0) (hpq : p ∣ q + 1) :
    p ^ (1 + n.factorization p) ∣ (if Even n then q ^ n - 1 else q ^ n + 1) := by
  by_cases he : Even n
  · rw [if_pos he]
    obtain ⟨m, hm⟩ := he
    have hm0 : m ≠ 0 := by omega
    have hn2 : n = 2 * m := by omega
    have h := pow_dvd_pow_sub_one hp h5 (x := q ^ 2) (m := m) (by nlinarith) hm0
      (dvd_sq_sub_one hpq)
    have h2 : ¬ p ∣ 2 := fun h2 => by
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have hfac : n.factorization p = m.factorization p := by
      rw [hn2, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd h2, zero_add]
    rw [hfac, hn2, pow_mul]
    exact h
  · rw [if_neg he]
    exact pow_dvd_pow_add_one hp h5 (Nat.not_even_iff_odd.mp he) hpq

private theorem pow_dvd_prod_Icc {p n a : ℕ} {f : ℕ → ℕ} (hn : 5 ≤ n)
    (h2 : p ∣ f 2) (h3 : p ∣ f 3) (h4 : p ∣ f 4) (hf : p ^ a ∣ f n) :
    p ^ (3 + a) ∣ ∏ i ∈ Finset.Icc 2 n, f i := by
  have hsub : ({2, 3, 4, n} : Finset ℕ) ⊆ Finset.Icc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_Icc]
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ f hsub)
  rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
    Finset.prod_insert (by simp; omega), Finset.prod_singleton]
  have h := mul_dvd_mul h2 (mul_dvd_mul h3 (mul_dvd_mul h4 hf))
  have e : p ^ (3 + a) = p * (p * (p * p ^ a)) := by ring
  rw [e]
  exact h

theorem pow_dvd_numerator_psl {p n q : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpn : p ∣ n) (hn : n ≠ 0)
    (hpq : p ∣ q - 1) (hq : 2 ≤ q) :
    p ^ (4 + (Nat.gcd n (q - 1)).factorization p) ∣ lieOrderNumerator .PSL n q := by
  have hn5 : 5 ≤ n := h5.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn)
  have hg : (Nat.gcd n (q - 1)).factorization p ≤ n.factorization p :=
    (Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left hn) hn).2 (Nat.gcd_dvd_left n (q - 1)) p
  have hprod := pow_dvd_prod_Icc (f := fun i => q ^ i - 1) hn5
    (dvd_pow_sub_one_of_dvd_sub_one hpq) (dvd_pow_sub_one_of_dvd_sub_one hpq)
    (dvd_pow_sub_one_of_dvd_sub_one hpq) (pow_dvd_pow_sub_one hp h5 hq hn hpq)
  unfold lieOrderNumerator
  exact Dvd.dvd.mul_left ((pow_dvd_pow p (by omega)).trans hprod) _

theorem pow_dvd_numerator_psu {p n q : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpn : p ∣ n) (hn : n ≠ 0)
    (hpq : p ∣ q + 1) (hq : 2 ≤ q) :
    p ^ (4 + (Nat.gcd n (q + 1)).factorization p) ∣ lieOrderNumerator .PSU n q := by
  have hn5 : 5 ≤ n := h5.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn)
  have hg : (Nat.gcd n (q + 1)).factorization p ≤ n.factorization p :=
    (Nat.factorization_le_iff_dvd (Nat.gcd_ne_zero_left hn) hn).2 (Nat.gcd_dvd_left n (q + 1)) p
  have hprod := pow_dvd_prod_Icc
    (f := fun i => if Even i then q ^ i - 1 else q ^ i + 1) hn5
    (dvd_psu_factor hpq) (dvd_psu_factor hpq) (dvd_psu_factor hpq)
    (pow_dvd_psu_factor hp h5 hq hn hpq)
  unfold lieOrderNumerator
  exact Dvd.dvd.mul_left ((pow_dvd_pow p (by omega)).trans hprod) _

private theorem lieOrderNumerator_psl_ne_zero {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderNumerator .PSL n q ≠ 0 := by
  unfold lieOrderNumerator
  refine mul_ne_zero (pow_ne_zero _ (by omega)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  have : 1 < q ^ i := Nat.one_lt_pow (by omega) (by omega)
  omega

private theorem lieOrderNumerator_psu_ne_zero {n q : ℕ} (hq : 2 ≤ q) :
    lieOrderNumerator .PSU n q ≠ 0 := by
  unfold lieOrderNumerator
  refine mul_ne_zero (pow_ne_zero _ (by omega)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  have : 1 < q ^ i := Nat.one_lt_pow (by omega) (by omega)
  split_ifs <;> omega

private theorem four_le_of_pow_dvd {p N g M : ℕ} (hp : p.Prime) (hM : N * g = M) (hM0 : M ≠ 0)
    (hpow : p ^ (4 + g.factorization p) ∣ M) : 4 ≤ N.factorization p := by
  subst hM
  have hN0 : N ≠ 0 := left_ne_zero_of_mul hM0
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hM0
  have h := (hp.pow_dvd_iff_le_factorization hM0).1 hpow
  rw [Nat.factorization_mul hN0 hg0, Finsupp.add_apply] at h
  omega

theorem four_le_factorization_of_dvd_lieOrderDivisor {t : StatedLieTag} {n q p N : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hq : 2 ≤ q) (hN : N * lieOrderDivisor t n q = lieOrderNumerator t n q) (hd : p ∣ lieOrderDivisor t n q) :
    4 ≤ N.factorization p := by
  have hpnum : p ∣ lieOrderNumerator t n q := hd.trans (Dvd.intro_left N hN)
  rcases dvd_lieOrderDivisor_cases hp h5 hd with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
  · have hn : n ≠ 0 := by
      rintro rfl
      have h1 : lieOrderNumerator .PSL 0 q = 1 := by simp [lieOrderNumerator]
      rw [h1] at hpnum
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpnum)
    exact four_le_of_pow_dvd hp hN (lieOrderNumerator_psl_ne_zero hq)
      (pow_dvd_numerator_psl hp h5 hpn hn hpq hq)
  · have hn : n ≠ 0 := by
      rintro rfl
      have h1 : lieOrderNumerator .PSU 0 q = 1 := by simp [lieOrderNumerator]
      rw [h1] at hpnum
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpnum)
    exact four_le_of_pow_dvd hp hN (lieOrderNumerator_psu_ne_zero hq)
      (pow_dvd_numerator_psu hp h5 hpn hn hpq hq)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
