module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftLeaves
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Quasithin.Vol2.Ch11SecBL2UKp
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace KListI1Proof

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.AGLEmbedding

open scoped MatrixGroups

theorem card_psl_three_three : Nat.card PSL(3, ZMod 3) = 5616 := by
  have h := CFSG.Quasithin.Vol2.Ch11.SecB.card_psl_eq_ordA (K := ZMod 3) (n := 3) (by norm_num)
  rw [Nat.card_zmod] at h
  rw [h]
  decide

theorem card_psl_two (r : ℕ) [Fact r.Prime] :
    Nat.card PSL(2, ZMod r) = ordA 1 r := by
  have h := CFSG.Quasithin.Vol2.Ch11.SecB.card_psl_eq_ordA (K := ZMod r) (n := 2) (by norm_num)
  rw [Nat.card_zmod] at h
  exact h

theorem ordA_one_eq {r : ℕ} (hr : Odd r) : ordA 1 r = r * (r ^ 2 - 1) / 2 := by
  have hI : Finset.Icc 2 (1 + 1) = {2} := by decide
  unfold ordA
  rw [hI, Finset.prod_singleton]
  have hg : Nat.gcd (1 + 1) (r - 1) = 2 := by
    apply Nat.gcd_eq_left
    obtain ⟨a, rfl⟩ := hr
    omega
  rw [hg]
  norm_num

theorem psl2_facts {r ord : ℕ} (hr : Odd r) (h : ord = r * (r ^ 2 - 1) / 2) :
    r ∣ ord ∧ 2 * ord + r = r ^ 3 := by
  obtain ⟨a, rfl⟩ := hr
  have h1 : (2 * a + 1) ^ 2 - 1 = 4 * (a * (a + 1)) := by
    have : (2 * a + 1) ^ 2 = 4 * (a * (a + 1)) + 1 := by ring
    omega
  have h2 : ord = (2 * a + 1) * (2 * (a * (a + 1))) := by
    rw [h, h1, show (2 * a + 1) * (4 * (a * (a + 1))) = 2 * ((2 * a + 1) * (2 * (a * (a + 1))))
      by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  exact ⟨⟨_, h2⟩, by rw [h2]; ring⟩

theorem le_succ_of_pow_two_dvd {m r ord : ℕ} (hr : Odd r) (hr3 : 3 ≤ r)
    (hcube : 2 * ord + r = r ^ 3) (hdvd : 2 ^ m ∣ ord) : 2 ^ m ≤ r + 1 := by
  obtain ⟨a, rfl⟩ := hr
  have hord : ord = (2 * a + 1) * (2 * a * (a + 1)) := by
    have h := hcube
    ring_nf at h ⊢
    nlinarith [h]
  have hcop : Nat.Coprime (2 ^ m) (2 * a + 1) := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  rw [hord] at hdvd
  have h2 : 2 ^ m ∣ 2 * a * (a + 1) := hcop.dvd_of_dvd_mul_left hdvd
  have ha : 1 ≤ a := by omega
  rcases Nat.even_or_odd a with hae | hao
  · have hcop2 : Nat.Coprime (2 ^ m) (a + 1) := by
      apply Nat.Coprime.pow_left
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_
      obtain ⟨b, hb⟩ := hae
      omega
    have h3 : 2 ^ m ∣ 2 * a := hcop2.dvd_of_dvd_mul_right h2
    have := Nat.le_of_dvd (by omega) h3
    omega
  · have hcop2 : Nat.Coprime (2 ^ m) a := by
      apply Nat.Coprime.pow_left
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_
      obtain ⟨b, hb⟩ := hao
      omega
    have h3 : 2 ^ m ∣ 2 * (a + 1) := by
      have : 2 * a * (a + 1) = a * (2 * (a + 1)) := by ring
      rw [this] at h2
      exact hcop2.dvd_of_dvd_mul_left h2
    have := Nat.le_of_dvd (by omega) h3
    omega

theorem false_of_cube_bound {m r ord : ℕ} (hr : Odd r) (hr3 : 3 ≤ r)
    (hcube : 2 * ord + r = r ^ 3) (hdvd : 2 ^ m ∣ ord) (h8 : 8 ≤ 2 ^ m)
    (hb : 4 * ord ≤ (2 ^ m) ^ 3) : False := by
  have hM := le_succ_of_pow_two_dvd hr hr3 hcube hdvd
  have h1 : (2 ^ m) ^ 3 ≤ (r + 1) ^ 3 := Nat.pow_le_pow_left hM 3
  have hr7 : 7 ≤ r := by omega
  nlinarith [hcube, hb, h1, hr7, Nat.mul_le_mul hr7 hr7]

theorem prime_dvd_of_dvd_div {q N F g r : ℕ} (hr : r.Prime) (hrq : ¬ r ∣ q) (hg : g ∣ F)
    (h : r ∣ q ^ N * F / g) : r ∣ F := by
  have h1 : r ∣ q ^ N * F := h.trans (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right hg _))
  rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
  · exact absurd (hr.dvd_of_dvd_pow h2) hrq
  · exact h2

theorem prime_le_of_dvd_prod {s : Finset ℕ} {f : ℕ → ℕ} {B r : ℕ} (hr : r.Prime)
    (hf : ∀ i ∈ s, 0 < f i ∧ f i ≤ B) (h : r ∣ ∏ i ∈ s, f i) : r ≤ B := by
  obtain ⟨i, hi, hdvd⟩ := (Prime.dvd_finset_prod_iff hr.prime _).1 h
  exact (Nat.le_of_dvd (hf i hi).1 hdvd).trans (hf i hi).2

theorem not_dvd_two_pow {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ∣ 2 ^ e := by
  intro h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))

theorem two_le_two_pow {e : ℕ} (he : 1 ≤ e) : 2 ≤ 2 ^ e :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he

theorem false_of_prime_bound {q N d r : ℕ} (hq : 2 ≤ q) (hd : 2 ≤ d) (hNd : d + 1 ≤ N)
    (hM : q ^ N ≤ r + 1) (hr : r ≤ q ^ d + 1) : False := by
  have h1 : q ^ (d + 1) ≤ q ^ N := Nat.pow_le_pow_right (by omega) hNd
  have h2 : q ^ (d + 1) = q ^ d * q := pow_succ q d
  have h3 : 4 ≤ q ^ d := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ q ^ d := Nat.pow_le_pow_right (by omega) hd
  have h4 : q ^ d * 2 ≤ q ^ d * q := Nat.mul_le_mul_left _ hq
  omega

theorem psl_prime_le {n q r : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q) (hr : r.Prime) (hrq : ¬ r ∣ q)
    (h : r ∣ ordA (n - 1) q) : r ≤ q ^ n := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  unfold ordA at h
  rw [hn1] at h
  have hg : Nat.gcd n (q - 1) ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
    (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)))
  refine prime_le_of_dvd_prod hr (fun i hi => ?_) (prime_dvd_of_dvd_div hr hrq hg h)
  rw [Finset.mem_Icc] at hi
  refine ⟨?_, (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) hi.2)⟩
  have := Nat.one_lt_pow (by omega : i ≠ 0) (by omega : 1 < q)
  omega

theorem toNat_pow_sub_bounds {q i : ℕ} (hq : 2 ≤ q) (hi : 2 ≤ i) :
    0 < ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat ∧ ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat ≤ q ^ i + 1 := by
  have h4 : 4 ≤ q ^ i := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ q ^ i := Nat.pow_le_pow_right (by omega) hi
  have hc : ((q : ℤ) ^ i) = ((q ^ i : ℕ) : ℤ) := by push_cast; rfl
  rcases neg_one_pow_eq_or ℤ i with h1 | h1
  · rw [h1, hc]; omega
  · rw [h1, hc]; omega

theorem psu_prime_le {n q r : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q) (hr : r.Prime) (hrq : ¬ r ∣ q)
    (h : r ∣ ordTwistedA (n - 1) q) : r ≤ q ^ n + 1 := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  unfold ordTwistedA at h
  rw [hn1] at h
  have hg : Nat.gcd n (q + 1) ∣ ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    refine (Nat.gcd_dvd_right _ _).trans ((add_one_dvd_sq_sub_one q).trans ?_)
    rw [← toNat_sq_sub_neg_one_sq]
    exact Finset.dvd_prod_of_mem (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
      (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
  refine prime_le_of_dvd_prod hr (fun i hi => ?_) (prime_dvd_of_dvd_div hr hrq hg h)
  rw [Finset.mem_Icc] at hi
  obtain ⟨h1, h2⟩ := toNat_pow_sub_bounds hq hi.1
  exact ⟨h1, h2.trans (Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) hi.2) 1)⟩

theorem psp_prime_le {n q r : ℕ} (hn : 1 ≤ n) (hq : 2 ≤ q) (hr : r.Prime) (hrq : ¬ r ∣ q)
    (h : r ∣ ordBC n q) : r ≤ q ^ (2 * n) := by
  unfold ordBC at h
  have hg : Nat.gcd 2 (q - 1) ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)))
  refine prime_le_of_dvd_prod hr (fun i hi => ?_) (prime_dvd_of_dvd_div hr hrq hg h)
  rw [Finset.mem_Icc] at hi
  refine ⟨?_, (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) (by omega))⟩
  have := Nat.one_lt_pow (by omega : 2 * i ≠ 0) (by omega : 1 < q)
  omega

theorem pomegaPlus_prime_le {n q r : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q) (hr : r.Prime)
    (hrq : ¬ r ∣ q) (h : r ∣ ordD n q) : r ≤ q ^ (2 * n) + 1 := by
  unfold ordD at h
  rw [mul_assoc (q ^ (n * (n - 1)))] at h
  have hg : Nat.gcd 4 (q ^ n - 1) ∣
      (q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)
  rcases (Nat.Prime.dvd_mul hr).1 (prime_dvd_of_dvd_div hr hrq hg h) with h3 | h3
  · have hpos : 0 < q ^ n - 1 := by
      have := Nat.one_lt_pow (by omega : n ≠ 0) (by omega : 1 < q)
      omega
    exact ((Nat.le_of_dvd hpos h3).trans ((Nat.sub_le _ _).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))).trans (Nat.le_succ _)
  · refine (prime_le_of_dvd_prod hr (fun i hi => ?_) h3).trans (Nat.le_succ _)
    rw [Finset.mem_Icc] at hi
    refine ⟨?_, (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) (by omega))⟩
    have := Nat.one_lt_pow (by omega : 2 * i ≠ 0) (by omega : 1 < q)
    omega

theorem pomegaMinus_prime_le {n q r : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q) (hr : r.Prime)
    (hrq : ¬ r ∣ q) (h : r ∣ ordTwistedD n q) : r ≤ q ^ (2 * n) + 1 := by
  unfold ordTwistedD at h
  rw [mul_assoc (q ^ (n * (n - 1)))] at h
  have hg : Nat.gcd 4 (q ^ n + 1) ∣
      (q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)
  rcases (Nat.Prime.dvd_mul hr).1 (prime_dvd_of_dvd_div hr hrq hg h) with h3 | h3
  · exact (Nat.le_of_dvd (Nat.succ_pos _) h3).trans
      (Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) (by omega)) 1)
  · refine (prime_le_of_dvd_prod hr (fun i hi => ?_) h3).trans (Nat.le_succ _)
    rw [Finset.mem_Icc] at hi
    refine ⟨?_, (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) (by omega))⟩
    have := Nat.one_lt_pow (by omega : 2 * i ≠ 0) (by omega : 1 < q)
    omega

theorem tri_ge {n : ℕ} (hn : 4 ≤ n) : n + 1 ≤ (n - 1) * n / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have : k + 4 - 1 = k + 3 := by omega
  rw [this]
  nlinarith

theorem sq_ge {n : ℕ} (hn : 3 ≤ n) : 2 * n + 1 ≤ n * n := by nlinarith

theorem mul_pred_ge {n : ℕ} (hn : 4 ≤ n) : 2 * n + 1 ≤ n * (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have : k + 4 - 1 = k + 3 := by omega
  rw [this]
  nlinarith

theorem ordA_ne_psl2_of_four_le {n e r : ℕ} (hn : 4 ≤ n) (he : 1 ≤ e) (hr : r.Prime)
    (hr5 : 5 ≤ r) : ordA (n - 1) (2 ^ e) ≠ ordA 1 r := by
  intro h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨hrd, hcube⟩ := psl2_facts hodd h
  have hq : 2 ≤ 2 ^ e := two_le_two_pow he
  have hdvd : (2 ^ e) ^ ((n - 1) * n / 2) ∣ ordA (n - 1) (2 ^ e) := pow_dvd_ordA (by omega) _
  rw [← pow_mul] at hdvd
  have hM := le_succ_of_pow_two_dvd hodd (by omega) hcube hdvd
  rw [pow_mul] at hM
  exact false_of_prime_bound hq (by omega) (tri_ge hn) hM
    ((psl_prime_le (by omega) hq hr (not_dvd_two_pow hr (by omega)) hrd).trans (Nat.le_succ _))

theorem ordTwistedA_ne_psl2 {n e r : ℕ} (hn : 4 ≤ n) (he : 1 ≤ e) (hr : r.Prime)
    (hr5 : 5 ≤ r) : ordTwistedA (n - 1) (2 ^ e) ≠ ordA 1 r := by
  intro h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨hrd, hcube⟩ := psl2_facts hodd h
  have hq : 2 ≤ 2 ^ e := two_le_two_pow he
  have hdvd : (2 ^ e) ^ ((n - 1) * n / 2) ∣ ordTwistedA (n - 1) (2 ^ e) :=
    pow_dvd_ordTwistedA (by omega) _
  rw [← pow_mul] at hdvd
  have hM := le_succ_of_pow_two_dvd hodd (by omega) hcube hdvd
  rw [pow_mul] at hM
  exact false_of_prime_bound hq (by omega) (tri_ge hn) hM
    (psu_prime_le (by omega) hq hr (not_dvd_two_pow hr (by omega)) hrd)

theorem ordBC_ne_psl2_of_three_le {n e r : ℕ} (hn : 3 ≤ n) (he : 1 ≤ e) (hr : r.Prime)
    (hr5 : 5 ≤ r) : ordBC n (2 ^ e) ≠ ordA 1 r := by
  intro h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨hrd, hcube⟩ := psl2_facts hodd h
  have hq : 2 ≤ 2 ^ e := two_le_two_pow he
  have hdvd : (2 ^ e) ^ (n * n) ∣ ordBC n (2 ^ e) := pow_dvd_ordBC (by omega) _
  rw [← pow_mul] at hdvd
  have hM := le_succ_of_pow_two_dvd hodd (by omega) hcube hdvd
  rw [pow_mul] at hM
  exact false_of_prime_bound hq (by omega) (sq_ge hn) hM
    ((psp_prime_le (by omega) hq hr (not_dvd_two_pow hr (by omega)) hrd).trans (Nat.le_succ _))

theorem ordD_ne_psl2 {n e r : ℕ} (hn : 4 ≤ n) (he : 1 ≤ e) (hr : r.Prime) (hr5 : 5 ≤ r) :
    ordD n (2 ^ e) ≠ ordA 1 r := by
  intro h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨hrd, hcube⟩ := psl2_facts hodd h
  have hq : 2 ≤ 2 ^ e := two_le_two_pow he
  have hdvd : (2 ^ e) ^ (n * (n - 1)) ∣ ordD n (2 ^ e) := pow_dvd_ordD _ _
  rw [← pow_mul] at hdvd
  have hM := le_succ_of_pow_two_dvd hodd (by omega) hcube hdvd
  rw [pow_mul] at hM
  exact false_of_prime_bound hq (by omega) (mul_pred_ge hn) hM
    (pomegaPlus_prime_le (by omega) hq hr (not_dvd_two_pow hr (by omega)) hrd)

theorem ordTwistedD_ne_psl2 {n e r : ℕ} (hn : 4 ≤ n) (he : 1 ≤ e) (hr : r.Prime)
    (hr5 : 5 ≤ r) : ordTwistedD n (2 ^ e) ≠ ordA 1 r := by
  intro h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨hrd, hcube⟩ := psl2_facts hodd h
  have hq : 2 ≤ 2 ^ e := two_le_two_pow he
  have hdvd : (2 ^ e) ^ (n * (n - 1)) ∣ ordTwistedD n (2 ^ e) := pow_dvd_ordTwistedD _ _
  rw [← pow_mul] at hdvd
  have hM := le_succ_of_pow_two_dvd hodd (by omega) hcube hdvd
  rw [pow_mul] at hM
  exact false_of_prime_bound hq (by omega) (mul_pred_ge hn) hM
    (pomegaMinus_prime_le (by omega) hq hr (not_dvd_two_pow hr (by omega)) hrd)

theorem ordA_two_le (q : ℕ) : ordA 2 q ≤ q ^ 8 := by
  have hI : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  unfold ordA
  rw [hI, Finset.prod_pair (by norm_num)]
  calc q ^ (2 * (2 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd (2 + 1) (q - 1)
      ≤ q ^ (2 * (2 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.div_le_self _ _
    _ ≤ q ^ 3 * (q ^ 2 * q ^ 3) := by
        show q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ q ^ 3 * (q ^ 2 * q ^ 3)
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 8 := by ring

theorem ordBC_two_le (q : ℕ) : ordBC 2 q ≤ q ^ 10 := by
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  unfold ordBC
  rw [hI, Finset.prod_pair (by norm_num)]
  calc q ^ (2 * 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) / Nat.gcd 2 (q - 1)
      ≤ q ^ (2 * 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) := Nat.div_le_self _ _
    _ ≤ q ^ 4 * (q ^ 2 * q ^ 4) := by
        show q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) ≤ q ^ 4 * (q ^ 2 * q ^ 4)
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 10 := by ring

theorem ordG2_le (q : ℕ) : ordG2 q ≤ q ^ 14 := by
  unfold ordG2
  calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 6 * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 14 := by ring

theorem ordA_two_ne_psl2 {e r : ℕ} (he : 2 ≤ e) (hr : r.Prime) (hr5 : 5 ≤ r) :
    ordA 2 (2 ^ e) ≠ ordA 1 r := by
  intro h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨-, hcube⟩ := psl2_facts hodd h
  have hq4 : 4 ≤ 2 ^ e :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hdvd : (2 ^ e) ^ 3 ∣ ordA 2 (2 ^ e) := by
    have := pow_dvd_ordA (n := 3) (by norm_num) (2 ^ e)
    have h3 : (3 - 1) * 3 / 2 = 3 := by norm_num
    rw [h3] at this
    exact this
  rw [← pow_mul] at hdvd
  refine false_of_cube_bound hodd (by omega) hcube hdvd ?_ ?_
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (e * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h8 := ordA_two_le (2 ^ e)
    have h6 : 2 ^ (e * 3) = (2 ^ e) ^ 3 := pow_mul 2 e 3
    rw [h6]
    set q := 2 ^ e with hq
    nlinarith [Nat.mul_le_mul_right (q ^ 8) hq4]

theorem ordBC_two_ne_psl2 {e r : ℕ} (he : 1 ≤ e) (hr : r.Prime) (hr5 : 5 ≤ r) :
    ordBC 2 (2 ^ e) ≠ ordA 1 r := by
  intro h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨-, hcube⟩ := psl2_facts hodd h
  have hq : 2 ≤ 2 ^ e := two_le_two_pow he
  have hdvd : (2 ^ e) ^ 4 ∣ ordBC 2 (2 ^ e) := pow_dvd_ordBC (n := 2) (by norm_num) (2 ^ e)
  rw [← pow_mul] at hdvd
  refine false_of_cube_bound hodd (by omega) hcube hdvd ?_ ?_
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (e * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h10 := ordBC_two_le (2 ^ e)
    have h6 : 2 ^ (e * 4) = (2 ^ e) ^ 4 := pow_mul 2 e 4
    rw [h6]
    set q := 2 ^ e with hqdef
    have hq4 : 4 ≤ q ^ 2 := by nlinarith
    nlinarith [Nat.mul_le_mul_right (q ^ 10) hq4]

theorem ordG2_ne_psl2 {e r : ℕ} (he : 1 ≤ e) (hr : r.Prime) (hr5 : 5 ≤ r) :
    ordG2 (2 ^ e) ≠ ordA 1 r := by
  intro h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨-, hcube⟩ := psl2_facts hodd h
  have hq : 2 ≤ 2 ^ e := two_le_two_pow he
  have hdvd : (2 ^ e) ^ 6 ∣ ordG2 (2 ^ e) := by
    unfold ordG2
    exact ⟨((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 2 - 1), by ring⟩
  rw [← pow_mul] at hdvd
  refine false_of_cube_bound hodd (by omega) hcube hdvd ?_ ?_
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (e * 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h14 := ordG2_le (2 ^ e)
    have h6 : 2 ^ (e * 6) = (2 ^ e) ^ 6 := pow_mul 2 e 6
    rw [h6]
    set q := 2 ^ e with hqdef
    have hq4 : 4 ≤ q ^ 4 := by nlinarith [Nat.pow_le_pow_left hq 4]
    nlinarith [Nat.mul_le_mul_right (q ^ 14) hq4]

theorem prime_dvd_5616 {p : ℕ} (hp : p.Prime) (hd : p ∣ 5616) : p ∈ [2, 3, 13] := by
  have key : ∀ a e : ℕ, a.Prime → p ∣ a ^ e → p = a := fun a e ha h =>
    (Nat.prime_dvd_prime_iff_eq hp ha).1 (hp.dvd_of_dvd_pow h)
  rw [show (5616 : ℕ) = 2 ^ 4 * 3 ^ 3 * 13 ^ 1 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · simp [key 2 4 Nat.prime_two hd]
    · simp [key 3 3 Nat.prime_three hd]
  · simp [key 13 1 (by norm_num) hd]

theorem lieSearch_5616 :
    lieSearch [2, 3, 13] 5616 (fun _ _ q o => q % 2 == 1 || o != 5616) = true := by
  decide +kernel

theorem lieOrd_two_pow_ne_5616 {t : StatedLieTag} {n f : ℕ} (ht : t ∈ searchTags) (hf : 1 ≤ f)
    (hmin : lieMin t ≤ n) (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t 2 f = true) :
    lieOrd t n (2 ^ f) ≠ 5616 := by
  intro h
  have h5 := lieSearch_sound (by norm_num : (5616 : ℕ) ≠ 0) (fun _ hq hd => prime_dvd_5616 hq hd)
    lieSearch_5616 ht Nat.prime_two hf hmin hnB hadm (h ▸ dvd_rfl)
  have h2 : 2 ^ f % 2 = 0 := by
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    simp [pow_succ]
  simp [h, h2] at h5

abbrev Avoids (c : ℕ) : Prop :=
  c ≠ 5616 ∧ ∀ r : ℕ, r.Prime → 5 ≤ r → r ≠ 7 → c ≠ ordA 1 r

theorem avoids_psl {n e : ℕ} (hn : 3 ≤ n) (he : 1 ≤ e) (h3 : n = 3 → 2 ≤ e) :
    Avoids (lieOrd .PSL n (2 ^ e)) := by
  refine ⟨lieOrd_two_pow_ne_5616 (by decide) he (show 2 ≤ n by omega)
    (le_lieExp_add_one (show 2 ≤ n by omega) (by simp)) rfl, ?_⟩
  intro r hr hr5 _
  rcases Nat.lt_or_ge n 4 with h | h
  · obtain rfl : n = 3 := by omega
    exact ordA_two_ne_psl2 (h3 rfl) hr hr5
  · exact ordA_ne_psl2_of_four_le h he hr hr5

theorem avoids_psu {n e : ℕ} (hn : 4 ≤ n) (he : 1 ≤ e) :
    Avoids (lieOrd .PSU n (2 ^ e)) := by
  refine ⟨lieOrd_two_pow_ne_5616 (by decide) he (show 3 ≤ n by omega)
    (le_lieExp_add_one (show 3 ≤ n by omega) (by simp)) rfl, ?_⟩
  intro r hr hr5 _
  exact ordTwistedA_ne_psl2 hn he hr hr5

theorem avoids_psp {n e : ℕ} (hn : 2 ≤ n) (he : 1 ≤ e) :
    Avoids (lieOrd .PSp n (2 ^ e)) := by
  refine ⟨lieOrd_two_pow_ne_5616 (by decide) he (show 2 ≤ n by omega)
    (le_lieExp_add_one (show 2 ≤ n by omega) (by simp)) rfl, ?_⟩
  intro r hr hr5 _
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact ordBC_two_ne_psl2 he hr hr5
  · exact ordBC_ne_psl2_of_three_le h he hr hr5

theorem avoids_pOmegaPlus {n e : ℕ} (hn : 4 ≤ n) (he : 1 ≤ e) :
    Avoids (lieOrd .POmegaPlus n (2 ^ e)) := by
  refine ⟨lieOrd_two_pow_ne_5616 (by decide) he (show 4 ≤ n by omega)
    (le_lieExp_add_one (show 4 ≤ n by omega) (by simp)) rfl, ?_⟩
  intro r hr hr5 _
  exact ordD_ne_psl2 hn he hr hr5

theorem avoids_pOmegaMinus {n e : ℕ} (hn : 4 ≤ n) (he : 1 ≤ e) :
    Avoids (lieOrd .POmegaMinus n (2 ^ e)) := by
  refine ⟨lieOrd_two_pow_ne_5616 (by decide) he (show 4 ≤ n by omega)
    (le_lieExp_add_one (show 4 ≤ n by omega) (by simp)) rfl, ?_⟩
  intro r hr hr5 _
  exact ordTwistedD_ne_psl2 hn he hr hr5

theorem avoids_g2 {e : ℕ} (he : 1 ≤ e) : Avoids (lieOrd .G2 0 (2 ^ e)) := by
  refine ⟨lieOrd_two_pow_ne_5616 (by decide) he (Nat.zero_le _) (Nat.zero_le _) rfl, ?_⟩
  intro r hr hr5 _
  exact ordG2_ne_psl2 he hr hr5

theorem cube_le_factorial {n : ℕ} (hn : 6 ≤ n) : n ^ 3 ≤ n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    have h1 : (k + 1) ^ 2 ≤ k ^ 3 := by nlinarith
    calc (k + 1) ^ 3 = (k + 1) * (k + 1) ^ 2 := by ring
      _ ≤ (k + 1) * k ^ 3 := Nat.mul_le_mul_left _ h1
      _ ≤ (k + 1) * k.factorial := Nat.mul_le_mul_left _ ih

theorem avoids_alt {n : ℕ} (hn : 6 ≤ n) : Avoids (n.factorial / 2) := by
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hfac : 2 * (n.factorial / 2) = n.factorial := Nat.mul_div_cancel' h2
  refine ⟨?_, ?_⟩
  · intro h
    rcases Nat.lt_or_ge n 9 with h9 | h9
    · interval_cases n <;> simp [Nat.factorial] at h
    · have h1 : Nat.factorial 9 ≤ n.factorial := Nat.factorial_le h9
      have h9' : Nat.factorial 9 = 362880 := by decide
      omega
  · intro r hr hr5 _ h
    have hodd : Odd r := hr.odd_of_ne_two (by omega)
    rw [ordA_one_eq hodd] at h
    obtain ⟨hrd, hcube⟩ := psl2_facts hodd h
    have hrn : r ≤ n := (Nat.Prime.dvd_factorial hr).1 (hrd.trans (Nat.div_dvd_of_dvd h2))
    have h3 : r ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hrn 3
    have h4 := cube_le_factorial hn
    omega

theorem avoids_168 : Avoids 168 := by
  refine ⟨by norm_num, ?_⟩
  intro r hr hr5 hr7 h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨-, hcube⟩ := psl2_facts hodd h
  have hr8 : r ≤ 7 := by
    by_contra hc
    push Not at hc
    nlinarith [Nat.mul_le_mul hc hc]
  interval_cases r <;> omega

theorem avoids_6048 : Avoids 6048 := by
  refine ⟨by norm_num, ?_⟩
  intro r hr hr5 _ h
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  rw [ordA_one_eq hodd] at h
  obtain ⟨-, hcube⟩ := psl2_facts hodd h
  have hr8 : r ≤ 23 := by
    by_contra hc
    push Not at hc
    nlinarith [Nat.mul_le_mul hc hc]
  interval_cases r <;> omega

open TauCeti in
theorem avoids_of_index {S : Type} [Group S]
    (hG2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (CFSGIndex.lie ⟨.G2 q, hv⟩).Group = ordG2 q.card)
    (hrk : ¬ RankOneChevTwo S) (d : ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (e : S ≃* (CFSGIndex.lie d).Group) : Avoids (Nat.card S) := by
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | A r q =>
    change q.p = 2 at hd
    have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hnd := ((LieTypeIndex.valid_iff _).1 hv).2
    have hr1 : 1 ≤ r := hrange.1
    by_cases hr1' : r = 1
    · subst hr1'
      exact (hrk (Or.inl ⟨⟨.A 1 q, hv⟩, Or.inl ⟨q, hd, rfl⟩, ⟨e⟩⟩)).elim
    · have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hc := card_eq_lieOrd_of_classical hm
      rw [hd] at hc
      rw [hc]
      refine avoids_psl (n := r + 1) (e := q.exponent) (by omega) q.exponent_pos ?_
      intro h3
      by_contra hlt
      have he1 : q.exponent = 1 := by have := q.exponent_pos; omega
      refine hnd ((LieTypeIndex.isDuplicateRepresentative_iff _).2 ?_)
      show (r = 1 ∧ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9)) ∨ (r = 2 ∧ q.card = 2) ∨
        (r = 3 ∧ q.card = 2)
      refine Or.inr (Or.inl ⟨by omega, ?_⟩)
      rw [PrimePower.card_def, hd, he1]
      norm_num
  | twistedA r q =>
    change q.p = 2 at hd
    have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hr2 : 2 ≤ r := hrange.1
    by_cases hr2' : r = 2
    · subst hr2'
      exact (hrk (Or.inl ⟨⟨.twistedA 2 q, hv⟩, Or.inr ⟨q, hd, rfl⟩, ⟨e⟩⟩)).elim
    · have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
      have hc := card_eq_lieOrd_of_classical hm
      rw [hd] at hc
      rw [hc]
      exact avoids_psu (n := r + 1) (e := q.exponent) (by omega) q.exponent_pos
  | B r q =>
    change q.p = 2 at hd
    have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hr2 : 2 ≤ r := hrange.1
    have hm : StatedClassicalModel S .PSp r q.p q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      · exact CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
          (by omega) e
    have hc := card_eq_lieOrd_of_classical hm
    rw [hd] at hc
    rw [hc]
    exact avoids_psp (n := r) (e := q.exponent) hr2 q.exponent_pos
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have hr4 : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    have hc := card_eq_lieOrd_of_classical hm
    rw [hd] at hc
    rw [hc]
    exact avoids_pOmegaPlus hr4 q.exponent_pos
  | twistedD r q =>
    change q.p = 2 at hd
    have hr4 : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    have hc := card_eq_lieOrd_of_classical hm
    rw [hd] at hc
    rw [hc]
    exact avoids_pOmegaMinus hr4 q.exponent_pos
  | G2 q =>
    change q.p = 2 at hd
    rw [Nat.card_congr e.toEquiv, hG2 q hv hd]
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hd]
    rw [hq]
    exact avoids_g2 q.exponent_pos
  | _ => exact hd.elim

open TauCeti in
theorem avoids_of_classical {S : Type} [Group S]
    (hG2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (CFSGIndex.lie ⟨.G2 q, hv⟩).Group = ordG2 q.card)
    (h : IsClassicalTwoOrG2 S) (hrk : ¬ RankOneChevTwo S) : Avoids (Nat.card S) := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · exact avoids_of_index hG2 hrk d hd e
  · rcases hn with rfl | rfl | rfl
    · exact (hrk (Or.inr ⟨e⟩)).elim
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      exact avoids_alt (by norm_num)
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      exact avoids_alt (by norm_num)
  · obtain ⟨d1, hv⟩ := d
    rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
    · simp only at hd1
      subst hd1
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hq' : q.p ^ q.exponent = 7 := by rw [← PrimePower.card_def]; exact hq
      obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
      rw [hp7, he1] at h
      rw [card_eq_lieOrd_of_classical h]
      have h168 : lieOrd .PSL (1 + 1) (7 ^ 1) = 168 := by decide
      rw [h168]
      exact avoids_168
    · simp only at hd1
      subst hd1
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hq' : q.p ^ q.exponent = 3 := by rw [← PrimePower.card_def]; exact hq
      obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
      rw [hp3, he1] at h
      rw [card_eq_lieOrd_of_classical h]
      have h6048 : lieOrd .PSU (2 + 1) (3 ^ 1) = 6048 := by decide
      rw [h6048]
      exact avoids_6048

open TauCeti in
theorem shapeI1_avoids {S : Type} [Group S]
    (hG2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (CFSGIndex.lie ⟨.G2 q, hv⟩).Group = ordG2 q.card)
    (h : ShapeI1 S) : Avoids (Nat.card S) := by
  rcases h with ⟨hc, hrk⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact avoids_of_classical hG2 hc hrk
  · have hn6 : 6 ≤ n := by rcases hn with h | ⟨h, -⟩ <;> omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    exact avoids_alt hn6

open TauCeti in
theorem KListI1_of_G2
    (hG2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (CFSGIndex.lie ⟨.G2 q, hv⟩).Group = CFSG.Open.ordG2 q.card) :
    KListI1 := by
  intro S _ _ h
  have hav := shapeI1_avoids hG2 h
  refine ⟨?_, ?_⟩
  · rintro ⟨e⟩
    apply hav.1
    rw [Nat.card_congr e.toEquiv]
    exact card_psl_three_three
  · intro r hr hr5 hr7 hne
    obtain ⟨e⟩ := hne
    haveI : Fact r.Prime := ⟨hr⟩
    apply hav.2 r hr hr5 hr7
    rw [Nat.card_congr e.toEquiv]
    exact card_psl_two r

end KListI1Proof

section G2Card


namespace KListI1Proof

open TauCeti in
theorem card_g2_even (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p = 2) :
    Nat.card (CFSGIndex.lie ⟨.G2 q, hv⟩).Group = CFSG.Open.ordG2 q.card := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp2
    (GaloisField q.p q.exponent) hK
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, GaloisField q.p q.exponent, inferInstance,
      inferInstance, ?_, ⟨e0.symm⟩⟩
    · rw [← PrimePower.card_def]
      exact hq3
    · rw [hK, PrimePower.card_def]
  rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional hce, PrimePower.card_def]
  rfl

end KListI1Proof

theorem KListI1_holds : KListI1 :=
  KListI1Proof.KListI1_of_G2 fun q hv hp2 => KListI1Proof.card_g2_even q hv hp2

end G2Card

end CFSG.LocalAnalysis.RankThreeUC.S15
