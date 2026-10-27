module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ArithRest
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ArithLin

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.EvenSmallLie.CatalogOrders
open CFSG.ComponentClassification.CatFC.KGHS3

private theorem false_of_27_dvd {L : Type} [Group L] [Finite L]
    (h3 : (Nat.card L).factorization 3 = 2) (h : 27 ∣ Nat.card L) : False := by
  have h' : 3 ^ 3 ∣ Nat.card L := by
    simpa only [show (27 : ℕ) = 3 ^ 3 by norm_num] using h
  have hle := (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h'
  omega

private theorem dvd_div_of_factor {q E F R g : ℕ} (hgpos : 0 < g) (hg : g ∣ F) :
    R ∣ q ^ E * (F * R) / g := by
  obtain ⟨c, rfl⟩ := hg
  rw [show q ^ E * ((g * c) * R) = g * (q ^ E * (c * R)) by ring,
    Nat.mul_div_cancel_left _ hgpos]
  exact ⟨q ^ E * c, by ring⟩

private theorem three_pow_three_dvd_pow_of_three_dvd {q E : ℕ} (h : 3 ∣ q) (hE : 3 ≤ E) :
    27 ∣ q ^ E := by
  obtain ⟨k, rfl⟩ := h
  rw [mul_pow]
  exact ((show 27 ∣ 3 ^ E by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact pow_dvd_pow 3 hE)).trans (dvd_mul_right _ _)

private theorem nine_dvd_cube_sub_one {q : ℕ} (hq : q % 3 = 1) : 9 ∣ q ^ 3 - 1 := by
  have hr : q % 9 = 1 ∨ q % 9 = 4 ∨ q % 9 = 7 := by omega
  have h : q ^ 3 % 9 = 1 := by
    rcases hr with h | h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  omega

private theorem nine_dvd_cube_add_one {q : ℕ} (hq : q % 3 = 2) : 9 ∣ q ^ 3 + 1 := by
  have hr : q % 9 = 2 ∨ q % 9 = 5 ∨ q % 9 = 8 := by omega
  have h : q ^ 3 % 9 = 8 := by
    rcases hr with h | h | h <;> rw [Nat.pow_mod, h] <;> norm_num
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h]

private theorem dvd_div_of_pow_of_coprime {q E P g : ℕ} (hgX : g ∣ q ^ E * P)
    (hcop : Nat.Coprime 27 g) (hpow : 27 ∣ q ^ E) : 27 ∣ q ^ E * P / g :=
  rest_dvd_div_of_coprime hgX hcop (dvd_mul_of_dvd_left hpow P)

private theorem three_pow_three_dvd_prod_Ioc {n : ℕ} (f : ℕ → ℕ) (a b : ℕ)
    (ha : a ∈ Finset.Ioc 2 n) (hb : b ∈ Finset.Ioc 2 n) (hab : a ≠ b)
    (hda : 9 ∣ f a) (hdb : 3 ∣ f b) :
    27 ∣ ∏ i ∈ Finset.Ioc 2 n, f i := by
  have hsub : ({a, b} : Finset ℕ) ⊆ Finset.Ioc 2 n := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  have hpair : 27 ∣ f a * f b := by
    rw [show (27 : ℕ) = 9 * 3 by norm_num]
    exact mul_dvd_mul hda hdb
  have hprod : f a * f b = ∏ i ∈ ({a, b} : Finset ℕ), f i := by
    rw [Finset.prod_insert (show a ∉ ({b} : Finset ℕ) by simpa using hab),
      Finset.prod_singleton]
  rw [hprod] at hpair
  exact hpair.trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub)

private theorem dvd_ordA_of_factor {n q : ℕ} (hn : 2 ≤ n)
    (hR : 27 ∣ ∏ i ∈ Finset.Ioc 2 n, (q ^ i - 1))
    (hg : Nat.gcd n (q - 1) ∣ q ^ 2 - 1) :
    27 ∣ ordA (n - 1) q := by
  have hn1 : n - 1 + 1 = n := by omega
  have hprod : ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1)
      = (q ^ 2 - 1) * ∏ i ∈ Finset.Ioc 2 n, (q ^ i - 1) := by
    rw [← Finset.mul_prod_Ioc_eq_prod_Icc (a := 2) (b := n) (f := fun i => q ^ i - 1) hn]
  unfold ordA
  rw [hn1, hprod]
  exact hR.trans (dvd_div_of_factor (Nat.gcd_pos_of_pos_left (q - 1) (by omega)) hg)

private theorem three_pow_three_dvd_ordA_mod_one {n q : ℕ} (hn : 4 ≤ n) (hq : q % 3 = 1) :
    27 ∣ ordA (n - 1) q := by
  have hq3 : ¬ 3 ∣ q := by omega
  refine dvd_ordA_of_factor (by omega) ?_ ((Nat.gcd_dvd_right n (q - 1)).trans
    (sub_one_dvd_sq_sub_one q))
  refine three_pow_three_dvd_prod_Ioc (fun i => q ^ i - 1) 3 4
    (Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩)
    (Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩) (by norm_num) ?_ ?_
  · exact nine_dvd_cube_sub_one hq
  · exact rest_three_dvd_sq hq3 2

private theorem three_pow_three_dvd_ordA_mod_two {n q : ℕ} (hn : 6 ≤ n) (hq : q % 3 = 2) :
    27 ∣ ordA (n - 1) q := by
  have hq3 : ¬ 3 ∣ q := by omega
  refine dvd_ordA_of_factor (by omega) ?_ ((Nat.gcd_dvd_right n (q - 1)).trans
    (sub_one_dvd_sq_sub_one q))
  refine three_pow_three_dvd_prod_Ioc (fun i => q ^ i - 1) 6 4
    (Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩)
    (Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩) (by norm_num) ?_ ?_
  · exact rest_nine_dvd_six hq3
  · exact rest_three_dvd_sq hq3 2

private theorem three_pow_three_dvd_ordA_pow {n q : ℕ} (hn : 3 ≤ n) (hq1 : 1 ≤ q)
    (hpq : 3 ∣ q) : 27 ∣ ordA (n - 1) q := by
  have hn1 : n - 1 + 1 = n := by omega
  have hE : 3 ≤ (n - 1) * n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have h1 : 2 ≤ n - 1 := by omega
    have h2 : 3 ≤ n := by omega
    have h : 6 ≤ (n - 1) * n := by
      calc 6 = 2 * 3 := by norm_num
        _ ≤ (n - 1) * n := Nat.mul_le_mul h1 h2
    omega
  have hcop : Nat.Coprime 27 (Nat.gcd n (q - 1)) := by
    have hcq : Nat.Coprime q (q - 1) :=
      (Nat.coprime_self_sub_right hq1).mpr (Nat.coprime_one_right q)
    have h3c : Nat.Coprime 3 (q - 1) := hcq.coprime_dvd_left hpq
    have h27 : Nat.Coprime 27 (q - 1) := by
      rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
      exact h3c.pow_left 3
    exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right n (q - 1)) h27
  have hgX : Nat.gcd n (q - 1) ∣ q ^ ((n - 1) * n / 2) *
      (∏ i ∈ Finset.Icc 2 n, (q ^ i - 1)) := by
    refine (Nat.gcd_dvd_right n (q - 1)).trans ?_
    refine (sub_one_dvd_sq_sub_one q).trans ?_
    exact (Finset.dvd_prod_of_mem (fun i => q ^ i - 1)
      (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)).trans
      (dvd_mul_left (∏ i ∈ Finset.Icc 2 n, (q ^ i - 1)) _)
  unfold ordA
  rw [hn1]
  exact dvd_div_of_pow_of_coprime hgX hcop
    (three_pow_three_dvd_pow_of_three_dvd hpq hE)

private theorem dvd_ordTwistedA_of_factor {n q : ℕ} (hn : 2 ≤ n)
    (hR : 27 ∣ ∏ i ∈ Finset.Ioc 2 n, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
    (hg : Nat.gcd n (q + 1) ∣ q ^ 2 - 1) :
    27 ∣ ordTwistedA (n - 1) q := by
  have hn1 : n - 1 + 1 = n := by omega
  have hf2 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := toNat_sq_sub_neg_one_sq q
  have hprod : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat *
      (∏ i ∈ Finset.Ioc 2 n, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
      = ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat := by
    rw [Finset.mul_prod_Ioc_eq_prod_Icc (a := 2) (b := n)
      (f := fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) hn]
  unfold ordTwistedA
  rw [hn1, ← hprod, hf2]
  exact hR.trans (dvd_div_of_factor (Nat.gcd_pos_of_pos_left (q + 1) (by omega)) hg)

private theorem three_pow_three_dvd_ordTwistedA_mod_one {n q : ℕ} (hn : 6 ≤ n)
    (hq : q % 3 = 1) : 27 ∣ ordTwistedA (n - 1) q := by
  have hq3 : ¬ 3 ∣ q := by omega
  have hq1 : 1 ≤ q := by omega
  refine dvd_ordTwistedA_of_factor (by omega) ?_ ((Nat.gcd_dvd_right n (q + 1)).trans
    (add_one_dvd_sq_sub_one q))
  refine three_pow_three_dvd_prod_Ioc
    (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) 6 4
    (Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩)
    (Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩) (by norm_num) ?_ ?_
  · rw [arith_toNat_even hq1 (by norm_num : Even 6)]
    exact rest_nine_dvd_six hq3
  · rw [arith_toNat_even hq1 (by norm_num : Even 4)]
    exact rest_three_dvd_sq hq3 2

private theorem three_pow_three_dvd_ordTwistedA_mod_two {n q : ℕ} (hn : 4 ≤ n)
    (hq : q % 3 = 2) : 27 ∣ ordTwistedA (n - 1) q := by
  have hq3 : ¬ 3 ∣ q := by omega
  have hq1 : 1 ≤ q := by omega
  have h3 : 9 ∣ ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat := by
    have e : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
      rw [show (-1 : ℤ) ^ 3 = -1 by norm_num, sub_neg_eq_add]
      have : ((q : ℤ) ^ 3 + 1) = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    rw [e]
    exact nine_dvd_cube_add_one hq
  refine dvd_ordTwistedA_of_factor (by omega) ?_ ((Nat.gcd_dvd_right n (q + 1)).trans
    (add_one_dvd_sq_sub_one q))
  refine three_pow_three_dvd_prod_Ioc
    (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) 3 4
    (Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩)
    (Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩) (by norm_num) h3 ?_
  rw [arith_toNat_even hq1 (by norm_num : Even 4)]
  exact rest_three_dvd_sq hq3 2

private theorem three_pow_three_dvd_ordTwistedA_pow {n q : ℕ} (hn : 3 ≤ n) (hpq : 3 ∣ q) :
    27 ∣ ordTwistedA (n - 1) q := by
  have hn1 : n - 1 + 1 = n := by omega
  have hE : 3 ≤ (n - 1) * n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have h1 : 2 ≤ n - 1 := by omega
    have h2 : 3 ≤ n := by omega
    have h : 6 ≤ (n - 1) * n := by
      calc 6 = 2 * 3 := by norm_num
        _ ≤ (n - 1) * n := Nat.mul_le_mul h1 h2
    omega
  have hcop : Nat.Coprime 27 (Nat.gcd n (q + 1)) := by
    have hcq : Nat.Coprime q (q + 1) :=
      (Nat.coprime_self_add_right (m := q) (n := 1)).mpr (Nat.coprime_one_right q)
    have h3c : Nat.Coprime 3 (q + 1) := hcq.coprime_dvd_left hpq
    have h27 : Nat.Coprime 27 (q + 1) := by
      rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
      exact h3c.pow_left 3
    exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right n (q + 1)) h27
  have hmem : 2 ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hf2 : q ^ 2 - 1 = ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat :=
    (toNat_sq_sub_neg_one_sq q).symm
  have hgX : Nat.gcd n (q + 1) ∣ q ^ ((n - 1) * n / 2) *
      (∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) := by
    refine (Nat.gcd_dvd_right n (q + 1)).trans ?_
    refine (add_one_dvd_sq_sub_one q).trans ?_
    rw [hf2]
    exact (Finset.dvd_prod_of_mem (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) hmem).trans
      (dvd_mul_left (∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) _)
  unfold ordTwistedA
  rw [hn1]
  exact dvd_div_of_pow_of_coprime hgX hcop
    (three_pow_three_dvd_pow_of_three_dvd hpq hE)

private theorem three_pow_three_dvd_ordBC_pow {n q : ℕ} (hn : 2 ≤ n) (hpq : 3 ∣ q) :
    27 ∣ ordBC n q := by
  have hE : 3 ≤ n * n := by
    have h : 2 * 2 ≤ n * n := Nat.mul_le_mul hn hn
    omega
  have hpow := three_pow_three_dvd_pow_of_three_dvd hpq hE
  have h1mem : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hf1 : q - 1 ∣ q ^ (2 * 1) - 1 := by simpa using sub_one_dvd_sq_sub_one q
  have hgq : q - 1 ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    hf1.trans (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1mem)
  have hgX : Nat.gcd 2 (q - 1) ∣ q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right 2 (q - 1)).trans (hgq.trans (dvd_mul_left _ _))
  unfold ordBC
  exact rest_dvd_div_of_coprime hgX
    (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 (q - 1)) (by norm_num))
    (dvd_mul_of_dvd_left hpow _)

private theorem three_pow_three_dvd_ordBC_ne {n q : ℕ} (hn : 3 ≤ n) (hq3 : ¬ 3 ∣ q) :
    27 ∣ ordBC n q := by
  have hP : 3 ^ 4 ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    rest_pow_four_dvd_prod hn hq3
  have h1mem : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hf1 : q - 1 ∣ q ^ (2 * 1) - 1 := by simpa using sub_one_dvd_sq_sub_one q
  have hgq : q - 1 ∣ ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    hf1.trans (Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1mem)
  have hgX : Nat.gcd 2 (q - 1) ∣ q ^ (n * n) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right 2 (q - 1)).trans (hgq.trans (dvd_mul_left _ _))
  unfold ordBC
  exact rest_dvd_div_of_coprime hgX
    (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 (q - 1)) (by norm_num))
    (dvd_mul_of_dvd_right ((by norm_num : 27 ∣ 3 ^ 4).trans hP) _)

private theorem three_pow_three_dvd_ordBC_of_three_le {n q : ℕ} (hn : 3 ≤ n) :
    27 ∣ ordBC n q := by
  by_cases hq : 3 ∣ q
  · exact three_pow_three_dvd_ordBC_pow (by omega) hq
  · exact three_pow_three_dvd_ordBC_ne hn hq

private theorem three_pow_three_dvd_ordD_pow {n q : ℕ} (hn : 4 ≤ n) (hpq : 3 ∣ q) :
    27 ∣ ordD n q := by
  have hE : 3 ≤ n * (n - 1) := by
    have h1 : 2 ≤ n := by omega
    have h2 : 3 ≤ n - 1 := by omega
    have h : 2 * 3 ≤ n * (n - 1) := Nat.mul_le_mul h1 h2
    omega
  have hpow := three_pow_three_dvd_pow_of_three_dvd hpq hE
  have hcop : Nat.Coprime 27 (Nat.gcd 4 (q ^ n - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 4 (q ^ n - 1)) (by norm_num)
  have hgX : Nat.gcd 4 (q ^ n - 1) ∣
      (q ^ (n * (n - 1)) * (q ^ n - 1)) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right 4 (q ^ n - 1)).trans
      ((dvd_mul_left (q ^ n - 1) (q ^ (n * (n - 1)))).mul_right _)
  unfold ordD
  exact rest_dvd_div_of_coprime hgX hcop
    ((dvd_mul_of_dvd_left hpow (q ^ n - 1)).mul_right _)

private theorem three_pow_three_dvd_ordD_of_four_le {n q : ℕ} (hn : 4 ≤ n) :
    27 ∣ ordD n q := by
  by_cases hq : 3 ∣ q
  · exact three_pow_three_dvd_ordD_pow hn hq
  · exact (by norm_num : (27 : ℕ) ∣ 3 ^ 5).trans (three_pow_five_dvd_ordD hn hq)

private theorem three_pow_three_dvd_ordTwistedD_pow {n q : ℕ} (hn : 4 ≤ n) (hpq : 3 ∣ q) :
    27 ∣ ordTwistedD n q := by
  have hE : 3 ≤ n * (n - 1) := by
    have h1 : 2 ≤ n := by omega
    have h2 : 3 ≤ n - 1 := by omega
    have h : 2 * 3 ≤ n * (n - 1) := Nat.mul_le_mul h1 h2
    omega
  have hpow := three_pow_three_dvd_pow_of_three_dvd hpq hE
  have hcop : Nat.Coprime 27 (Nat.gcd 4 (q ^ n + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 4 (q ^ n + 1)) (by norm_num)
  have hgX : Nat.gcd 4 (q ^ n + 1) ∣
      (q ^ (n * (n - 1)) * (q ^ n + 1)) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right 4 (q ^ n + 1)).trans
      ((dvd_mul_left (q ^ n + 1) (q ^ (n * (n - 1)))).mul_right _)
  unfold ordTwistedD
  exact rest_dvd_div_of_coprime hgX hcop
    ((dvd_mul_of_dvd_left hpow (q ^ n + 1)).mul_right _)

private theorem three_pow_three_dvd_ordTwistedD_ne {n q : ℕ} (hn : 4 ≤ n) (hq3 : ¬ 3 ∣ q) :
    27 ∣ ordTwistedD n q := by
  have hP : 3 ^ 4 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    rest_pow_four_dvd_prod (by omega) hq3
  have hcop : Nat.Coprime 27 (Nat.gcd 4 (q ^ n + 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 4 (q ^ n + 1)) (by norm_num)
  have hgX : Nat.gcd 4 (q ^ n + 1) ∣
      (q ^ (n * (n - 1)) * (q ^ n + 1)) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    (Nat.gcd_dvd_right 4 (q ^ n + 1)).trans
      ((dvd_mul_left (q ^ n + 1) (q ^ (n * (n - 1)))).mul_right _)
  unfold ordTwistedD
  exact rest_dvd_div_of_coprime hgX hcop
    (((by norm_num : 27 ∣ 3 ^ 4).trans hP).mul_left (q ^ (n * (n - 1)) * (q ^ n + 1)))

private theorem three_pow_three_dvd_ordTwistedD_of_four_le {n q : ℕ} (hn : 4 ≤ n) :
    27 ∣ ordTwistedD n q := by
  by_cases hq : 3 ∣ q
  · exact three_pow_three_dvd_ordTwistedD_pow hn hq
  · exact three_pow_three_dvd_ordTwistedD_ne hn hq

theorem classical_config {L : Type} [Group L] [Finite L] {t : StatedLieTag} {n p f : ℕ}
    (hM : StatedClassicalModel L t n p f) (h3 : (Nat.card L).factorization 3 = 2) :
    (t = .PSL ∧ (n = 2 ∨ n = 3 ∨ ((n = 4 ∨ n = 5) ∧ p ≠ 3 ∧ p ^ f % 3 = 2))) ∨
      (t = .PSU ∧ (n = 3 ∨ ((n = 4 ∨ n = 5) ∧ p ≠ 3 ∧ p ^ f % 3 = 1))) ∨
      (t = .PSp ∧ n = 2 ∧ p ≠ 3) := by
  have hcard : Nat.card L = lieOrd t n (p ^ f) := card_eq_lieOrd_of_classical hM
  obtain ⟨hadm, hrest⟩ := hM
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow f p hp.pos
  have htri : (p ^ f) % 3 = 0 ∨ (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 := by
    have := Nat.mod_lt (p ^ f) (by norm_num : 0 < 3)
    omega
  cases t
  ·
    left
    refine ⟨rfl, ?_⟩
    have hn2 : 2 ≤ n := hadm.2.2.1
    by_cases h2 : n = 2
    · exact Or.inl h2
    by_cases h3n : n = 3
    · exact Or.inr (Or.inl h3n)
    right; right
    have hn4 : 4 ≤ n := by omega
    refine ⟨?_, ?_, ?_⟩
    · by_contra hn45
      push_neg at hn45
      exact (false_of_27_dvd h3) (by
        rw [hcard]
        change 27 ∣ ordA (n - 1) (p ^ f)
        rcases htri with h0 | h1 | h2
        · exact three_pow_three_dvd_ordA_pow (by omega) hq1 (Nat.dvd_iff_mod_eq_zero.mpr h0)
        · exact three_pow_three_dvd_ordA_mod_one (by omega) h1
        · exact three_pow_three_dvd_ordA_mod_two (by omega) h2)
    · intro hp3
      have hpq : 3 ∣ p ^ f := by rw [hp3]; exact dvd_pow_self 3 (by omega)
      exact (false_of_27_dvd h3) (by
        rw [hcard]
        change 27 ∣ ordA (n - 1) (p ^ f)
        exact three_pow_three_dvd_ordA_pow (by omega) hq1 hpq)
    · by_contra hne
      rcases htri with h0 | h1 | h2
      · exact (false_of_27_dvd h3) (by
          rw [hcard]
          change 27 ∣ ordA (n - 1) (p ^ f)
          exact three_pow_three_dvd_ordA_pow (by omega) hq1 (Nat.dvd_iff_mod_eq_zero.mpr h0))
      · exact (false_of_27_dvd h3) (by
          rw [hcard]
          change 27 ∣ ordA (n - 1) (p ^ f)
          exact three_pow_three_dvd_ordA_mod_one (by omega) h1)
      · exact absurd h2 hne
  ·
    right; left
    refine ⟨rfl, ?_⟩
    have hn3 : 3 ≤ n := hadm.2.2.1
    by_cases h3n : n = 3
    · exact Or.inl h3n
    right
    have hn4 : 4 ≤ n := by omega
    refine ⟨?_, ?_, ?_⟩
    · by_contra hn45
      push_neg at hn45
      exact (false_of_27_dvd h3) (by
        rw [hcard]
        change 27 ∣ ordTwistedA (n - 1) (p ^ f)
        rcases htri with h0 | h1 | h2
        · exact three_pow_three_dvd_ordTwistedA_pow (by omega) (Nat.dvd_iff_mod_eq_zero.mpr h0)
        · exact three_pow_three_dvd_ordTwistedA_mod_one (by omega) h1
        · exact three_pow_three_dvd_ordTwistedA_mod_two (by omega) h2)
    · intro hp3
      have hpq : 3 ∣ p ^ f := by rw [hp3]; exact dvd_pow_self 3 (by omega)
      exact (false_of_27_dvd h3) (by
        rw [hcard]
        change 27 ∣ ordTwistedA (n - 1) (p ^ f)
        exact three_pow_three_dvd_ordTwistedA_pow (by omega) hpq)
    · by_contra hne
      rcases htri with h0 | h1 | h2
      · exact (false_of_27_dvd h3) (by
          rw [hcard]
          change 27 ∣ ordTwistedA (n - 1) (p ^ f)
          exact three_pow_three_dvd_ordTwistedA_pow (by omega) (Nat.dvd_iff_mod_eq_zero.mpr h0))
      · exact absurd h1 hne
      · exact (false_of_27_dvd h3) (by
          rw [hcard]
          change 27 ∣ ordTwistedA (n - 1) (p ^ f)
          exact three_pow_three_dvd_ordTwistedA_mod_two (by omega) h2)
  ·
    right; right
    have hn2 : 2 ≤ n := hadm.2.2.1
    refine ⟨rfl, ?_, ?_⟩
    · by_contra hn2ne
      exact (false_of_27_dvd h3) (by
        rw [hcard]
        change 27 ∣ ordBC n (p ^ f)
        exact three_pow_three_dvd_ordBC_of_three_le (by omega))
    · intro hp3
      have hpq : 3 ∣ p ^ f := by rw [hp3]; exact dvd_pow_self 3 (by omega)
      exact (false_of_27_dvd h3) (by
        rw [hcard]
        change 27 ∣ ordBC n (p ^ f)
        exact three_pow_three_dvd_ordBC_pow hn2 hpq)
  ·
    exact (false_of_27_dvd h3 (by
      rw [hcard]
      change 27 ∣ ordBC n (p ^ f)
      exact three_pow_three_dvd_ordBC_of_three_le hadm.2.2.1)).elim
  ·
    exact (false_of_27_dvd h3 (by
      rw [hcard]
      change 27 ∣ ordD n (p ^ f)
      exact three_pow_three_dvd_ordD_of_four_le hadm.2.2)).elim
  ·
    exact (false_of_27_dvd h3 (by
      rw [hcard]
      change 27 ∣ ordTwistedD n (p ^ f)
      exact three_pow_three_dvd_ordTwistedD_of_four_le hadm.2.2)).elim
  all_goals exact hrest.elim

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3
