module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36OddChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRecog

public section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.HarrisLit.N36.OddChar

theorem three_mul_psl_lt {Q n : ℕ} (hQ : 3 ≤ Q) (hn : 3 ≤ n) :
    3 * (Q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (Q ^ i - 1)) <
      Q ^ (3 * (n * (n - 1) / 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ih := psl_lt (Q := Q) (by omega) (show 2 ≤ m by omega)
  rw [Finset.prod_Icc_succ_top (by omega), Nat.triangle_succ]
  calc 3 * (Q ^ (m * (m - 1) / 2 + m) * ((∏ i ∈ Finset.Icc 2 m, (Q ^ i - 1)) * (Q ^ (m + 1) - 1)))
      = (3 * (Q ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 2 m, (Q ^ i - 1))) *
          (Q ^ m * (Q ^ (m + 1) - 1)) := by rw [pow_add]; ring
    _ < (3 * Q ^ (3 * (m * (m - 1) / 2))) * (Q ^ m * Q ^ (m + 1)) :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.mul_lt_mul_of_pos_left ih (by norm_num))
          (Nat.mul_le_mul_left _ (pow_sub_one_le _)) (by positivity)
    _ ≤ (Q * Q ^ (3 * (m * (m - 1) / 2))) * (Q ^ m * Q ^ (m + 1)) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hQ)
    _ = Q ^ (3 * (m * (m - 1) / 2) + (2 * m + 2)) := by ring
    _ ≤ Q ^ (3 * (m * (m - 1) / 2 + m)) := Nat.pow_le_pow_right (by omega) (by omega)

theorem three_mul_psu_lt {Q n : ℕ} (hQ : 3 ≤ Q) (hn : 3 ≤ n) :
    3 * (Q ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then Q ^ i - 1 else Q ^ i + 1)) <
      Q ^ (3 * (n * (n - 1) / 2)) := by
  have hQ0 : 0 < Q := by omega
  rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
  · rw [show (3 : ℕ) * (3 - 1) / 2 = 3 by norm_num, show (3 : ℕ) = 2 + 1 by rfl,
      Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]
    have h2 : Even 2 := even_two
    have h3 : ¬ Even (2 + 1) := by decide
    rw [ite_eq_left h2, ite_eq_right h3]
    have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ0
    have hlt : (Q ^ 2 - 1) * (Q ^ (2 + 1) + 1) < Q ^ 5 := by
      have hQ2 : Q ^ 2 ≤ Q ^ (2 + 1) := Nat.pow_le_pow_right hQ0 (by norm_num)
      have hQ5 : Q ^ 5 = Q ^ 2 * Q ^ (2 + 1) := by ring
      obtain ⟨a, ha⟩ : ∃ a, Q ^ 2 = a + 1 := ⟨Q ^ 2 - 1, by omega⟩
      rw [hQ5, ha, Nat.add_sub_cancel]
      nlinarith
    calc 3 * (Q ^ (2 + 1) * ((Q ^ 2 - 1) * (Q ^ (2 + 1) + 1)))
        < 3 * (Q ^ (2 + 1) * Q ^ 5) :=
          Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hlt (by positivity))
            (by norm_num)
      _ ≤ Q * (Q ^ (2 + 1) * Q ^ 5) := Nat.mul_le_mul_right _ hQ
      _ = Q ^ (3 * (2 + 1)) := by ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ih := psu_lt (Q := Q) (by omega) (show 3 ≤ m by omega)
    have hg : (if Even (m + 1) then Q ^ (m + 1) - 1 else Q ^ (m + 1) + 1) ≤ Q ^ (m + 2) := by
      split_ifs
      · exact (pow_sub_one_le _).trans (Nat.pow_le_pow_right hQ0 (by omega))
      · exact pow_add_one_le_pow_succ (by omega) (m + 1)
    rw [Finset.prod_Icc_succ_top (by omega), Nat.triangle_succ]
    calc 3 * (Q ^ (m * (m - 1) / 2 + m) * ((∏ i ∈ Finset.Icc 2 m,
          (if Even i then Q ^ i - 1 else Q ^ i + 1)) *
          (if Even (m + 1) then Q ^ (m + 1) - 1 else Q ^ (m + 1) + 1)))
        = (3 * (Q ^ (m * (m - 1) / 2) *
            ∏ i ∈ Finset.Icc 2 m, (if Even i then Q ^ i - 1 else Q ^ i + 1))) *
            (Q ^ m * (if Even (m + 1) then Q ^ (m + 1) - 1 else Q ^ (m + 1) + 1)) := by
          rw [pow_add]; ring
      _ < (3 * Q ^ (3 * (m * (m - 1) / 2))) * (Q ^ m * Q ^ (m + 2)) :=
          Nat.mul_lt_mul_of_lt_of_le (Nat.mul_lt_mul_of_pos_left ih (by norm_num))
            (Nat.mul_le_mul_left _ hg) (by positivity)
      _ ≤ (Q * Q ^ (3 * (m * (m - 1) / 2))) * (Q ^ m * Q ^ (m + 2)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hQ)
      _ = Q ^ (3 * (m * (m - 1) / 2) + (2 * m + 3)) := by ring
      _ ≤ Q ^ (3 * (m * (m - 1) / 2 + m)) := Nat.pow_le_pow_right hQ0 (by omega)

theorem three_mul_psp_lt {Q n : ℕ} (hQ : 3 ≤ Q) (hn : 2 ≤ n) :
    3 * (Q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1)) < Q ^ (3 * n ^ 2) := by
  have hQ0 : 0 < Q := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ih := psp_lt (Q := Q) (by omega) (show 1 ≤ m by omega)
  rw [Finset.prod_Icc_succ_top (by omega)]
  calc 3 * (Q ^ ((m + 1) ^ 2) * ((∏ i ∈ Finset.Icc 1 m, (Q ^ (2 * i) - 1)) *
        (Q ^ (2 * (m + 1)) - 1)))
      = (3 * (Q ^ (m ^ 2) * ∏ i ∈ Finset.Icc 1 m, (Q ^ (2 * i) - 1))) *
          (Q ^ (2 * m + 1) * (Q ^ (2 * (m + 1)) - 1)) := by
        rw [show (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) by ring, pow_add]; ring
    _ < (3 * Q ^ (3 * m ^ 2)) * (Q ^ (2 * m + 1) * Q ^ (2 * (m + 1))) :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.mul_lt_mul_of_pos_left ih (by norm_num))
          (Nat.mul_le_mul_left _ (pow_sub_one_le _)) (by positivity)
    _ ≤ (Q * Q ^ (3 * m ^ 2)) * (Q ^ (2 * m + 1) * Q ^ (2 * (m + 1))) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hQ)
    _ = Q ^ (3 * m ^ 2 + (4 * m + 4)) := by ring
    _ ≤ Q ^ (3 * (m + 1) ^ 2) := Nat.pow_le_pow_right hQ0 (by nlinarith)

theorem three_mul_omega_lt {Q n c : ℕ} (hQ : 3 ≤ Q) (hn : 4 ≤ n) (hc : c ≤ Q ^ (n + 1)) :
    3 * (Q ^ (n * (n - 1)) * c * ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) <
      Q ^ (3 * (n * (n - 1))) := by
  have hQ0 : 0 < Q := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hP := lt_pow_two_mul_of_lt (psp_lt (Q := Q) (by omega) (n := m) (by omega))
  calc 3 * (Q ^ ((m + 1) * m) * c * ∏ i ∈ Finset.Icc 1 m, (Q ^ (2 * i) - 1))
      ≤ 3 * (Q ^ ((m + 1) * m + (m + 1 + 1)) * ∏ i ∈ Finset.Icc 1 m, (Q ^ (2 * i) - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (mul_le_pow_add le_rfl hc))
    _ < 3 * (Q ^ ((m + 1) * m + (m + 1 + 1)) * Q ^ (2 * m ^ 2)) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hP (by positivity)) (by norm_num)
    _ ≤ Q * (Q ^ ((m + 1) * m + (m + 1 + 1)) * Q ^ (2 * m ^ 2)) := Nat.mul_le_mul_right _ hQ
    _ = Q ^ ((m + 1) * m + (m + 1 + 1) + 2 * m ^ 2 + 1) := by ring
    _ ≤ Q ^ (3 * ((m + 1) * m)) := Nat.pow_le_pow_right hQ0 (by nlinarith)

theorem three_mul_numerator_lt {t : StatedLieTag} {m p e : ℕ}
    (ht : CatLeafProof.X10Lin.IsClassicalTag t) (hrank : t = .PSL → 3 ≤ m)
    (hadm : StatedLieAdmissible t m p e) (hp2 : p ≠ 2) :
    3 * lieOrderNumerator t m (p ^ e) < (p ^ e) ^ (3 * lieSylowExponent t m) := by
  have hp : p.Prime := hadm.1
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hQ3 : 3 ≤ p ^ e := hp3.trans (Nat.le_self_pow (by have := hadm.2.1; omega) p)
  obtain ⟨-, -, hcase⟩ := hadm
  generalize p ^ e = Q at hQ3 ⊢
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact three_mul_psl_lt hQ3 (hrank rfl)
  · exact three_mul_psu_lt hQ3 hcase.1
  · exact three_mul_psp_lt hQ3 hcase.1
  · exact three_mul_psp_lt hQ3 (by have := hcase.1; omega)
  · simp only [lieOrderNumerator, lieSylowExponent]
    exact three_mul_omega_lt hQ3 hcase
      ((pow_sub_one_le m).trans (Nat.pow_le_pow_right (by omega) (by omega)))
  · simp only [lieOrderNumerator, lieSylowExponent]
    exact three_mul_omega_lt hQ3 hcase (pow_add_one_le_pow_succ (by omega) m)

theorem false_of_pslTwo_of_classical {X : Type} [Group X] {t : StatedLieTag} {m p e f : ℕ}
    (hp2 : p ≠ 2) (ht : CatLeafProof.X10Lin.IsClassicalTag t) (hrank : t = .PSL → 3 ≤ m)
    (hadm : StatedLieAdmissible t m p e) (h : Blueprint.LieModel X t m p e)
    (hX : Blueprint.LieModel X .PSL 2 p f) : False := by
  have hp : p.Prime := hadm.1
  have hm0 : m ≠ 0 := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (obtain ⟨-, -, hc⟩ := hadm; omega)
  obtain ⟨h1, h1p⟩ := CatLeafProof.X10Lin.lieOrder_of_lieModel_classical ht hp2 hm0 h
  obtain ⟨h2, h2p⟩ :=
    CatLeafProof.X10Lin.lieOrder_of_lieModel_classical (Or.inl rfl) hp2 (by norm_num) hX
  have hfe : f = lieSylowExponent t m * e := by
    have h3 := h2p.symm.trans h1p
    simpa [lieSylowExponent] using h3
  have hbound := three_mul_numerator_lt ht hrank hadm hp2
  set Q := p ^ e with hQ
  set N := lieSylowExponent t m with hN
  have hq : p ^ f = Q ^ N := by rw [hfe, mul_comm, pow_mul]
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hgcd : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨i, hi⟩ := hodd
    rw [hi, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left ⟨i, rfl⟩
  have h2' : Nat.card X * 2 = p ^ f * ((p ^ f) ^ 2 - 1) := by
    have h3 := h2
    simp only [lieOrderDivisor, lieOrderNumerator, show (2 : ℕ) * (2 - 1) / 2 = 1 by rfl,
      pow_one, Finset.Icc_self, Finset.prod_singleton] at h3
    rwa [hgcd] at h3
  have hdiv := divisor_pos (t := t) (n := m) (Q := Q)
    (show 2 ≤ Q by have := hp.two_le; exact this.trans (Nat.le_self_pow
      (by have := hadm.2.1; omega) p))
  have hle : Nat.card X ≤ lieOrderNumerator t m Q := by
    rw [← h1]
    exact Nat.le_mul_of_pos_right _ hdiv
  have hcube : (Q ^ N) ^ 3 = Q ^ (3 * N) := by rw [← pow_mul, mul_comm]
  rw [← hcube, ← hq] at hbound
  have hq3 : 3 ≤ p ^ f := by
    have := hp.two_le
    have hf : 1 ≤ f := (N36.admissible_of_lieModel' hX).2.1
    have h3 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hp3 : 3 ≤ p := by omega
    omega
  generalize p ^ f = q at hq3 h2' hbound
  generalize Nat.card X = x at h2' hle
  have hsq : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨r, hr⟩ : ∃ r, q ^ 2 = r + 1 := ⟨q ^ 2 - 1, by omega⟩
  rw [hr, Nat.add_sub_cancel] at h2'
  have hq3' : q ^ 3 = q * (r + 1) := by rw [← hr]; ring
  rw [hq3'] at hbound
  have hr8 : 8 ≤ r := by nlinarith
  nlinarith

end CFSG.ComponentClassification.HarrisLit.L35
