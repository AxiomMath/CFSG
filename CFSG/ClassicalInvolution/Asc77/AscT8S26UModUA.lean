module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26UModLA
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem s26U_root_props [Finite K] (hodd : Odd (Nat.card K)) (hq1 : p ^ f % 4 = 1) {n : ℕ}
    (hn : 1 ≤ n) {a b c d : K} (hdet : a * d - b * c = 1) (ha : h.bar a = d)
    (hneg : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) ^ 2 ^ n = -1) {l : K}
    (hl : l ^ 2 - (a + d) * l + 1 = 0) : l ^ 2 ^ n = -1 ∧ h.bar l = l := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hdet' : ((!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) -
      l • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
    rw [Matrix.det_fin_two]
    simp
    linear_combination hl + hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
  have hAv : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) *ᵥ v = l • v := by
    have h1 := hv
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h1
    exact h1
  have hpow : ∀ k : ℕ, (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) ^ k *ᵥ v = l ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have hy := hpow (2 ^ n)
  rw [hneg] at hy
  simp only [neg_mulVec, one_mulVec] at hy
  have hl2 : (l ^ 2 ^ n + 1) • v = 0 := by
    rw [add_smul, one_smul, ← hy]
    simp
  have hl2' : l ^ 2 ^ n = -1 := by
    rcases smul_eq_zero.mp hl2 with h' | h'
    · linear_combination h'
    · exact absurd h' hv0
  refine ⟨hl2', ?_⟩
  have hd : h.bar d = a := by rw [← ha, h.bar_bar]
  have hbl : (h.bar l) ^ 2 - (a + d) * h.bar l + 1 = 0 := by
    have := congrArg h.bar hl
    simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero, ha, hd] at this
    linear_combination this
  have hprod : (h.bar l - l) * (h.bar l - ((a + d) - l)) = 0 := by linear_combination hbl - hl
  rcases mul_eq_zero.mp hprod with h' | h'
  · linear_combination h'
  ·
    have hbar : h.bar l = (a + d) - l := by linear_combination h'
    have hll : l * h.bar l = 1 := by rw [hbar]; linear_combination -hl
    by_contra hne
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at hll
    have hlq : l ^ (p ^ f + 1) = 1 := by
      rw [pow_succ', ← h.bar_apply]
      exact hll
    have h2' : (1 : K) ≠ -1 := by
      intro h'
      apply h2
      linear_combination h'
    let u : Kˣ := Units.mk0 l hl0
    have hu1 : u ^ 2 ^ n ≠ 1 := by
      intro h'
      have h'' : l ^ 2 ^ n = 1 := by
        have := congrArg (fun x : Kˣ => (x : K)) h'
        simpa [u] using this
      rw [hl2'] at h''
      exact h2' h''.symm
    have hu2 : u ^ 2 ^ (n + 1) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      show l ^ 2 ^ (n + 1) = 1
      rw [pow_succ, pow_mul, hl2']
      norm_num
    have hord : orderOf u = 2 ^ (n + 1) := orderOf_eq_prime_pow hu1 hu2
    have hu3 : u ^ (p ^ f + 1) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      exact hlq
    have hdvd : 2 ^ (n + 1) ∣ p ^ f + 1 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hu3
    have h4 : 4 ∣ 2 ^ (n + 1) := by
      have := pow_dvd_pow 2 (show 2 ≤ n + 1 by omega)
      simpa using this
    have h4' := h4.trans hdvd
    omega


theorem s26U_exists_root [Finite K] (hodd : Odd (Nat.card K)) {a d : K}
    (ha : h.bar a = d) : ∃ l : K, l ^ 2 - (a + d) * l + 1 = 0 := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have h4 : (4 : K) ≠ 0 := by
    have := mul_ne_zero h2 h2
    norm_num at this
    exact this
  have hd : h.bar d = a := by rw [← ha, h.bar_bar]
  have hδ : h.bar ((a + d) ^ 2 - 4) = (a + d) ^ 2 - 4 := by
    simp only [map_sub, map_pow, map_add, ha, hd, map_ofNat]
    ring
  have hsq : IsSquare ((a + d) ^ 2 - 4) := by
    by_cases h0 : (a + d) ^ 2 - 4 = 0
    · exact ⟨0, by simp [h0]⟩
    · have : Fact p.Prime := ⟨h.prime⟩
      have : CharP K p := h.charP
      have := Fintype.ofFinite K
      have hchar : ringChar K ≠ 2 := by
        intro h'
        have h5 : ((2 : ℕ) : K) = 0 := by
          rw [← h']
          exact ringChar.Nat.cast_ringChar
        exact h2 (by simpa using h5)
      rw [FiniteField.isSquare_iff hchar h0]
      have hq : Odd (p ^ f) := by
        have hcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
        rw [hcard, pow_two] at hodd
        exact (Nat.odd_mul.mp hodd).1
      obtain ⟨j, hj⟩ := hq
      have hpow : ((a + d) ^ 2 - 4) ^ (p ^ f) = (a + d) ^ 2 - 4 := by
        rw [← h.bar_apply]
        exact hδ
      have h1 : ((a + d) ^ 2 - 4) ^ (2 * j) = 1 := by
        have h' : ((a + d) ^ 2 - 4) * ((a + d) ^ 2 - 4) ^ (2 * j) = ((a + d) ^ 2 - 4) * 1 := by
          rw [← pow_succ', mul_one, ← hj]
          exact hpow
        exact mul_left_cancel₀ h0 h'
      have hcard : Fintype.card K / 2 = (2 * j) * (j + 1) := by
        rw [← Nat.card_eq_fintype_card, h.card, pow_mul' p 2 f, hj]
        ring_nf
        omega
      rw [hcard, pow_mul, h1, one_pow]
  obtain ⟨s, hs⟩ := hsq
  have hl2 : 2 * ((a + d + s) / 2) = a + d + s := by field_simp
  refine ⟨(a + d + s) / 2, ?_⟩
  have h0 : 4 * (((a + d + s) / 2) ^ 2 - (a + d) * ((a + d + s) / 2) + 1) = 0 := by
    linear_combination (2 * ((a + d + s) / 2) + (a + d + s) - 2 * (a + d)) * hl2 - hs
  exact (mul_eq_zero.mp h0).resolve_left h4


theorem s26U_split_data [Finite K] (hodd : Odd (Nat.card K)) (hq1 : p ^ f % 4 = 1) {n : ℕ}
    (hn : 1 ≤ n) {a b c d : K} (hdet : a * d - b * c = 1) (ha : h.bar a = d)
    (hneg : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) ^ 2 ^ n = -1) :
    ∃ s₀ : K, h.bar s₀ = s₀ ∧ s₀ ^ 2 = (a - d) ^ 2 + 4 * (b * c) ∧ s₀ ≠ 0 ∧
      (b ≠ 0 ∨ c ≠ 0) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have h2' : (1 : K) ≠ -1 := by
    intro h'
    apply h2
    linear_combination h'
  have hd : h.bar d = a := by rw [← ha, h.bar_bar]
  obtain ⟨l, hl⟩ := s26U_exists_root h hodd ha
  obtain ⟨hl2, hbl⟩ := s26U_root_props h hodd hq1 hn hdet ha hneg hl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨2 * l - (a + d), ?_, ?_, ?_, ?_⟩
  · simp only [map_sub, map_mul, map_add, ha, hd, hbl, map_ofNat]
    ring
  · linear_combination 4 * hl + 4 * hdet
  · intro h0
    have h3 : l ^ 2 = 1 := by
      have : 2 * l = a + d := by linear_combination h0
      have h5 : l ^ 2 - 2 * l * l + 1 = 0 := by rw [this]; linear_combination hl
      linear_combination -h5
    apply h2'
    rw [pow_succ', pow_mul, h3, one_pow] at hl2
    exact hl2
  · by_contra hnd
    push Not at hnd
    obtain ⟨hb0, hc0⟩ := hnd
    have hda : a * d = 1 := by rw [hb0, hc0] at hdet; linear_combination hdet
    have hroot : a ^ 2 - (a + d) * a + 1 = 0 := by linear_combination -hda
    obtain ⟨ha2, hba⟩ := s26U_root_props h hodd hq1 hn hdet ha hneg hroot
    have hdd : d = a := by rw [← ha]; exact hba
    apply h2'
    have h3 : a ^ 2 = 1 := by rw [hdd] at hda; linear_combination hda
    rw [pow_succ', pow_mul, h3, one_pow] at ha2
    exact ha2


theorem s26_commutant_U (h2 : (2 : K) ≠ 0) {a b c d e g w k m s₀ : K}
    (ha : h.bar a = d) (hb : h.bar b = -c) (hs₀ : h.bar s₀ = s₀)
    (hs₀sq : s₀ ^ 2 = (a - d) ^ 2 + 4 * (b * c)) (hs₀0 : s₀ ≠ 0) (hnd : b ≠ 0 ∨ c ≠ 0)
    (hNm : h.bar m * m = 1) (C1 : b * w = c * g) (C2 : (a - d) * g + b * (k - e) = 0)
    (C3 : c * (e - k) + (d - a) * w = 0) (B1 : e ^ 2 + g * w = m ^ 2) (B3 : w * (e + k) = 0)
    (U11 : h.bar e * e + h.bar w * w = 1) (U21 : h.bar g * e + h.bar k * w = 0) :
    g = 0 ∧ w = 0 ∧ e = k ∧ (e = m ∨ e = -m) := by
  have h8 : (8 : K) ≠ 0 := by
    have := mul_ne_zero (mul_ne_zero h2 h2) h2
    norm_num at this
    exact this
  have hd : h.bar d = a := by rw [← ha, h.bar_bar]
  have hc : h.bar c = -b := by
    have := congrArg h.bar hb
    rw [h.bar_bar, map_neg] at this
    linear_combination this
  have hbs : h.bar (a - d) = -(a - d) := by
    rw [map_sub, ha, hd]
    ring
  by_cases hek : e + k = 0
  ·
    exfalso
    have hk : k = -e := by linear_combination hek
    subst hk
    have F2 : (a - d) * g = 2 * b * e := by linear_combination C2
    have F1 : (a - d) * w = 2 * c * e := by linear_combination -C3
    have F4 : (a - d) * h.bar g = 2 * c * h.bar e := by
      have := congrArg h.bar F2
      simp only [map_mul, hbs, hb, map_ofNat] at this
      linear_combination -this
    have F3 : (a - d) * h.bar w = 2 * b * h.bar e := by
      have := congrArg h.bar F1
      simp only [map_mul, hbs, hc, map_ofNat] at this
      linear_combination -this
    by_cases hs : a - d = 0
    · have hbe : b * e = 0 := by
        have : 2 * (b * e) = 0 := by linear_combination -F2 + g * hs
        exact (mul_eq_zero.mp this).resolve_left h2
      have hce : c * e = 0 := by
        have : 2 * (c * e) = 0 := by linear_combination -F1 + w * hs
        exact (mul_eq_zero.mp this).resolve_left h2
      by_cases he : e = 0
      · subst he
        simp only [map_zero, zero_mul, zero_add] at U11
        have hs₀sq' : s₀ ^ 2 = 4 * (b * c) := by rw [hs₀sq, hs]; ring
        have hgw : g * w = m ^ 2 := by linear_combination B1
        have e1 : (2 * b * w) ^ 2 = (s₀ * m) ^ 2 := by
          linear_combination 4 * (b * w) * C1 + 4 * b * c * hgw - m ^ 2 * hs₀sq'
        have hbc0 : b * c = 0 := by
          have key : 8 * (b * c) = 0 := by
            rcases sq_eq_sq_iff_eq_or_eq_neg.mp e1 with h1 | h1
            · have h1b := congrArg h.bar h1
              simp only [map_mul, hs₀, hb, map_ofNat] at h1b
              linear_combination (2 * c * h.bar w) * h1 - (s₀ * m) * h1b - (4 * b * c) * U11
                - s₀ ^ 2 * hNm - hs₀sq'
            · have h1b := congrArg h.bar h1
              simp only [map_mul, map_neg, hs₀, hb, map_ofNat] at h1b
              linear_combination (2 * c * h.bar w) * h1 + (s₀ * m) * h1b - (4 * b * c) * U11
                - s₀ ^ 2 * hNm - hs₀sq'
          exact (mul_eq_zero.mp key).resolve_left h8
        apply hs₀0
        have : s₀ ^ 2 = 0 := by rw [hs₀sq', hbc0]; ring
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      · rcases hnd with hb0 | hc0
        · exact hb0 ((mul_eq_zero.mp hbe).resolve_right he)
        · exact hc0 ((mul_eq_zero.mp hce).resolve_right he)
    · have N1 : h.bar e * e * s₀ ^ 2 = (a - d) ^ 2 := by
        rw [hs₀sq]
        linear_combination (a - d) ^ 2 * U11 - ((a - d) * h.bar w) * F1 - (2 * c * e) * F3
      have N2 : e ^ 2 * s₀ ^ 2 = (a - d) ^ 2 * m ^ 2 := by
        rw [hs₀sq]
        linear_combination (a - d) ^ 2 * B1 - (2 * b * e) * F1 - ((a - d) * w) * F2
      have e1 : (e * s₀) ^ 2 = ((a - d) * m) ^ 2 := by linear_combination N2
      have hs2 : 2 * (a - d) ^ 2 = 0 := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp e1 with h1 | h1
        · have h1b := congrArg h.bar h1
          simp only [map_mul, hs₀, hbs] at h1b
          linear_combination (h.bar e * s₀) * h1 + ((a - d) * m) * h1b - N1 - (a - d) ^ 2 * hNm
        · have h1b := congrArg h.bar h1
          simp only [map_mul, map_neg, hs₀, hbs] at h1b
          linear_combination (h.bar e * s₀) * h1 - ((a - d) * m) * h1b - N1 - (a - d) ^ 2 * hNm
      have : (a - d) ^ 2 = 0 := (mul_eq_zero.mp hs2).resolve_left h2
      exact hs (pow_eq_zero_iff two_ne_zero |>.mp this)
  · have hw : w = 0 := (mul_eq_zero.mp B3).resolve_right hek
    subst hw
    simp only [map_zero, mul_zero, add_zero] at U11 U21
    have he0 : e ≠ 0 := by
      intro he
      rw [he] at U11
      simp at U11
    have hg : g = 0 := by
      have hbg : h.bar g = 0 := (mul_eq_zero.mp U21).resolve_right he0
      have := congrArg h.bar hbg
      rw [h.bar_bar, map_zero] at this
      exact this
    subst hg
    have hek' : e = k := by
      rcases hnd with hb0 | hc0
      · have : b * (k - e) = 0 := by linear_combination C2
        have := (mul_eq_zero.mp this).resolve_left hb0
        linear_combination -this
      · have : c * (e - k) = 0 := by linear_combination C3
        have := (mul_eq_zero.mp this).resolve_left hc0
        linear_combination this
    refine ⟨rfl, rfl, hek', ?_⟩
    have : e ^ 2 = m ^ 2 := by linear_combination B1
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this


theorem s26_matrix_main_U (h2 : (2 : K) ≠ 0) {a b c d s₀ : K} (ha : h.bar a = d)
    (hb : h.bar b = -c) (hs₀ : h.bar s₀ = s₀) (hs₀sq : s₀ ^ 2 = (a - d) ^ 2 + 4 * (b * c))
    (hs₀0 : s₀ ≠ 0) (hnd : b ≠ 0 ∨ c ≠ 0) {M : Matrix (Fin 3) (Fin 3) K}
    (hx : s26xM * M = M * s26xM) (hr : s26R0 a b c d * M = M * s26R0 a b c d)
    (hU : (M.map h.bar)ᵀ * M = 1) (hQ00 : (M * M) 0 0 = (M * M) 2 2)
    (hQ10 : (M * M) 1 0 = 0) :
    M = M 2 2 • (1 : Matrix (Fin 3) (Fin 3) K) ∨ M = M 2 2 • s26xM := by
  obtain ⟨m02, m12, m20, m21⟩ := s26_block_diag h2 hx
  have r00 := congrFun (congrFun hr 0) 0
  have r01 := congrFun (congrFun hr 0) 1
  have r10 := congrFun (congrFun hr 1) 0
  simp [s26R0, Matrix.mul_apply, Fin.sum_univ_three, m02, m12, m20, m21] at r00 r01 r10
  simp [Matrix.mul_apply, Fin.sum_univ_three, m02, m12, m20, m21] at hQ00 hQ10
  have u00 := congrFun (congrFun hU 0) 0
  have u10 := congrFun (congrFun hU 1) 0
  have u22 := congrFun (congrFun hU 2) 2
  simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_three, m02, m12,
    m20, m21] at u00 u10 u22
  have hres := s26_commutant_U h h2 (a := a) (b := b) (c := c) (d := d) (e := M 0 0)
    (g := M 0 1) (w := M 1 0) (k := M 1 1) (m := M 2 2) ha hb hs₀ hs₀sq hs₀0 hnd
    (by linear_combination u22) (by linear_combination r00) (by linear_combination r01)
    (by linear_combination r10) (by linear_combination hQ00) (by linear_combination hQ10)
    (by linear_combination u00) (by linear_combination u10)
  obtain ⟨hg, hh, hek, hem⟩ := hres
  rcases hem with he | he
  · left
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, m02, m12, m20, m21, hg, hh, ← hek, he]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s26xM, Matrix.smul_apply, m02, m12, m20, m21, hg, hh, ← hek, he]

end CFSG.ClassicalInvolution.Asc77
