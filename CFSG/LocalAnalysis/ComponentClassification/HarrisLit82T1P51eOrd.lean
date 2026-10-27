module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eZsig
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

variable {ℓ p m : ℕ}

theorem index_psl (h : IsPrimDiv ℓ p m) (hp : 0 < p) (hm : 0 < m) {n f : ℕ}
    (hd : ℓ ∣ lieOrderCofactor .PSL n (p ^ f)) : ∃ i ∈ Finset.Icc 2 n, m ∣ f * i := by
  change ℓ ∣ ∏ i ∈ Finset.Icc 2 n, ((p ^ f) ^ i - 1) at hd
  obtain ⟨i, hi, hdi⟩ := exists_mem_dvd_of_dvd_prod h.1 hd
  exact ⟨i, hi, (h.dvd_pow_pow_sub_one_iff hp hm f i).1 hdi⟩

theorem index_psu (h : IsPrimDiv ℓ p m) (hp : 0 < p) (hm : 0 < m) {n f : ℕ}
    (hd : ℓ ∣ lieOrderCofactor .PSU n (p ^ f)) :
    ∃ i ∈ Finset.Icc 2 n, (Even i ∧ m ∣ f * i) ∨ (¬ Even i ∧ m ∣ 2 * (f * i)) := by
  change ℓ ∣ ∏ i ∈ Finset.Icc 2 n,
    (if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1) at hd
  obtain ⟨i, hi, hdi⟩ := exists_mem_dvd_of_dvd_prod h.1 hd
  refine ⟨i, hi, ?_⟩
  by_cases he : Even i
  · simp only [he, ↓reduceIte] at hdi
    exact Or.inl ⟨he, (h.dvd_pow_pow_sub_one_iff hp hm f i).1 hdi⟩
  · simp only [he, ↓reduceIte] at hdi
    exact Or.inr ⟨he, h.dvd_of_dvd_pow_pow_add_one hp hm hdi⟩

theorem index_sp (h : IsPrimDiv ℓ p m) (hp : 0 < p) (hm : 0 < m) {n f : ℕ}
    (hd : ℓ ∣ ∏ i ∈ Finset.Icc 1 n, ((p ^ f) ^ (2 * i) - 1)) :
    ∃ i ∈ Finset.Icc 1 n, m ∣ f * (2 * i) := by
  obtain ⟨i, hi, hdi⟩ := exists_mem_dvd_of_dvd_prod h.1 hd
  exact ⟨i, hi, (h.dvd_pow_pow_sub_one_iff hp hm f _).1 hdi⟩

theorem index_list (h : IsPrimDiv ℓ p m) (hp : 0 < p) (hm : 0 < m) {f : ℕ} (L : List ℕ)
    (hd : ℓ ∣ (L.map fun d => (p ^ f) ^ d - 1).prod) : ∃ d ∈ L, m ∣ f * d := by
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil] at hd
    exact absurd (Nat.dvd_one.1 hd) h.1.ne_one
  | cons d L ih =>
    rw [List.map_cons, List.prod_cons] at hd
    rcases (Nat.Prime.dvd_mul h.1).1 hd with h1 | h1
    · exact ⟨d, List.mem_cons_self .., (h.dvd_pow_pow_sub_one_iff hp hm f d).1 h1⟩
    · obtain ⟨d', hd', hdd⟩ := ih h1
      exact ⟨d', List.mem_cons_of_mem _ hd', hdd⟩

theorem index_b3 (h : IsPrimDiv ℓ p m) (hp : 0 < p) (hm : 0 < m) {r : ℕ}
    (hd : ℓ ∣ lieOrderCofactor .POmegaOdd 3 (p ^ r)) :
    m ∣ r * 2 ∨ m ∣ r * 4 ∨ m ∣ r * 6 := by
  obtain ⟨i, hi, hdi⟩ := index_sp h hp hm (n := 3) hd
  obtain ⟨h1, h3⟩ := Finset.mem_Icc.1 hi
  interval_cases i
  · exact Or.inl (by simpa using hdi)
  · exact Or.inr (Or.inl (by simpa using hdi))
  · exact Or.inr (Or.inr (by simpa using hdi))

theorem dvd_cofactor_b3 {i r : ℕ} (h : IsPrimDiv ℓ p (r * (2 * i))) (hi : i ∈ Finset.Icc 1 3) :
    ℓ ∣ lieOrderCofactor .POmegaOdd 3 (p ^ r) :=
  h.dvd_pow_pow_sub_one.trans (Finset.dvd_prod_of_mem (fun j => (p ^ r) ^ (2 * j) - 1) hi)

theorem le_of_index {k r : ℕ} (hr : 0 < r) (h : k ∣ r * 2 ∨ k ∣ r * 4 ∨ k ∣ r * 6) :
    k ≤ r * 6 := by
  rcases h with h | h | h
  · have := Nat.le_of_dvd (by omega) h
    omega
  · have := Nat.le_of_dvd (by omega) h
    omega
  · exact Nat.le_of_dvd (by omega) h

theorem exists_of_dvd_four {f r k D : ℕ} (hr : 0 < r) (hfD : f * D = r * 6)
    (h : r * 4 ∣ f * k) : ∃ c, 6 * k = 4 * c * D := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, Nat.eq_of_mul_eq_mul_left hr ?_⟩
  calc r * (6 * k) = (f * D) * k := by rw [hfD]; ring
    _ = (f * k) * D := by ring
    _ = r * (4 * c * D) := by rw [hc]; ring

theorem pow_twelve_sub_one (q : ℕ) (hq : 1 ≤ q) :
    q ^ 12 - 1 = (q ^ 4 - 1) * (q ^ 8 + q ^ 4 + 1) := by
  have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ hq
  zify [h1, h2]
  ring

theorem admissible_of_lieModel_pomegaOdd {G : Type} [Group G] {n p r : ℕ}
    (h : Blueprint.LieModel G .POmegaOdd n p r) : StatedLieAdmissible .POmegaOdd n p r :=
  CFSG.Blueprint.LieModel.admissible h


theorem cofactor_pomegaPlus_succ (n q : ℕ) : lieOrderCofactor .POmegaPlus (n + 1) q =
    (q ^ (n + 1) - 1) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
  rfl

theorem cofactor_pomegaMinus_succ (n q : ℕ) : lieOrderCofactor .POmegaMinus (n + 1) q =
    (q ^ (n + 1) + 1) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1) :=
  rfl

structure OrdData (t : StatedLieTag) (n p f r : ℕ) : Prop where
  three_le : 3 ≤ p
  one_le_f : 1 ≤ f
  one_le_r : 1 ≤ r
  exp_eq : lieSylowExponent t n * f = 9 * r
  dvd_six : ∀ {ℓ : ℕ}, IsPrimDiv ℓ p (r * (2 * 3)) → ℓ ∣ lieOrderCofactor t n (p ^ f)
  dvd_four : ∀ {ℓ : ℕ}, IsPrimDiv ℓ p (r * (2 * 2)) → ℓ ∣ lieOrderCofactor t n (p ^ f)
  le_six : ∀ {ℓ k : ℕ}, IsPrimDiv ℓ p k → 0 < k → ℓ ∣ lieOrderCofactor t n (p ^ f) →
    ¬ ℓ ∣ lieOrderDivisor t n (p ^ f) → k ≤ r * 6

theorem ordData_of_lieModel (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {t : StatedLieTag} {n p f r : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hY : Blueprint.LieModel Y t n p f) (hadm' : StatedLieAdmissible .POmegaOdd 3 p r)
    (hY' : Blueprint.LieModel Y .POmegaOdd 3 p r) : OrdData t n p f r := by
  obtain ⟨-, hord, hfac⟩ := hO Y t n p f hadm hY
  obtain ⟨-, hord', hfac'⟩ := hO Y .POmegaOdd 3 p r hadm' hY'
  have hp : p.Prime := hadm.1
  have hp0 : 0 < p := hp.pos
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hr : 1 ≤ r := hadm'.2.1
  rw [lieOrderNumerator_eq hadm] at hord
  rw [lieOrderNumerator_eq hadm'] at hord'
  have hA : ∀ {ℓ k : ℕ}, IsPrimDiv ℓ p k → 2 ≤ k →
      ℓ ∣ lieOrderCofactor .POmegaOdd 3 (p ^ r) → ℓ ∣ lieOrderCofactor t n (p ^ f) := by
    intro ℓ k hℓ hk hd
    have h1 : ℓ ∣ Nat.card Y * lieOrderDivisor .POmegaOdd 3 (p ^ r) := by
      rw [hord']
      exact Dvd.dvd.mul_left hd _
    have hY2 : ℓ ∣ Nat.card Y := by
      rcases (Nat.Prime.dvd_mul hℓ.1).1 h1 with h2 | h2
      · exact h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ.1 Nat.prime_two).1 h2)
          (hℓ.ne_two hodd hk)
    have h3 : ℓ ∣ (p ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (p ^ f) := by
      rw [← hord]
      exact Dvd.dvd.mul_right hY2 _
    rcases (Nat.Prime.dvd_mul hℓ.1).1 h3 with h4 | h4
    · rw [← pow_mul] at h4
      exact absurd h4 (hℓ.not_dvd_pow_base hp0 (by omega) _)
    · exact h4
  refine ⟨by have := hp.two_le; omega, hadm.2.1, hr, ?_, fun h₆ => ?_, fun h₄ => ?_, ?_⟩
  · rw [← hfac, hfac']
    rfl
  · exact hA h₆ (by omega) (dvd_cofactor_b3 h₆ (Finset.mem_Icc.2 ⟨by norm_num, le_rfl⟩))
  · exact hA h₄ (by omega) (dvd_cofactor_b3 h₄ (Finset.mem_Icc.2 ⟨by norm_num, by norm_num⟩))
  · intro ℓ k hℓ hk hd hdiv
    have h1 : ℓ ∣ Nat.card Y * lieOrderDivisor t n (p ^ f) := by
      rw [hord]
      exact Dvd.dvd.mul_left hd _
    have hY2 := ((Nat.Prime.dvd_mul hℓ.1).1 h1).resolve_right hdiv
    have h3 : ℓ ∣ (p ^ r) ^ lieSylowExponent .POmegaOdd 3 *
        lieOrderCofactor .POmegaOdd 3 (p ^ r) := by
      rw [← hord']
      exact Dvd.dvd.mul_right hY2 _
    rcases (Nat.Prime.dvd_mul hℓ.1).1 h3 with h4 | h4
    · rw [← pow_mul] at h4
      exact absurd h4 (hℓ.not_dvd_pow_base hp0 hk _)
    · exact le_of_index (by omega) (index_b3 hℓ hp0 hk h4)

theorem eq_of_sp {n p f r : ℕ} (hp3 : 3 ≤ p) (hf : 1 ≤ f) (hr : 1 ≤ r) (hn : 2 ≤ n)
    (hNf : n ^ 2 * f = 9 * r)
    (h6 : ∀ {ℓ : ℕ}, IsPrimDiv ℓ p (r * (2 * 3)) →
      ℓ ∣ ∏ i ∈ Finset.Icc 1 n, ((p ^ f) ^ (2 * i) - 1))
    (hD : ∀ {ℓ k : ℕ}, IsPrimDiv ℓ p k → 0 < k →
      ℓ ∣ ∏ i ∈ Finset.Icc 1 n, ((p ^ f) ^ (2 * i) - 1) → ¬ ℓ ∣ 2 → k ≤ r * 6) :
    n = 3 ∧ f = r := by
  have hp0 : 0 < p := by omega
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  obtain ⟨i, hi, hi6⟩ := index_sp h₆ hp0 (by omega) (h6 h₆)
  obtain ⟨hi1, hin⟩ := Finset.mem_Icc.1 hi
  have h2n : 2 * n ≤ f * (2 * n) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * (2 * n) by omega)
  have hℓc : ℓ ∣ ∏ i ∈ Finset.Icc 1 n, ((p ^ f) ^ (2 * i) - 1) :=
    hℓ.dvd_pow_pow_sub_one.trans (Finset.dvd_prod_of_mem (fun i => (p ^ f) ^ (2 * i) - 1)
      (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩))
  have e3 := hD hℓ (by omega) hℓc (hℓ.not_dvd_small hp0 (by omega) two_pos (by norm_num))
  have e1 : r * (2 * 3) ≤ f * (2 * i) := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hi6
  have e2 : f * (2 * i) ≤ f * (2 * n) := Nat.mul_le_mul_left _ (by omega)
  have hfn : f * n = r * 3 := by
    have : f * (2 * n) = 2 * (f * n) := by ring
    omega
  have hn3 : n = 3 := by
    have h3 : f * (n * n) = f * (n * 3) := by
      calc f * (n * n) = n ^ 2 * f := by ring
        _ = 9 * r := hNf
        _ = 3 * (f * n) := by rw [hfn]; ring
        _ = f * (n * 3) := by ring
    have h4 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) h3
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) h4
  subst hn3
  exact ⟨rfl, by omega⟩

namespace OrdData

variable {n p f r : ℕ}

theorem eq_psp (h : OrdData .PSp n p f r) (hn : 2 ≤ n) : n = 3 ∧ f = r :=
  eq_of_sp h.three_le h.one_le_f h.one_le_r hn h.exp_eq h.dvd_six
    fun hℓ hk hd h2 => h.le_six hℓ hk hd fun hd' => h2 (hd'.trans (Nat.gcd_dvd_left _ _))

theorem eq_pomegaOdd (h : OrdData .POmegaOdd n p f r) (hn : 2 ≤ n) : n = 3 ∧ f = r :=
  eq_of_sp h.three_le h.one_le_f h.one_le_r hn h.exp_eq h.dvd_six
    fun hℓ hk hd h2 => h.le_six hℓ hk hd h2

theorem false_psl (h : OrdData .PSL n p f r) (hn : 2 ≤ n) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change n * (n - 1) / 2 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  obtain ⟨ℓ₄, h₄⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 2) by omega)
  obtain ⟨k, hk, hk6⟩ := index_psl h₆ hp0 (by omega) (h.dvd_six h₆)
  obtain ⟨hk2, hkn⟩ := Finset.mem_Icc.1 hk
  have hnf : n ≤ f * n := Nat.le_mul_of_pos_left n (by omega)
  have hfn3 : 3 ≤ f * n := by
    by_contra hlt
    have hn2 : n = 2 := by omega
    subst hn2
    omega
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 hfn3
  have hℓc : ℓ ∣ lieOrderCofactor .PSL n (p ^ f) :=
    hℓ.dvd_pow_pow_sub_one.trans
      (Finset.dvd_prod_of_mem (fun i => (p ^ f) ^ i - 1) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩))
  have hℓd : ¬ ℓ ∣ lieOrderDivisor .PSL n (p ^ f) := by
    intro hd
    change ℓ ∣ Nat.gcd n (p ^ f - 1) at hd
    have h1 : f * n ∣ f :=
      (hℓ.dvd_iff hp0 (by omega) f).1 (hd.trans (Nat.gcd_dvd_right _ _))
    have h2 := Nat.le_of_dvd (by omega) h1
    have h3 : f * 2 ≤ f * n := Nat.mul_le_mul_left f hn
    omega
  have e3 := h.le_six hℓ (by omega) hℓc hℓd
  have e1 : r * (2 * 3) ≤ f * k := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hk6
  have e2 : f * k ≤ f * n := Nat.mul_le_mul_left _ hkn
  have hfn : f * n = r * 6 := by omega
  obtain ⟨N, hN⟩ : ∃ N, N = n * (n - 1) / 2 := ⟨_, rfl⟩
  have h2N : 2 * N = n * (n - 1) := by
    rw [hN]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  rw [← hN] at hNf
  have hn4 : n = 4 := by
    have h3 : f * (n * (n - 1)) = f * (n * 3) := by
      calc f * (n * (n - 1)) = 2 * (N * f) := by rw [← h2N]; ring
        _ = 3 * (f * n) := by rw [hNf, hfn]; ring
        _ = f * (n * 3) := by ring
    have h4 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) h3
    have h5 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) h4
    omega
  subst hn4
  obtain ⟨k', hk', hk'4⟩ := index_psl h₄ hp0 (by omega) (h.dvd_four h₄)
  obtain ⟨c, hc⟩ := exists_of_dvd_four (by omega) hfn (show r * 4 ∣ f * k' from hk'4)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hk'
  interval_cases k' <;> omega

theorem false_psu (h : OrdData .PSU n p f r) (hn : 3 ≤ n) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change n * (n - 1) / 2 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  obtain ⟨ℓ₄, h₄⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 2) by omega)
  obtain ⟨j, hjodd, hjn, hnj⟩ : ∃ j, ¬ Even j ∧ j ≤ n ∧ n ≤ j + 1 := by
    by_cases he : Even n
    · refine ⟨n - 1, fun h => ?_, by omega, by omega⟩
      have h1 : Even (n - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]; exact he
      exact (Nat.even_add_one.1 h1) h
    · exact ⟨n, he, le_rfl, by omega⟩
  have hj3 : 3 ≤ j := by
    rcases Nat.even_or_odd j with h | ⟨c, hc⟩
    · exact absurd h hjodd
    · omega
  obtain ⟨i, hi, hi6⟩ := index_psu h₆ hp0 (by omega) (h.dvd_six h₆)
  obtain ⟨hi2, hin⟩ := Finset.mem_Icc.1 hi
  have hjf : j ≤ f * j := Nat.le_mul_of_pos_left j (by omega)
  have hfj0 : 0 < f * j := by omega
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ 2 * (f * j) by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .PSU n (p ^ f) := by
    have h1 := hℓ.dvd_pow_pow_add_one hfj0
    have h2 := Finset.dvd_prod_of_mem
      (fun i => if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1)
      (Finset.mem_Icc.2 ⟨(by omega : 2 ≤ j), hjn⟩)
    simp only [hjodd, ↓reduceIte] at h2
    exact h1.trans h2
  have hℓd : ¬ ℓ ∣ lieOrderDivisor .PSU n (p ^ f) := by
    intro hd
    change ℓ ∣ Nat.gcd n (p ^ f + 1) at hd
    have h1 : 2 * (f * j) ∣ 2 * f :=
      hℓ.dvd_two_mul_of_dvd_add_one hp0 (by omega) (hd.trans (Nat.gcd_dvd_right _ _))
    have h2 := Nat.le_of_dvd (by omega) h1
    have h3 : f * 3 ≤ f * j := Nat.mul_le_mul_left f hj3
    omega
  have e3 := h.le_six hℓ (by omega) hℓc hℓd
  have e1 : r * (2 * 3) ≤ 2 * (f * j) := by
    rcases hi6 with ⟨-, h6⟩ | ⟨he, h6⟩
    · have h1 := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) h6
      have h2 : f * i ≤ f * (j + 1) := Nat.mul_le_mul_left _ (by omega)
      have h3 : f * (j + 1) = f * j + f := by ring
      have h4 : f ≤ f * j := Nat.le_mul_of_pos_right f (by omega)
      omega
    · have h6' := Nat.le_of_dvd (Nat.mul_pos two_pos (Nat.mul_pos (by omega) (by omega))) h6
      have hij : i ≤ j := by
        rcases Nat.lt_or_ge i n with hlt | hge
        · omega
        · by_contra hij
          have hj' : i = j + 1 := by omega
          exact he (hj' ▸ Nat.even_add_one.2 hjodd)
      have : f * i ≤ f * j := Nat.mul_le_mul_left _ hij
      omega
  have hfj : 2 * (f * j) = r * 6 := by omega
  obtain ⟨N, hN⟩ : ∃ N, N = n * (n - 1) / 2 := ⟨_, rfl⟩
  have h2N : 2 * N = n * (n - 1) := by
    rw [hN]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  rw [← hN] at hNf
  have hnj6 : n * (n - 1) = 6 * j := by
    have h3 : f * (n * (n - 1)) = f * (6 * j) := by
      calc f * (n * (n - 1)) = 2 * (N * f) := by rw [← h2N]; ring
        _ = 3 * (2 * (f * j)) := by rw [hNf, hfj]; ring
        _ = f * (6 * j) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  rcases (show j = n ∨ j + 1 = n by omega) with hjn' | hjn'
  ·
    rw [hjn'] at hnj6 hfj
    have h5 : n - 1 = 6 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) (by rw [hnj6]; ring)
    have hn7 : n = 7 := by omega
    subst hn7
    have hfD : f * 14 = r * 6 := by omega
    obtain ⟨i', hi', hi'4⟩ := index_psu h₄ hp0 (by omega) (h.dvd_four h₄)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi'
    rcases hi'4 with ⟨-, h4⟩ | ⟨-, h4⟩
    · obtain ⟨c, hc⟩ := exists_of_dvd_four (by omega) hfD (show r * 4 ∣ f * i' from h4)
      interval_cases i' <;> omega
    · obtain ⟨c, hc⟩ := exists_of_dvd_four (k := 2 * i') (by omega) hfD
        (by rw [show f * (2 * i') = 2 * (f * i') by ring]; exact h4)
      interval_cases i' <;> omega
  ·
    have h6 : n * j = 6 * j := by
      rw [show n - 1 = j by omega] at hnj6
      exact hnj6
    have hn6 : n = 6 := Nat.eq_of_mul_eq_mul_right (by omega : 0 < j) h6
    subst hn6
    obtain rfl : j = 5 := by omega
    have hfD : f * 10 = r * 6 := by omega
    obtain ⟨i', hi', hi'4⟩ := index_psu h₄ hp0 (by omega) (h.dvd_four h₄)
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi'
    rcases hi'4 with ⟨-, h4⟩ | ⟨-, h4⟩
    · obtain ⟨c, hc⟩ := exists_of_dvd_four (by omega) hfD (show r * 4 ∣ f * i' from h4)
      interval_cases i' <;> omega
    · obtain ⟨c, hc⟩ := exists_of_dvd_four (k := 2 * i') (by omega) hfD
        (by rw [show f * (2 * i') = 2 * (f * i') by ring]; exact h4)
      interval_cases i' <;> omega

theorem false_pomegaPlus (h : OrdData .POmegaPlus n p f r) (hn : 4 ≤ n) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hNf : (n' + 1) * n' * f = 9 * r := h.exp_eq
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have h₆c : ℓ₆ ∣ ((p ^ f) ^ (n' + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 n', ((p ^ f) ^ (2 * i) - 1) := by
    rw [← cofactor_pomegaPlus_succ]
    exact h.dvd_six h₆
  have h2n : 2 * n' ≤ f * (2 * n') := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : r * (2 * 3) ≤ f * (2 * n') := by
    rcases (Nat.Prime.dvd_mul h₆.1).1 h₆c with h1 | h1
    · have h2 := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega))
        ((h₆.dvd_pow_pow_sub_one_iff hp0 (by omega) f _).1 h1)
      have h3 : f * (n' + 1) ≤ f * (2 * n') := Nat.mul_le_mul_left f (by omega)
      omega
    · obtain ⟨i, hi, hi6⟩ := index_sp h₆ hp0 (by omega) h1
      obtain ⟨hi1, hin⟩ := Finset.mem_Icc.1 hi
      have h2 := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hi6
      have h3 : f * (2 * i) ≤ f * (2 * n') := Nat.mul_le_mul_left _ (by omega)
      omega
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * (2 * n') by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .POmegaPlus (n' + 1) (p ^ f) := by
    rw [cofactor_pomegaPlus_succ]
    exact Dvd.dvd.mul_left (hℓ.dvd_pow_pow_sub_one.trans (Finset.dvd_prod_of_mem
      (fun i => (p ^ f) ^ (2 * i) - 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩))) _
  have hℓd : ¬ ℓ ∣ lieOrderDivisor .POmegaPlus (n' + 1) (p ^ f) := by
    intro hd
    change ℓ ∣ Nat.gcd 4 ((p ^ f) ^ (n' + 1) - 1) at hd
    exact hℓ.not_dvd_small hp0 (by omega) (by norm_num) le_rfl
      (hd.trans (Nat.gcd_dvd_left _ _))
  have e3 := h.le_six hℓ (by omega) hℓc hℓd
  have hfn : f * n' = r * 3 := by
    have : f * (2 * n') = 2 * (f * n') := by ring
    omega
  have h3 : f * (n' * (n' + 1)) = f * (n' * 3) := by
    calc f * (n' * (n' + 1)) = (n' + 1) * n' * f := by ring
      _ = 9 * r := hNf
      _ = 3 * (f * n') := by rw [hfn]; ring
      _ = f * (n' * 3) := by ring
  have h4 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) h3
  have h5 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n') h4
  omega

theorem false_pomegaMinus (h : OrdData .POmegaMinus n p f r) (hn : 4 ≤ n) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hNf : (n' + 1) * n' * f = 9 * r := h.exp_eq
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  obtain ⟨ℓ₄, h₄⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 2) by omega)
  have h₆c : ℓ₆ ∣ ((p ^ f) ^ (n' + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 n', ((p ^ f) ^ (2 * i) - 1) := by
    rw [← cofactor_pomegaMinus_succ]
    exact h.dvd_six h₆
  have h₄c : ℓ₄ ∣ ((p ^ f) ^ (n' + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 n', ((p ^ f) ^ (2 * i) - 1) := by
    rw [← cofactor_pomegaMinus_succ]
    exact h.dvd_four h₄
  have hfn0 : 0 < f * (n' + 1) := Nat.mul_pos (by omega) (by omega)
  have e1 : r * (2 * 3) ≤ 2 * (f * (n' + 1)) := by
    rcases (Nat.Prime.dvd_mul h₆.1).1 h₆c with h1 | h1
    · exact Nat.le_of_dvd (by omega) (h₆.dvd_of_dvd_pow_pow_add_one hp0 (by omega) h1)
    · obtain ⟨i, hi, hi6⟩ := index_sp h₆ hp0 (by omega) h1
      obtain ⟨hi1, hin⟩ := Finset.mem_Icc.1 hi
      have h2 := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hi6
      have h3 : f * (2 * i) ≤ f * (2 * (n' + 1)) := Nat.mul_le_mul_left _ (by omega)
      have h4 : f * (2 * (n' + 1)) = 2 * (f * (n' + 1)) := by ring
      omega
  have hn'f : n' + 1 ≤ f * (n' + 1) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ 2 * (f * (n' + 1)) by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .POmegaMinus (n' + 1) (p ^ f) := by
    rw [cofactor_pomegaMinus_succ]
    exact Dvd.dvd.mul_right (hℓ.dvd_pow_pow_add_one hfn0) _
  have hℓd : ¬ ℓ ∣ lieOrderDivisor .POmegaMinus (n' + 1) (p ^ f) := by
    intro hd
    change ℓ ∣ Nat.gcd 4 ((p ^ f) ^ (n' + 1) + 1) at hd
    exact hℓ.not_dvd_small hp0 (by omega) (by norm_num) le_rfl
      (hd.trans (Nat.gcd_dvd_left _ _))
  have e3 := h.le_six hℓ (by omega) hℓc hℓd
  have hfn : f * (n' + 1) = r * 3 := by omega
  have h3 : f * ((n' + 1) * n') = f * ((n' + 1) * 3) := by
    calc f * ((n' + 1) * n') = (n' + 1) * n' * f := by ring
      _ = 9 * r := hNf
      _ = 3 * (f * (n' + 1)) := by rw [hfn]; ring
      _ = f * ((n' + 1) * 3) := by ring
  have h4 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) h3
  have h5 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n' + 1) h4
  subst h5
  have hfD : f * 8 = r * 6 := by omega
  rcases (Nat.Prime.dvd_mul h₄.1).1 h₄c with h1 | h1
  · obtain ⟨c, hc⟩ := exists_of_dvd_four (k := 8) (by omega) hfD
      (by rw [show f * 8 = 2 * (f * (3 + 1)) by ring]
          exact h₄.dvd_of_dvd_pow_pow_add_one hp0 (by omega) h1)
    omega
  · obtain ⟨i, hi, hi4⟩ := index_sp h₄ hp0 (by omega) h1
    obtain ⟨hi1, hin⟩ := Finset.mem_Icc.1 hi
    obtain ⟨c, hc⟩ := exists_of_dvd_four (k := 2 * i) (by omega) hfD
      (show r * 4 ∣ f * (2 * i) from hi4)
    interval_cases i <;> omega

theorem false_g2 (h : OrdData .G2 n p f r) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change 6 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have h6L : ℓ₆ ∣ ([6, 2].map fun d => (p ^ f) ^ d - 1).prod := by
    have hL : lieOrderCofactor .G2 n (p ^ f) =
        ([6, 2].map fun d => (p ^ f) ^ d - 1).prod := by
      simp [lieOrderCofactor]
    rw [← hL]
    exact h.dvd_six h₆
  obtain ⟨d, hdL, hd6⟩ := index_list h₆ hp0 (by omega) _ h6L
  have e1 : r * (2 * 3) ≤ f * 6 := by
    simp at hdL
    rcases hdL with rfl | rfl <;>
      (have := Nat.le_of_dvd (by omega) hd6; omega)
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * 6 by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .G2 n (p ^ f) := by
    change ℓ ∣ ((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 2 - 1)
    exact Dvd.dvd.mul_right hℓ.dvd_pow_pow_sub_one _
  have e3 := h.le_six hℓ (by omega) hℓc (fun hd => hℓ.1.not_dvd_one hd)
  omega

theorem false_f4 (h : OrdData .F4 n p f r) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change 24 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have h6L : ℓ₆ ∣ ([12, 8, 6, 2].map fun d => (p ^ f) ^ d - 1).prod := by
    have hL : lieOrderCofactor .F4 n (p ^ f) =
        ([12, 8, 6, 2].map fun d => (p ^ f) ^ d - 1).prod := by
      simp [lieOrderCofactor, mul_assoc]
    rw [← hL]
    exact h.dvd_six h₆
  obtain ⟨d, hdL, hd6⟩ := index_list h₆ hp0 (by omega) _ h6L
  have e1 : r * (2 * 3) ≤ f * 12 := by
    simp at hdL
    rcases hdL with rfl | rfl | rfl | rfl <;>
      (have := Nat.le_of_dvd (by omega) hd6; omega)
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * 12 by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .F4 n (p ^ f) := by
    change ℓ ∣ ((p ^ f) ^ 12 - 1) * ((p ^ f) ^ 8 - 1) * ((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 2 - 1)
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      hℓ.dvd_pow_pow_sub_one _) _) _
  have e3 := h.le_six hℓ (by omega) hℓc (fun hd => hℓ.1.not_dvd_one hd)
  omega

theorem false_e6 (h : OrdData .E6 n p f r) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change 36 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have hL : lieOrderCofactor .E6 n (p ^ f) =
      ([12, 9, 8, 6, 5, 2].map fun d => (p ^ f) ^ d - 1).prod := by
    simp [lieOrderCofactor, mul_assoc]
  have h6L : ℓ₆ ∣ ([12, 9, 8, 6, 5, 2].map fun d => (p ^ f) ^ d - 1).prod := by
    rw [← hL]
    exact h.dvd_six h₆
  obtain ⟨d, hdL, hd6⟩ := index_list h₆ hp0 (by omega) _ h6L
  have e1 : r * (2 * 3) ≤ f * 12 := by
    simp at hdL
    rcases hdL with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (have := Nat.le_of_dvd (by omega) hd6; omega)
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * 12 by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .E6 n (p ^ f) := by
    rw [hL]
    exact hℓ.dvd_pow_pow_sub_one.trans
      (List.dvd_prod (List.mem_map.2 ⟨12, by simp, rfl⟩))
  have hℓd : ¬ ℓ ∣ lieOrderDivisor .E6 n (p ^ f) := by
    intro hd
    change ℓ ∣ Nat.gcd 3 (p ^ f - 1) at hd
    exact hℓ.not_dvd_small hp0 (by omega) (by norm_num) (by norm_num)
      (hd.trans (Nat.gcd_dvd_left _ _))
  have e3 := h.le_six hℓ (by omega) hℓc hℓd
  omega

theorem false_e7 (h : OrdData .E7 n p f r) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change 63 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have hL : lieOrderCofactor .E7 n (p ^ f) =
      ([18, 14, 12, 10, 8, 6, 2].map fun d => (p ^ f) ^ d - 1).prod := by
    simp [lieOrderCofactor, mul_assoc]
  have h6L : ℓ₆ ∣ ([18, 14, 12, 10, 8, 6, 2].map fun d => (p ^ f) ^ d - 1).prod := by
    rw [← hL]
    exact h.dvd_six h₆
  obtain ⟨d, hdL, hd6⟩ := index_list h₆ hp0 (by omega) _ h6L
  have e1 : r * (2 * 3) ≤ f * 18 := by
    simp at hdL
    rcases hdL with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (have := Nat.le_of_dvd (by omega) hd6; omega)
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * 18 by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .E7 n (p ^ f) := by
    rw [hL]
    exact hℓ.dvd_pow_pow_sub_one.trans
      (List.dvd_prod (List.mem_map.2 ⟨18, by simp, rfl⟩))
  have hℓd : ¬ ℓ ∣ lieOrderDivisor .E7 n (p ^ f) := by
    intro hd
    change ℓ ∣ Nat.gcd 2 (p ^ f - 1) at hd
    exact hℓ.not_dvd_small hp0 (by omega) (by norm_num) (by norm_num)
      (hd.trans (Nat.gcd_dvd_left _ _))
  have e3 := h.le_six hℓ (by omega) hℓc hℓd
  omega

theorem false_e8 (h : OrdData .E8 n p f r) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change 120 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have hL : lieOrderCofactor .E8 n (p ^ f) =
      ([30, 24, 20, 18, 14, 12, 8, 2].map fun d => (p ^ f) ^ d - 1).prod := by
    simp [lieOrderCofactor, mul_assoc]
  have h6L : ℓ₆ ∣ ([30, 24, 20, 18, 14, 12, 8, 2].map fun d => (p ^ f) ^ d - 1).prod := by
    rw [← hL]
    exact h.dvd_six h₆
  obtain ⟨d, hdL, hd6⟩ := index_list h₆ hp0 (by omega) _ h6L
  have e1 : r * (2 * 3) ≤ f * 30 := by
    simp at hdL
    rcases hdL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (have := Nat.le_of_dvd (by omega) hd6; omega)
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * 30 by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .E8 n (p ^ f) := by
    rw [hL]
    exact hℓ.dvd_pow_pow_sub_one.trans
      (List.dvd_prod (List.mem_map.2 ⟨30, by simp, rfl⟩))
  have e3 := h.le_six hℓ (by omega) hℓc (fun hd => hℓ.1.not_dvd_one hd)
  omega

theorem false_twistedE6 (h : OrdData .twistedE6 n p f r) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change 36 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have h₆c : ℓ₆ ∣ ((p ^ f) ^ 12 - 1) * ((p ^ f) ^ 9 + 1) * ((p ^ f) ^ 8 - 1) *
      ((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 5 + 1) * ((p ^ f) ^ 2 - 1) := h.dvd_six h₆
  have hm6 : 0 < r * (2 * 3) := by omega
  have e1 : r * (2 * 3) ≤ f * 18 := by
    have hs := fun k (hk : 0 < k) (h : r * (2 * 3) ∣ f * k) =>
      Nat.le_of_dvd (Nat.mul_pos (by omega) hk) h
    have ha := fun k (hk : 0 < k) (h : r * (2 * 3) ∣ 2 * (f * k)) =>
      Nat.le_of_dvd (Nat.mul_pos two_pos (Nat.mul_pos (by omega) hk)) h
    rcases (Nat.Prime.dvd_mul h₆.1).1 h₆c with h | h
    · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
      · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
        · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
          · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
            · have := hs 12 (by norm_num) ((h₆.dvd_pow_pow_sub_one_iff hp0 hm6 f 12).1 h)
              omega
            · have := ha 9 (by norm_num) (h₆.dvd_of_dvd_pow_pow_add_one hp0 hm6 h)
              omega
          · have := hs 8 (by norm_num) ((h₆.dvd_pow_pow_sub_one_iff hp0 hm6 f 8).1 h)
            omega
        · have := hs 6 (by norm_num) ((h₆.dvd_pow_pow_sub_one_iff hp0 hm6 f 6).1 h)
          omega
      · have := ha 5 (by norm_num) (h₆.dvd_of_dvd_pow_pow_add_one hp0 hm6 h)
        omega
    · have := hs 2 (by norm_num) ((h₆.dvd_pow_pow_sub_one_iff hp0 hm6 f 2).1 h)
      omega
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ 2 * (f * 9) by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .twistedE6 n (p ^ f) := by
    change ℓ ∣ ((p ^ f) ^ 12 - 1) * ((p ^ f) ^ 9 + 1) * ((p ^ f) ^ 8 - 1) *
      ((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 5 + 1) * ((p ^ f) ^ 2 - 1)
    have h1 := hℓ.dvd_pow_pow_add_one (by omega)
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_left h1 _) _) _) _) _
  have hℓd : ¬ ℓ ∣ lieOrderDivisor .twistedE6 n (p ^ f) := by
    intro hd
    change ℓ ∣ Nat.gcd 3 (p ^ f + 1) at hd
    exact hℓ.not_dvd_small hp0 (by omega) (by norm_num) (by norm_num)
      (hd.trans (Nat.gcd_dvd_left _ _))
  have e3 := h.le_six hℓ (by omega) hℓc hℓd
  omega

theorem false_trialityD4 (h : OrdData .trialityD4 n p f r) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change 12 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have h₆c : ℓ₆ ∣ ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1) * ((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 2 - 1) :=
    h.dvd_six h₆
  have hm6 : 0 < r * (2 * 3) := by omega
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp0
  have e1 : r * (2 * 3) ≤ f * 12 := by
    rcases (Nat.Prime.dvd_mul h₆.1).1 h₆c with h | h
    · rcases (Nat.Prime.dvd_mul h₆.1).1 h with h | h
      · have h12 : ℓ₆ ∣ (p ^ f) ^ 12 - 1 := by
          rw [pow_twelve_sub_one _ hq1]
          exact Dvd.dvd.mul_left h _
        exact Nat.le_of_dvd (by omega) ((h₆.dvd_pow_pow_sub_one_iff hp0 hm6 f 12).1 h12)
      · have := Nat.le_of_dvd (by omega) ((h₆.dvd_pow_pow_sub_one_iff hp0 hm6 f 6).1 h)
        omega
    · have := Nat.le_of_dvd (by omega) ((h₆.dvd_pow_pow_sub_one_iff hp0 hm6 f 2).1 h)
      omega
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ f * 12 by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .trialityD4 n (p ^ f) := by
    change ℓ ∣ ((p ^ f) ^ 8 + (p ^ f) ^ 4 + 1) * ((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 2 - 1)
    have h1 := hℓ.dvd_pow_pow_sub_one (f := f) (k := 12)
    rw [pow_twelve_sub_one _ hq1] at h1
    rcases (Nat.Prime.dvd_mul hℓ.1).1 h1 with h2 | h2
    · exact absurd ((hℓ.dvd_pow_pow_sub_one_iff hp0 (by omega) f 4).1 h2)
        (fun h3 => by have := Nat.le_of_dvd (by omega) h3; omega)
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h2 _) _
  have e3 := h.le_six hℓ (by omega) hℓc (fun hd => hℓ.1.not_dvd_one hd)
  omega

theorem false_twistedG2 (h : OrdData .twistedG2 n p f r) : False := by
  have hp3 := h.three_le
  have hp0 : 0 < p := by omega
  have hf := h.one_le_f
  have hr := h.one_le_r
  have hNf := h.exp_eq
  change 3 * f = 9 * r at hNf
  obtain ⟨ℓ₆, h₆⟩ := exists_isPrimDiv hp3 (show 3 ≤ r * (2 * 3) by omega)
  have h₆c : ℓ₆ ∣ ((p ^ f) ^ 3 + 1) * (p ^ f - 1) := h.dvd_six h₆
  have hm6 : 0 < r * (2 * 3) := by omega
  have e1 : r * (2 * 3) ≤ 2 * (f * 3) := by
    rcases (Nat.Prime.dvd_mul h₆.1).1 h₆c with h | h
    · exact Nat.le_of_dvd (by omega) (h₆.dvd_of_dvd_pow_pow_add_one hp0 hm6 h)
    · have := Nat.le_of_dvd (by omega) ((h₆.dvd_iff hp0 hm6 f).1 h)
      omega
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hp3 (show 3 ≤ 2 * (f * 3) by omega)
  have hℓc : ℓ ∣ lieOrderCofactor .twistedG2 n (p ^ f) := by
    change ℓ ∣ ((p ^ f) ^ 3 + 1) * (p ^ f - 1)
    exact Dvd.dvd.mul_right (hℓ.dvd_pow_pow_add_one (by omega)) _
  have e3 := h.le_six hℓ (by omega) hℓc (fun hd => hℓ.1.not_dvd_one hd)
  omega

end OrdData

theorem eq_of_lieModel_pomegaOdd_three (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {t : StatedLieTag} {n p f r : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hY : Blueprint.LieModel Y t n p f) (hadm' : StatedLieAdmissible .POmegaOdd 3 p r)
    (hY' : Blueprint.LieModel Y .POmegaOdd 3 p r) :
    (t = .POmegaOdd ∨ t = .PSp) ∧ n = 3 ∧ f = r := by
  have h := ordData_of_lieModel hO hp2 hadm hY hadm' hY'
  cases t with
  | PSL => exact (h.false_psl hadm.2.2.1).elim
  | PSU => exact (h.false_psu hadm.2.2.1).elim
  | PSp =>
    obtain ⟨h1, h2⟩ := h.eq_psp hadm.2.2.1
    exact ⟨Or.inr rfl, h1, h2⟩
  | POmegaOdd =>
    obtain ⟨h1, h2⟩ := h.eq_pomegaOdd (by have := hadm.2.2.1; omega)
    exact ⟨Or.inl rfl, h1, h2⟩
  | POmegaPlus => exact (h.false_pomegaPlus hadm.2.2).elim
  | POmegaMinus => exact (h.false_pomegaMinus hadm.2.2).elim
  | G2 => exact h.false_g2.elim
  | F4 => exact h.false_f4.elim
  | E6 => exact h.false_e6.elim
  | E7 => exact h.false_e7.elim
  | E8 => exact h.false_e8.elim
  | twistedE6 => exact h.false_twistedE6.elim
  | trialityD4 => exact h.false_trialityD4.elim
  | twistedB2 => exact absurd hadm.2.2.2.1 hp2
  | twistedG2 => exact h.false_twistedG2.elim
  | twistedF4 => exact absurd hadm.2.2.2.1 hp2
  | Tits => exact absurd hadm.2.2.2.1 hp2

theorem noSpin7_of_lieModel (hO : LieOrderFormulasInput) {L : Type} [Group L]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hL : Blueprint.LieModel (L ⧸ center L) t n p f)
    (ht : ¬ ((t = .POmegaOdd ∨ t = .PSp) ∧ n = 3)) : NoSpin7 p L := by
  intro r _ _ hL'
  obtain ⟨h1, h2, -⟩ := eq_of_lieModel_pomegaOdd_three hO hp2 hadm hL
    (admissible_of_lieModel_pomegaOdd hL') hL'
  exact ht ⟨h1, h2⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51e
