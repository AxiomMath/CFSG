module

public import CFSG.LieType.SeitzGeneration.ExcTorusArith
public import CFSG.Timmesfeld.Orders.ExceptionalWeylCert

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.LieType.SeitzGeneration CFSG.Timmesfeld.ExceptionalOrders CFSG.Blueprint.Chevalley

section Val

variable {p q e : ℕ}

theorem vp_pow_sub_one_of_not_dvd (hq : 1 ≤ q) (he : orderOf (q : ZMod p) = e)
    {d : ℕ} (hd : ¬ e ∣ d) : (q ^ d - 1).factorization p = 0 :=
  Nat.factorization_eq_zero_of_not_dvd fun h => hd ((dvd_pow_sub_one_iff_orderOf hq he).1 h)

theorem vp_pow_sub_one_of_dvd (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q)
    (hq : 2 ≤ q) (he : orderOf (q : ZMod p) = e) {k : ℕ} (hk : k ≠ 0) :
    (q ^ (e * k) - 1).factorization p = (q ^ e - 1).factorization p + k.factorization p := by
  have h := ordProj_pow_sub_one_of_dvd hp hp2 hpq hq he hk
  rw [← pow_add] at h
  exact Nat.pow_right_injective hp.two_le h

theorem vp_pow_sub_one (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q) (hq : 2 ≤ q)
    (he : orderOf (q : ZMod p) = e) {d : ℕ} (hd : d ≠ 0) (hside : e ∣ d → ¬ p ∣ d / e) :
    (q ^ d - 1).factorization p = if e ∣ d then (q ^ e - 1).factorization p else 0 := by
  by_cases hed : e ∣ d
  · rw [if_pos hed]
    obtain ⟨k, rfl⟩ := hed
    have hk : k ≠ 0 := fun h => hd (by rw [h, mul_zero])
    have he0 : e ≠ 0 := fun h => hd (by rw [h, zero_mul])
    rw [vp_pow_sub_one_of_dvd hp hp2 hpq hq he hk]
    have h1 := hside ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)] at h1
    rw [Nat.factorization_eq_zero_of_not_dvd h1, add_zero]
  · rw [if_neg hed, vp_pow_sub_one_of_not_dvd (by omega) he hed]

theorem geomSum_mul_sub_one (n s q : ℕ) (hq : 1 ≤ q) :
    geomSum n s q * (q ^ s - 1) = q ^ (s * n) - 1 := by
  have h1 : 1 ≤ q ^ s := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ (s * n) := Nat.one_le_pow _ _ hq
  have hz := geom_sum_mul ((q : ℤ) ^ s) n
  have e1 : ((geomSum n s q : ℕ) : ℤ) = ∑ i ∈ Finset.range n, ((q : ℤ) ^ s) ^ i := by
    simp only [geomSum, Nat.cast_sum, Nat.cast_pow, ← pow_mul]
  zify [h1, h2]
  rw [e1, hz, ← pow_mul]

theorem geomSum_pos {n : ℕ} (s : ℕ) {q : ℕ} (hn : 0 < n) (hq : 0 < q) : 0 < geomSum n s q :=
  Finset.sum_pos (fun _ _ => pow_pos hq _) ⟨0, Finset.mem_range.2 hn⟩

theorem factorization_geomSum (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q) (hq : 2 ≤ q)
    (he : orderOf (q : ZMod p) = e) {n s : ℕ} (hn : 0 < n) (hs : 0 < s)
    (h1 : e ∣ s * n → ¬ p ∣ s * n / e) (h2 : e ∣ s → ¬ p ∣ s / e) :
    (geomSum n s q).factorization p =
      if e ∣ s * n ∧ ¬ e ∣ s then (q ^ e - 1).factorization p else 0 := by
  have hG : geomSum n s q ≠ 0 := (geomSum_pos s hn (by omega)).ne'
  have hq1 : q ^ s - 1 ≠ 0 := by
    have : 1 < q ^ s := Nat.one_lt_pow hs.ne' (by omega)
    omega
  have hmul : (geomSum n s q * (q ^ s - 1)).factorization p = (q ^ (s * n) - 1).factorization p := by
    rw [geomSum_mul_sub_one n s q (by omega)]
  rw [Nat.factorization_mul hG hq1, Finsupp.add_apply,
    vp_pow_sub_one hp hp2 hpq hq he (Nat.mul_ne_zero hs.ne' hn.ne') h1,
    vp_pow_sub_one hp hp2 hpq hq he hs.ne' h2] at hmul
  by_cases hsn : e ∣ s * n
  · by_cases hes : e ∣ s
    · simp only [hsn, hes, if_true] at hmul
      simp only [hsn, hes, not_true_eq_false, and_false, if_false]
      omega
    · simp only [hsn, hes, if_true, if_false] at hmul
      simp only [hsn, hes, not_false_eq_true, and_self, if_true]
      omega
  · have hes : ¬ e ∣ s := fun h => hsn (h.mul_right n)
    simp only [hsn, hes, if_false] at hmul
    simp only [hsn, false_and, if_false]
    omega

@[expose] def GoodFactors (p e : ℕ) (fs : List (ℕ × ℕ)) : Prop :=
  ∀ f ∈ fs, 0 < f.1 ∧ 0 < f.2 ∧ (e ∣ f.2 * f.1 → ¬ p ∣ f.2 * f.1 / e) ∧
    (e ∣ f.2 → ¬ p ∣ f.2 / e)

@[expose] def cntFactors (e : ℕ) (fs : List (ℕ × ℕ)) : ℕ :=
  (fs.filter fun f => e ∣ f.2 * f.1 ∧ ¬ e ∣ f.2).length

theorem goodFactors_of_bound {fs : List (ℕ × ℕ)} {B : ℕ} (he : 0 < e) (hB : B < p * e)
    (hfs : ∀ f ∈ fs, 0 < f.1 ∧ 0 < f.2 ∧ f.2 * f.1 ≤ B) : GoodFactors p e fs := by
  intro f hf
  obtain ⟨h1, h2, h3⟩ := hfs f hf
  refine ⟨h1, h2, fun hd hpk => ?_, fun hd hpk => ?_⟩
  · obtain ⟨k, hk⟩ := hd
    rw [hk, Nat.mul_div_cancel_left _ he] at hpk
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk
        have := Nat.mul_pos h2 h1
        omega
      · exact h
    have := Nat.le_of_dvd hk0 hpk
    have h4 : e * p ≤ e * k := Nat.mul_le_mul_left e this
    rw [← hk] at h4
    nlinarith
  · obtain ⟨k, hk⟩ := hd
    rw [hk, Nat.mul_div_cancel_left _ he] at hpk
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk
        omega
      · exact h
    have := Nat.le_of_dvd hk0 hpk
    have h4 : e * p ≤ e * k := Nat.mul_le_mul_left e this
    rw [← hk] at h4
    have h5 : f.2 ≤ f.2 * f.1 := Nat.le_mul_of_pos_right _ h1
    nlinarith

theorem not_dvd_of_small_quot {k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6) : ¬ p ∣ k := by
  intro h
  have hk0 : 0 < k := by omega
  have hle := Nat.le_of_dvd hk0 h
  have hp6 : p ≤ 6 := by omega
  interval_cases p
  · rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  · norm_num at hp

theorem goodFactors_of_small {fs : List (ℕ × ℕ)} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hfs : ∀ f ∈ fs, 0 < f.1 ∧ 0 < f.2 ∧
      (e ∣ f.2 * f.1 → (f.2 * f.1 / e = 1 ∨ f.2 * f.1 / e = 2 ∨ f.2 * f.1 / e = 3 ∨
        f.2 * f.1 / e = 4 ∨ f.2 * f.1 / e = 6)) ∧
      (e ∣ f.2 → (f.2 / e = 1 ∨ f.2 / e = 2 ∨ f.2 / e = 3 ∨ f.2 / e = 4 ∨ f.2 / e = 6))) :
    GoodFactors p e fs := fun f hf => by
  obtain ⟨h1, h2, h3, h4⟩ := hfs f hf
  exact ⟨h1, h2, fun h => not_dvd_of_small_quot hp hp5 (h3 h),
    fun h => not_dvd_of_small_quot hp hp5 (h4 h)⟩

theorem factorization_prod_geomSum (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q) (hq : 2 ≤ q)
    (he : orderOf (q : ZMod p) = e) (fs : List (ℕ × ℕ)) (hfs : GoodFactors p e fs) :
    (fs.map fun f => geomSum f.1 f.2 q).prod ≠ 0 ∧
      ((fs.map fun f => geomSum f.1 f.2 q).prod).factorization p =
        (q ^ e - 1).factorization p * cntFactors e fs := by
  induction fs with
  | nil => simp [cntFactors]
  | cons f fs ih =>
    obtain ⟨ih0, ih1⟩ := ih fun g hg => hfs g (List.mem_cons_of_mem _ hg)
    obtain ⟨hn, hs, h1, h2⟩ := hfs f List.mem_cons_self
    have hG : geomSum f.1 f.2 q ≠ 0 := (geomSum_pos f.2 hn (by omega)).ne'
    rw [List.map_cons, List.prod_cons]
    refine ⟨mul_ne_zero hG ih0, ?_⟩
    rw [Nat.factorization_mul hG ih0, Finsupp.add_apply, ih1,
      factorization_geomSum hp hp2 hpq hq he hn hs h1 h2]
    unfold cntFactors
    by_cases hc : e ∣ f.2 * f.1 ∧ ¬ e ∣ f.2
    · rw [if_pos hc, List.filter_cons_of_pos (by simpa using hc), List.length_cons]
      ring
    · rw [if_neg hc, List.filter_cons_of_neg (by simpa using hc), zero_add]

theorem factorization_prod_lt_of_cnt_lt (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q)
    (hq : 2 ≤ q) (he : orderOf (q : ZMod p) = e) {fsJ fsI : List (ℕ × ℕ)}
    (hJ : GoodFactors p e fsJ) (hI : GoodFactors p e fsI)
    (hc : cntFactors e fsJ < cntFactors e fsI) :
    ((fsJ.map fun f => geomSum f.1 f.2 q).prod).factorization p <
      ((fsI.map fun f => geomSum f.1 f.2 q).prod).factorization p := by
  rw [(factorization_prod_geomSum hp hp2 hpq hq he fsJ hJ).2,
    (factorization_prod_geomSum hp hp2 hpq hq he fsI hI).2]
  have hdvd : p ∣ q ^ e - 1 := (dvd_pow_sub_one_iff_orderOf (by omega) he).2 dvd_rfl
  have hne : q ^ e - 1 ≠ 0 := by
    have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
    have : 1 < q ^ e := Nat.one_lt_pow he0 (by omega)
    omega
  have hm : 1 ≤ (q ^ e - 1).factorization p := hp.factorization_pos_of_dvd hne hdvd
  exact Nat.mul_lt_mul_of_pos_left hc hm

end Val

section Chain

variable {τ : Tag}

@[expose] def chainFactors (ss : List (ChainStep τ)) : List (ℕ × ℕ) :=
  ss.flatMap fun s => s.factors

theorem chain_prod_eq (ss : List (ChainStep τ)) (q : ℕ) :
    (ss.map fun s => s.value q).prod =
      ((chainFactors ss).map fun f => geomSum f.1 f.2 q).prod := by
  induction ss with
  | nil => simp [chainFactors]
  | cons s ss ih =>
    have e1 : chainFactors (s :: ss) = s.factors ++ chainFactors ss := by
      simp [chainFactors]
    rw [List.map_cons, List.prod_cons, ih, e1, List.map_append, List.prod_append]
    rfl

end Chain

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
