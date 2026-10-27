module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Assembly.LowTwoRank CatLeaf
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporFactors sporOrder sporFactors_prime
  sporFactors_nodup exists_eq_of_prime_dvd_prod)

@[expose] def OddLieOrder (m : ℕ) : Prop :=
  ∃ (τ : StatedLieTag) (n p f : ℕ), p.Prime ∧ p ≠ 2 ∧ StatedLieAdmissible τ n p f ∧
    m * lieOrderDivisor τ n (p ^ f) = lieOrderNumerator τ n (p ^ f) ∧
    m.factorization p = lieSylowExponent τ n * f

@[expose] def IndShape (τ : StatedLieTag) (n p f : ℕ) : Prop :=
  (τ = .POmegaOdd ∧ n = 3) ∨ (τ = .PSL ∧ n = 4) ∨ (τ = .PSU ∧ n = 4) ∨ (τ = .PSp ∧ n = 2) ∨
    (τ = .PSL ∧ n = 2 ∧ Even f) ∨ (p = 3 ∧ f = 1)

@[expose] def IndLieOrder (m : ℕ) : Prop :=
  ∃ (τ : StatedLieTag) (n p f : ℕ), p.Prime ∧ p ≠ 2 ∧ StatedLieAdmissible τ n p f ∧
    IndShape τ n p f ∧ m * lieOrderDivisor τ n (p ^ f) = lieOrderNumerator τ n (p ^ f) ∧
    m.factorization p = lieSylowExponent τ n * f

theorem IndLieOrder.oddLieOrder {m : ℕ} (h : IndLieOrder m) : OddLieOrder m := by
  obtain ⟨τ, n, p, f, hp, hp2, ha, -, h1, h2⟩ := h
  exact ⟨τ, n, p, f, hp, hp2, ha, h1, h2⟩

theorem tri_bounds {k : ℕ} (hk : 2 ≤ k) : 1 ≤ k * (k - 1) / 2 ∧ k ≤ k * (k - 1) / 2 + 1 := by
  have h : 2 * (k - 1) ≤ k * (k - 1) := Nat.mul_le_mul_right _ hk
  generalize k * (k - 1) = X at h ⊢
  omega

theorem tri_three {k : ℕ} (hk : 3 ≤ k) : 3 ≤ k * (k - 1) / 2 := by
  have h : 3 * 2 ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
  generalize k * (k - 1) = X at h ⊢
  omega

theorem rect_bounds' {k : ℕ} (hk : 4 ≤ k) : 12 ≤ k * (k - 1) :=
  Nat.mul_le_mul (by omega : 4 ≤ k) (by omega : 3 ≤ k - 1)

theorem rect_bounds {k : ℕ} (hk : 4 ≤ k) : 1 ≤ k * (k - 1) ∧ k ≤ k * (k - 1) + 1 := by
  have h : k * 1 ≤ k * (k - 1) := Nat.mul_le_mul_left _ (by omega)
  have h' := rect_bounds' hk
  generalize k * (k - 1) = X at h h' ⊢
  omega

theorem lieSylowExponent_bounds {τ : StatedLieTag} {n p f : ℕ}
    (h : StatedLieAdmissible τ n p f) :
    1 ≤ lieSylowExponent τ n ∧ n ≤ lieSylowExponent τ n + 1 := by
  obtain ⟨-, -, h⟩ := h
  cases τ
  · exact tri_bounds h.1
  · exact tri_bounds (by have := h.1; omega)
  · have := h.1
    simp only [lieSylowExponent]
    constructor <;> nlinarith
  · have := h.1
    simp only [lieSylowExponent]
    constructor <;> nlinarith
  · exact rect_bounds h
  · exact rect_bounds h
  all_goals (obtain ⟨rfl, -⟩ := h; simp only [lieSylowExponent]; omega)

theorem two_le_lieSylowExponent_three {τ : StatedLieTag} {n : ℕ}
    (h : StatedLieAdmissible τ n 3 1) : 2 ≤ lieSylowExponent τ n := by
  obtain ⟨-, -, h⟩ := h
  cases τ
  · obtain ⟨h2, -, h3⟩ := h
    have hn : 3 ≤ n := by
      by_contra hn
      exact h3 (by rw [show n = 2 by omega]; norm_num)
    have := tri_three hn
    simp only [lieSylowExponent]
    omega
  · have := tri_three h.1
    simp only [lieSylowExponent]
    omega
  · have := h.1
    simp only [lieSylowExponent]
    nlinarith
  · have := h.1
    simp only [lieSylowExponent]
    nlinarith
  · exact (rect_bounds' h).trans' (by norm_num)
  · exact (rect_bounds' h).trans' (by norm_num)
  all_goals (simp only [lieSylowExponent]; omega)

theorem prod_pos_of_prime {l : List (ℕ × ℕ)} (hl : ∀ x ∈ l, x.1.Prime) :
    0 < (l.map fun x => x.1 ^ x.2).prod := by
  apply List.prod_pos
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  exact pow_pos (hl x hx).pos _

theorem factorization_prod_of_mem :
    ∀ {l : List (ℕ × ℕ)}, (∀ x ∈ l, x.1.Prime) → (l.map Prod.fst).Nodup → ∀ x ∈ l,
      ((l.map fun y : ℕ × ℕ => y.1 ^ y.2).prod).factorization x.1 = x.2
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | y :: l, hl, hnd, x, hx => by
    rw [List.map_cons, List.prod_cons]
    rw [List.map_cons, List.nodup_cons] at hnd
    have hy := hl y (by simp)
    have hl' : ∀ z ∈ l, z.1.Prime := fun z hz => hl z (List.mem_cons_of_mem _ hz)
    rw [Nat.factorization_mul (pow_ne_zero _ hy.ne_zero) (prod_pos_of_prime hl').ne',
      Finsupp.add_apply, hy.factorization_pow, Finsupp.single_apply]
    rcases List.mem_cons.1 hx with rfl | hx'
    · rw [ite_eq_left rfl, Nat.factorization_eq_zero_of_not_dvd, add_zero]
      intro hd
      obtain ⟨z, hz, hyz⟩ := exists_eq_of_prime_dvd_prod hy hl' hd
      exact hnd.1 (hyz ▸ List.mem_map_of_mem hz)
    · have hne : y.1 ≠ x.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hx')
      rw [ite_eq_right hne, zero_add]
      exact factorization_prod_of_mem hl' hnd.2 x hx'

@[expose] def allTags : List StatedLieTag :=
  [.PSL, .PSU, .PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus, .G2, .F4, .E6, .E7, .E8, .twistedE6,
    .trialityD4, .twistedB2, .twistedG2, .twistedF4, .Tits]

theorem mem_allTags (τ : StatedLieTag) : τ ∈ allTags := by
  cases τ <;> simp [allTags]

@[expose] def lieCand (m p e : ℕ) (τ : StatedLieTag) (n f : ℕ) : Bool :=
  f == 0 || lieSylowExponent τ n * f != e ||
    lieOrderNumerator τ n (p ^ f) != m * lieOrderDivisor τ n (p ^ f)

@[expose] def oddLieCheck (m : ℕ) (l : List (ℕ × ℕ)) : Bool :=
  l.all fun x => x.1 == 2 || allTags.all fun τ => (List.range (x.2 + 2)).all fun n =>
    (List.range (x.2 + 1)).all fun f => lieCand m x.1 x.2 τ n f

theorem not_oddLieOrder_of_check {m : ℕ} {l : List (ℕ × ℕ)}
    (hl : (l.map fun x => x.1 ^ x.2).prod = m) (hpr : ∀ x ∈ l, x.1.Prime)
    (hnd : (l.map Prod.fst).Nodup) (hc : oddLieCheck m l = true) : ¬ OddLieOrder m := by
  rintro ⟨τ, n, p, f, hp, hp2, ha, hnum, hfac⟩
  obtain ⟨hN1, hnN⟩ := lieSylowExponent_bounds ha
  have hf1 : 1 ≤ f := ha.2.1
  have hNf : lieSylowExponent τ n ≤ lieSylowExponent τ n * f := Nat.le_mul_of_pos_right _ hf1
  have hfN : f ≤ lieSylowExponent τ n * f := Nat.le_mul_of_pos_left _ hN1
  have hm : 0 < m := hl ▸ prod_pos_of_prime hpr
  have hpd : p ∣ m := Nat.dvd_of_factorization_pos (by rw [hfac]; omega)
  obtain ⟨x, hx, rfl⟩ := exists_eq_of_prime_dvd_prod hp hpr (hl ▸ hpd)
  have he : m.factorization x.1 = x.2 := hl ▸ factorization_prod_of_mem hpr hnd x hx
  rw [he] at hfac
  rw [oddLieCheck, List.all_eq_true] at hc
  have h1 := hc x hx
  simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h1
  rcases h1 with h2 | h1
  · exact hp2 h2
  have h3 := h1 τ (mem_allTags τ) n (by omega) f (by omega)
  simp only [lieCand, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h3
  rcases h3 with (h0 | hN) | hne
  · omega
  · exact hN hfac.symm
  · exact hne hnum.symm

theorem IndLieOrder.exists_sq_dvd {m : ℕ} (hm : m ≠ 0) (h : IndLieOrder m) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ m := by
  obtain ⟨τ, n, p, f, hp, hp2, ha, hs, -, hfac⟩ := h
  refine ⟨p, hp, hp2, (hp.pow_dvd_iff_le_factorization hm).2 ?_⟩
  rw [hfac]
  have hf1 : 1 ≤ f := ha.2.1
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, k, rfl⟩ |
      ⟨rfl, rfl⟩
  · simp only [lieSylowExponent]
    omega
  · simp only [lieSylowExponent]
    omega
  · simp only [lieSylowExponent]
    omega
  · simp only [lieSylowExponent]
    omega
  · simp only [lieSylowExponent]
    omega
  · have := two_le_lieSylowExponent_three ha
    omega

theorem three_dvd_sq_sub_one {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have h1 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> rw [h]
  have h2 : 1 ≤ q ^ 2 := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · simp at hq
    · exact Nat.one_le_pow _ _ h
  omega

theorem IndLieOrder.three_dvd {m : ℕ} (h : IndLieOrder m) : 3 ∣ m := by
  obtain ⟨τ, n, p, f, hp, hp2, ha, hs, hnum, hfac⟩ := h
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨hN1, -⟩ := lieSylowExponent_bounds ha
    have hf1 : 1 ≤ f := ha.2.1
    have hNf : 1 ≤ lieSylowExponent τ n * f := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact Nat.dvd_of_factorization_pos (by rw [hfac]; omega)
  have hq : ¬ 3 ∣ p ^ f := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have h3 := three_dvd_sq_sub_one hq
  have key : ∀ d : ℕ, d ∣ 4 → 3 ∣ m * d → 3 ∣ m := fun d hd h =>
    (Nat.Coprime.coprime_dvd_right hd (by norm_num : Nat.Coprime 3 4)).dvd_of_dvd_mul_right h
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩ | ⟨h3', -⟩
  · refine key 2 (by norm_num) ?_
    rw [show lieOrderDivisor .POmegaOdd 3 (p ^ f) = 2 from rfl] at hnum
    rw [hnum]
    simp only [lieOrderNumerator]
    exact Dvd.dvd.mul_left (h3.trans ((by norm_num : (p ^ f) ^ (2 * 1) - 1 = (p ^ f) ^ 2 - 1) ▸
      Finset.dvd_prod_of_mem (fun i => (p ^ f) ^ (2 * i) - 1)
        (Finset.mem_Icc.2 ⟨le_rfl, by norm_num⟩))) _
  · refine key (Nat.gcd 4 (p ^ f - 1)) (Nat.gcd_dvd_left 4 _) ?_
    rw [show lieOrderDivisor .PSL 4 (p ^ f) = Nat.gcd 4 (p ^ f - 1) from rfl] at hnum
    rw [hnum]
    simp only [lieOrderNumerator]
    exact Dvd.dvd.mul_left (h3.trans (Finset.dvd_prod_of_mem (fun i => (p ^ f) ^ i - 1)
      (Finset.mem_Icc.2 ⟨le_rfl, by norm_num⟩))) _
  · refine key (Nat.gcd 4 (p ^ f + 1)) (Nat.gcd_dvd_left 4 _) ?_
    rw [show lieOrderDivisor .PSU 4 (p ^ f) = Nat.gcd 4 (p ^ f + 1) from rfl] at hnum
    rw [hnum]
    simp only [lieOrderNumerator]
    refine Dvd.dvd.mul_left (h3.trans ?_) _
    have := Finset.dvd_prod_of_mem
      (fun i => if Even i then (p ^ f) ^ i - 1 else (p ^ f) ^ i + 1)
      (Finset.mem_Icc.2 ⟨le_rfl, (by norm_num : 2 ≤ 4)⟩)
    simpa using this
  · refine key (Nat.gcd 2 (p ^ f - 1)) (Nat.dvd_trans (Nat.gcd_dvd_left 2 _) (by norm_num)) ?_
    rw [show lieOrderDivisor .PSp 2 (p ^ f) = Nat.gcd 2 (p ^ f - 1) from rfl] at hnum
    rw [hnum]
    simp only [lieOrderNumerator]
    exact Dvd.dvd.mul_left (h3.trans ((by norm_num : (p ^ f) ^ (2 * 1) - 1 = (p ^ f) ^ 2 - 1) ▸
      Finset.dvd_prod_of_mem (fun i => (p ^ f) ^ (2 * i) - 1)
        (Finset.mem_Icc.2 ⟨le_rfl, by norm_num⟩))) _
  · refine key (Nat.gcd 2 (p ^ f - 1)) (Nat.dvd_trans (Nat.gcd_dvd_left 2 _) (by norm_num)) ?_
    rw [show lieOrderDivisor .PSL 2 (p ^ f) = Nat.gcd 2 (p ^ f - 1) from rfl] at hnum
    rw [hnum]
    simp only [lieOrderNumerator]
    exact Dvd.dvd.mul_left (h3.trans (Finset.dvd_prod_of_mem (fun i => (p ^ f) ^ i - 1)
      (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩))) _
  · exact absurd h3' hp3

theorem not_oddLieOrder_sporOrder (s : TauCeti.SporadicName) : ¬ OddLieOrder (sporOrder s) :=
  not_oddLieOrder_of_check rfl (sporFactors_prime s) (sporFactors_nodup s)
    (by cases s <;> decide +kernel)

theorem not_oddLieOrder_G24 : ¬ OddLieOrder 251596800 :=
  not_oddLieOrder_of_check
    (l := [(2, 12), (3, 3), (5, 2), (7, 1), (13, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_HS : ¬ OddLieOrder 44352000 :=
  not_oddLieOrder_of_check
    (l := [(2, 9), (3, 2), (5, 3), (7, 1), (11, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_U62 : ¬ OddLieOrder 9196830720 :=
  not_oddLieOrder_of_check
    (l := [(2, 15), (3, 6), (5, 1), (7, 1), (11, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_Fi22 : ¬ OddLieOrder 64561751654400 :=
  not_oddLieOrder_of_check
    (l := [(2, 17), (3, 9), (5, 2), (7, 1), (11, 1), (13, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_E62 : ¬ OddLieOrder 76532479683774853939200 :=
  not_oddLieOrder_of_check
    (l := [(2, 36), (3, 9), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_F42 : ¬ OddLieOrder 3311126603366400 :=
  not_oddLieOrder_of_check
    (l := [(2, 24), (3, 6), (5, 2), (7, 2), (13, 1), (17, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_A11 : ¬ OddLieOrder 19958400 :=
  not_oddLieOrder_of_check
    (l := [(2, 7), (3, 4), (5, 2), (7, 1), (11, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_L34 : ¬ OddLieOrder 20160 :=
  not_oddLieOrder_of_check
    (l := [(2, 6), (3, 2), (5, 1), (7, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_Sp62 : ¬ OddLieOrder 1451520 :=
  not_oddLieOrder_of_check
    (l := [(2, 9), (3, 4), (5, 1), (7, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_M12 : ¬ OddLieOrder 95040 :=
  not_oddLieOrder_of_check
    (l := [(2, 6), (3, 3), (5, 1), (11, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_B : ¬ OddLieOrder 4154781481226426191177580544000000 :=
  not_oddLieOrder_of_check
    (l := [(2, 41), (3, 13), (5, 6), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1),
        (47, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
