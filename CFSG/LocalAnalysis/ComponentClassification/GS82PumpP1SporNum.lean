module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.SporNum

open CFSG Assembly.LowTwoRank CatLeaf HarrisLit.T1.SporRow
open CFSG.ComponentClassification.GSThmB.QPUSpor (exists_eq_of_prime_dvd_prod)

@[expose] def admB : StatedLieTag → ℕ → ℕ → ℕ → Bool
  | .PSL, n, p, f => 2 ≤ n && !(n == 2 && p ^ f == 2) && !(n == 2 && p ^ f == 3)
  | .PSU, n, p, f => 3 ≤ n && !(n == 3 && p ^ f == 2)
  | .PSp, n, p, f => 2 ≤ n && !(n == 2 && p ^ f == 2)
  | .POmegaOdd, n, p, _ => 3 ≤ n && p != 2
  | .POmegaPlus, n, _, _ => 4 ≤ n
  | .POmegaMinus, n, _, _ => 4 ≤ n
  | .G2, n, p, f => n == 0 && 3 ≤ p ^ f
  | .F4, n, _, _ => n == 0
  | .E6, n, _, _ => n == 0
  | .E7, n, _, _ => n == 0
  | .E8, n, _, _ => n == 0
  | .twistedE6, n, _, _ => n == 0
  | .trialityD4, n, _, _ => n == 0
  | .twistedB2, n, p, f => n == 0 && p == 2 && 3 ≤ f
  | .twistedF4, n, p, f => n == 0 && p == 2 && 3 ≤ f
  | .twistedG2, n, p, f => n == 0 && p == 3 && 3 ≤ f
  | .Tits, n, p, f => n == 0 && p == 2 && f == 1

theorem admB_of_admissible {τ : StatedLieTag} {n p f : ℕ} (h : StatedLieAdmissible τ n p f) :
    admB τ n p f = true := by
  obtain ⟨-, -, h⟩ := h
  cases τ <;> simp_all [admB] <;> tauto

@[expose] def lieDivOrder (τ : StatedLieTag) (n q : ℕ) : ℕ :=
  lieOrderNumerator τ n q / lieOrderDivisor τ n q

@[expose] def lieDivCand (N p e : ℕ) (ok : ℕ → Bool) (L : List (StatedLieTag × ℕ × ℕ × ℕ))
    (τ : StatedLieTag) (n f : ℕ) : Bool :=
  f == 0 || e < lieSylowExponent τ n * f || !admB τ n p f ||
    (lieOrderDivisor τ n (p ^ f) != 0 &&
      (lieOrderNumerator τ n (p ^ f) % lieOrderDivisor τ n (p ^ f) != 0 ||
        N % lieDivOrder τ n (p ^ f) != 0 || !ok (lieDivOrder τ n (p ^ f)) ||
        decide ((τ, n, p, f) ∈ L)))

@[expose] def lieDivCheck (N : ℕ) (l : List (ℕ × ℕ)) (ok : ℕ → Bool)
    (L : List (StatedLieTag × ℕ × ℕ × ℕ)) : Bool :=
  l.all fun x => x.1 == 2 || allTags.all fun τ => (List.range (x.2 + 2)).all fun n =>
    (List.range (x.2 + 1)).all fun f => lieDivCand N x.1 x.2 ok L τ n f

theorem mem_of_lieDivCheck {N : ℕ} {l : List (ℕ × ℕ)} {ok : ℕ → Bool}
    {L : List (StatedLieTag × ℕ × ℕ × ℕ)}
    (hl : (l.map fun x => x.1 ^ x.2).prod = N) (hpr : ∀ x ∈ l, x.1.Prime)
    (hnd : (l.map Prod.fst).Nodup) (hc : lieDivCheck N l ok L = true)
    {c : ℕ} {τ : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (ha : StatedLieAdmissible τ n p f)
    (hnum : c * lieOrderDivisor τ n (p ^ f) = lieOrderNumerator τ n (p ^ f))
    (hfac : c.factorization p = lieSylowExponent τ n * f) (hdvd : c ∣ N) (hok : ok c = true) :
    (τ, n, p, f) ∈ L := by
  obtain ⟨hN1, hnN⟩ := lieSylowExponent_bounds ha
  have hp : p.Prime := ha.1
  have hf1 : 1 ≤ f := ha.2.1
  have hNf : lieSylowExponent τ n ≤ lieSylowExponent τ n * f := Nat.le_mul_of_pos_right _ hf1
  have hfN : f ≤ lieSylowExponent τ n * f := Nat.le_mul_of_pos_left _ hN1
  have hN0 : 0 < N := hl ▸ prod_pos_of_prime hpr
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hN0.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  have hpc : p ∣ c := Nat.dvd_of_factorization_pos (by rw [hfac]; omega)
  obtain ⟨x, hx, rfl⟩ := exists_eq_of_prime_dvd_prod hp hpr (hl ▸ hpc.trans hdvd)
  have he : N.factorization x.1 = x.2 := hl ▸ factorization_prod_of_mem hpr hnd x hx
  have hle : c.factorization x.1 ≤ N.factorization x.1 :=
    (Nat.factorization_le_iff_dvd hc0 hN0.ne').2 hdvd x.1
  rw [he, hfac] at hle
  rw [lieDivCheck, List.all_eq_true] at hc
  have h1 := hc x hx
  simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h1
  rcases h1 with h2 | h1
  · exact absurd h2 hp2
  have h3 := h1 τ (mem_allTags τ) n (by omega) f (by omega)
  have hadm := admB_of_admissible ha
  simp only [lieDivCand, lieDivOrder, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_true', Bool.and_eq_true, bne_iff_ne, ne_eq] at h3
  rcases h3 with ((h0 | hlt) | hb) | ⟨hd, (((hmod | hN) | hko) | hmem)⟩
  · omega
  · omega
  · rw [hadm] at hb
    exact absurd hb (by decide)
  · exact absurd (by rw [← hnum, Nat.mul_mod_left]) hmod
  · rw [← hnum, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd)] at hN
    exact absurd (Nat.mod_eq_zero_of_dvd hdvd) hN
  · rw [← hnum, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd), hok] at hko
    exact absurd hko (by decide)
  · exact hmem

theorem not_oddLieOrder_of_lieDivCheck {N : ℕ} {l : List (ℕ × ℕ)} {ok : ℕ → Bool}
    (hl : (l.map fun x => x.1 ^ x.2).prod = N) (hpr : ∀ x ∈ l, x.1.Prime)
    (hnd : (l.map Prod.fst).Nodup) (hc : lieDivCheck N l ok [] = true) {c : ℕ}
    (hdvd : c ∣ N) (hok : ok c = true) : ¬ OddLieOrder c := by
  rintro ⟨τ, n, p, f, -, hp2, ha, h1, h2⟩
  exact List.not_mem_nil (mem_of_lieDivCheck hl hpr hnd hc hp2 ha h1 h2 hdvd hok)

theorem not_oddLieOrder_ru {c : ℕ} (hd : c ∣ 145926144000) (h3 : ¬ 3 ∣ c) :
    ¬ OddLieOrder c :=
  not_oddLieOrder_of_lieDivCheck (ok := fun c => c % 3 != 0)
    (l := [(2, 14), (3, 3), (5, 3), (7, 1), (13, 1), (29, 1)]) (by norm_num)
    (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel) hd
    (by simpa [Nat.dvd_iff_mod_eq_zero] using h3)

theorem not_oddLieOrder_monster {c : ℕ}
    (hd : c ∣ 808017424794512875886459904961710757005754368000000000)
    (h41 : 2 ^ 41 ∣ c) (h42 : ¬ 2 ^ 42 ∣ c) : ¬ OddLieOrder c :=
  not_oddLieOrder_of_lieDivCheck (ok := fun c => c % 2 ^ 41 == 0 && c % 2 ^ 42 != 0)
    (l := [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3), (17, 1), (19, 1), (23, 1),
      (29, 1), (31, 1), (41, 1), (47, 1), (59, 1), (71, 1)]) (by norm_num)
    (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel) hd
    (by simp [Nat.dvd_iff_mod_eq_zero] at h41 h42 ⊢; exact ⟨h41, h42⟩)

theorem not_oddLieOrder_A10 : ¬ OddLieOrder 1814400 :=
  not_oddLieOrder_of_check (l := [(2, 7), (3, 4), (5, 2), (7, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_M11 : ¬ OddLieOrder 7920 :=
  not_oddLieOrder_of_check (l := [(2, 4), (3, 2), (5, 1), (11, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_O8p2 : ¬ OddLieOrder 174182400 :=
  not_oddLieOrder_of_check (l := [(2, 12), (3, 5), (5, 2), (7, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_Fi23 : ¬ OddLieOrder 4089470473293004800 :=
  not_oddLieOrder_of_check
    (l := [(2, 18), (3, 13), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (23, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_J2 : ¬ OddLieOrder 604800 :=
  not_oddLieOrder_of_check (l := [(2, 7), (3, 3), (5, 2), (7, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

theorem not_oddLieOrder_J1 : ¬ OddLieOrder 175560 :=
  not_oddLieOrder_of_check (l := [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (19, 1)])
    (by norm_num) (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel)

end CFSG.ComponentClassification.GS82PumpInputs.SporNum
