module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.Open.SporadicExistence
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.HardMathSupport.Dickson.I271.B3BLeaf

open CFSG.Open CFSG.ComponentClassification.CatLeaf

theorem seven_dvd_or_pow_six (q : ℕ) : 7 ∣ q ∨ 7 ∣ q ^ 6 - 1 := by
  by_cases h : q % 7 = 0
  · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
  · right
    have hq7 : q % 7 < 7 := Nat.mod_lt _ (by norm_num)
    have h1 : q ^ 6 % 7 = 1 := by
      rw [Nat.pow_mod]
      interval_cases hr : q % 7 <;> simp_all
    have h2 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega

theorem prime_dvd_baby {r : ℕ} (hr : r.Prime) (h : r ∣ orderBabyMonster) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 ∨ r = 23 ∨ r = 31 ∨
      r = 47 := by
  have key : ∀ q e : ℕ, q.Prime → r ∣ q ^ e → r = q := fun q e hq hd =>
    (Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow hd)
  have key1 : ∀ q : ℕ, q.Prime → r ∣ q → r = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hr hq).1 hd
  unfold orderBabyMonster at h
  simp only [Nat.Prime.dvd_mul hr, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (key 2 41 Nat.prime_two h)
  · exact Or.inr (Or.inl (key 3 13 Nat.prime_three h))
  · exact Or.inr (Or.inr (Or.inl (key 5 6 (by norm_num) h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key 7 2 (by norm_num) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key1 11 (by norm_num) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key1 13 (by norm_num) h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key1 17 (by norm_num) h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key1 19 (by norm_num) h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key1 23 (by norm_num) h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key1 31 (by norm_num) h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (key1 47 (by norm_num) h))))))))))

theorem prime_pow_dvd_baby {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k)
    (h : p ^ k ∣ orderBabyMonster) : (p = 2 ∧ k ≤ 41) ∨ p = 3 ∨ (p = 5 ∧ k ≤ 6) := by
  have hpd : p ∣ orderBabyMonster := (dvd_pow_self p (by omega)).trans h
  have hp3 : p ^ 3 ∣ orderBabyMonster := (pow_dvd_pow p hk).trans h
  rcases prime_dvd_baby hp hpd with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine Or.inl ⟨rfl, ?_⟩
    by_contra hk41
    exact absurd ((pow_dvd_pow 2 (by omega : 42 ≤ k)).trans h) (by decide +kernel)
  · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    by_contra hk6
    exact absurd ((pow_dvd_pow 5 (by omega : 7 ≤ k)).trans h) (by decide +kernel)
  all_goals exact absurd hp3 (by decide +kernel)

theorem seven_dvd_of_mul_eq {X D u P : ℕ} (hDu : D ∣ u) (hD : 0 < D) (huu : u * u ∣ P)
    (h7 : 7 ∣ P) (hX : X * D = P) : 7 ∣ X := by
  by_cases h7D : 7 ∣ D
  · have h7u : 7 ∣ u := h7D.trans hDu
    obtain ⟨e, he⟩ := hDu
    have h2 : u * u = D * (e * u) := by
      calc u * u = D * e * u := by rw [← he]
        _ = D * (e * u) := by ring
    have h3 : D * (e * u) ∣ D * X := by
      rw [← h2, mul_comm D X, hX]
      exact huu
    exact h7u.trans ((dvd_mul_left u e).trans (Nat.dvd_of_mul_dvd_mul_left hD h3))
  · rw [← hX] at h7
    exact ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h7).resolve_right h7D

theorem seven_dvd_of_coprime {X D P : ℕ} (h7 : 7 ∣ P) (hD : ¬ 7 ∣ D) (hX : X * D = P) :
    7 ∣ X := by
  rw [← hX] at h7
  exact ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h7).resolve_right hD

theorem not_seven_dvd_of_dvd_three {D : ℕ} (h : D ∣ 3) : ¬ 7 ∣ D := fun h7 => by
  have := Nat.le_of_dvd (by norm_num) (h7.trans h)
  omega

@[expose] def Dead (t : StatedLieTag) (n q : ℕ) : Prop :=
  (7 ∣ lieOrderNumerator t n q ∨
      ¬ lieOrderNumerator t n q ∣ lieOrderDivisor t n q * orderBabyMonster) ∧
    ¬ 7 ∣ lieOrderDivisor t n q

instance (t : StatedLieTag) (n q : ℕ) : Decidable (Dead t n q) :=
  inferInstanceAs (Decidable ((_ ∨ _) ∧ _))

theorem not_dead {t : StatedLieTag} {n q X : ℕ} (hX : X * lieOrderDivisor t n q =
    lieOrderNumerator t n q) (hd : X ∣ orderBabyMonster) (h7 : ¬ 7 ∣ X) : ¬ Dead t n q := by
  rintro ⟨h | h, hD⟩
  · exact h7 (seven_dvd_of_coprime h hD hX)
  · exact h (by rw [← hX, mul_comm (lieOrderDivisor t n q)]; exact mul_dvd_mul_right hd _)

theorem seven_dvd_e6 {q X : ℕ}
    (hX : X * lieOrderDivisor .E6 0 q = lieOrderNumerator .E6 0 q) : 7 ∣ X := by
  refine seven_dvd_of_coprime ?_ (not_seven_dvd_of_dvd_three (Nat.gcd_dvd_left 3 (q - 1))) hX
  show 7 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
    (q ^ 2 - 1)
  rcases seven_dvd_or_pow_six q with h | h
  · exact (h.trans (dvd_pow_self q (by norm_num : (36 : ℕ) ≠ 0))).trans
      ⟨(q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1),
        by ring⟩
  · exact h.trans ⟨q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1), by ring⟩

theorem seven_dvd_twistedE6 {q X : ℕ}
    (hX : X * lieOrderDivisor .twistedE6 0 q = lieOrderNumerator .twistedE6 0 q) : 7 ∣ X := by
  refine seven_dvd_of_coprime ?_ (not_seven_dvd_of_dvd_three (Nat.gcd_dvd_left 3 (q + 1))) hX
  show 7 ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
    (q ^ 2 - 1)
  rcases seven_dvd_or_pow_six q with h | h
  · exact (h.trans (dvd_pow_self q (by norm_num : (36 : ℕ) ≠ 0))).trans
      ⟨(q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1),
        by ring⟩
  · exact h.trans ⟨q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1), by ring⟩

theorem seven_dvd_psl {n q X : ℕ} (hn : 6 ≤ n)
    (hX : X * lieOrderDivisor .PSL n q = lieOrderNumerator .PSL n q) : 7 ∣ X := by
  have hnum : lieOrderNumerator .PSL n q =
      q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) := rfl
  have hdiv : lieOrderDivisor .PSL n q = Nat.gcd n (q - 1) := rfl
  rw [hnum, hdiv] at hX
  have hN : n * (n - 1) / 2 ≠ 0 := by
    have := Nat.mul_le_mul hn (show 5 ≤ n - 1 by omega)
    omega
  refine seven_dvd_of_mul_eq (u := q - 1) (Nat.gcd_dvd_right _ _)
    (Nat.gcd_pos_of_pos_left _ (by omega)) ?_ ?_ hX
  · refine Dvd.dvd.mul_left ?_ _
    have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_Icc]
      omega
    refine Dvd.dvd.trans ?_ (Finset.prod_dvd_prod_of_subset _ _ (fun i => q ^ i - 1) hsub)
    rw [Finset.prod_pair (by norm_num)]
    have h2 := Nat.sub_dvd_pow_sub_pow q 1 2
    have h3 := Nat.sub_dvd_pow_sub_pow q 1 3
    rw [one_pow] at h2 h3
    exact mul_dvd_mul h2 h3
  · rcases seven_dvd_or_pow_six q with h | h
    · exact (h.trans (dvd_pow_self q hN)).mul_right _
    · exact Dvd.dvd.mul_left (h.trans (Finset.dvd_prod_of_mem (fun i => q ^ i - 1)
        (Finset.mem_Icc.2 ⟨by norm_num, hn⟩))) _

theorem seven_dvd_psu {n q X : ℕ} (hn : 6 ≤ n)
    (hX : X * lieOrderDivisor .PSU n q = lieOrderNumerator .PSU n q) : 7 ∣ X := by
  have hnum : lieOrderNumerator .PSU n q = q ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1) := rfl
  have hdiv : lieOrderDivisor .PSU n q = Nat.gcd n (q + 1) := rfl
  rw [hnum, hdiv] at hX
  have hN : n * (n - 1) / 2 ≠ 0 := by
    have := Nat.mul_le_mul hn (show 5 ≤ n - 1 by omega)
    omega
  refine seven_dvd_of_mul_eq (u := q + 1) (Nat.gcd_dvd_right _ _)
    (Nat.gcd_pos_of_pos_left _ (by omega)) ?_ ?_ hX
  · refine Dvd.dvd.mul_left ?_ _
    have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_Icc]
      omega
    refine Dvd.dvd.trans ?_ (Finset.prod_dvd_prod_of_subset _ _
      (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hsub)
    rw [Finset.prod_pair (by norm_num), if_pos (show Even 2 by decide),
      if_neg (show ¬ Even 3 by decide)]
    have h2 : q + 1 ∣ q ^ 2 - 1 := by
      have := Nat.mul_self_sub_mul_self_eq q 1
      rw [mul_one, ← pow_two] at this
      exact ⟨q - 1, this⟩
    have h3 : q + 1 ∣ q ^ 3 + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow q 1 (show Odd 3 by decide)
      rwa [one_pow] at this
    exact mul_dvd_mul h2 h3
  · rcases seven_dvd_or_pow_six q with h | h
    · exact (h.trans (dvd_pow_self q hN)).mul_right _
    · refine Dvd.dvd.mul_left (h.trans ?_) _
      have := Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1)
        (Finset.mem_Icc.2 ⟨(by norm_num : 2 ≤ 6), hn⟩)
      rwa [if_pos (show Even 6 by decide)] at this

theorem psl_three_two :
    ∀ f ∈ Finset.Icc 1 13, 3 ∣ 2 ^ f - 1 → Dead .PSL 3 (2 ^ f) := by decide +kernel

theorem psl_three_five :
    ∀ f ∈ Finset.Icc 1 2, 3 ∣ 5 ^ f - 1 → Dead .PSL 3 (5 ^ f) := by decide +kernel

theorem psu_three_two :
    ∀ f ∈ Finset.Icc 1 13, 3 ∣ 2 ^ f + 1 → f ≠ 1 → Dead .PSU 3 (2 ^ f) := by decide +kernel

theorem psu_three_five :
    ∀ f ∈ Finset.Icc 1 2, 3 ∣ 5 ^ f + 1 → Dead .PSU 3 (5 ^ f) := by decide +kernel

theorem psl_three_false {p f X : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (h3 : 3 ∣ p ^ f - 1)
    (hX : X * lieOrderDivisor .PSL 3 (p ^ f) = lieOrderNumerator .PSL 3 (p ^ f))
    (hsyl : p ^ (3 * f) ∣ X) (hdvd : X ∣ orderBabyMonster) (h7 : ¬ 7 ∣ X) : False := by
  rcases prime_pow_dvd_baby hp (by omega) (hsyl.trans hdvd) with ⟨rfl, hk⟩ | rfl | ⟨rfl, hk⟩
  · exact not_dead hX hdvd h7 (psl_three_two f (Finset.mem_Icc.2 ⟨hf, by omega⟩) h3)
  · have h3q : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have h1 : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    omega
  · exact not_dead hX hdvd h7 (psl_three_five f (Finset.mem_Icc.2 ⟨hf, by omega⟩) h3)

theorem psu_three_false {p f X : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hne : p ^ f ≠ 2)
    (h3 : 3 ∣ p ^ f + 1)
    (hX : X * lieOrderDivisor .PSU 3 (p ^ f) = lieOrderNumerator .PSU 3 (p ^ f))
    (hsyl : p ^ (3 * f) ∣ X) (hdvd : X ∣ orderBabyMonster) (h7 : ¬ 7 ∣ X) : False := by
  rcases prime_pow_dvd_baby hp (by omega) (hsyl.trans hdvd) with ⟨rfl, hk⟩ | rfl | ⟨rfl, hk⟩
  · exact not_dead hX hdvd h7 (psu_three_two f (Finset.mem_Icc.2 ⟨hf, by omega⟩) h3
      fun h1 => hne (by rw [h1]; norm_num))
  · have h3q : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  · exact not_dead hX hdvd h7 (psu_three_five f (Finset.mem_Icc.2 ⟨hf, by omega⟩) h3)

theorem dead_orthogonal_odd : Dead .POmegaOdd 3 3 := by decide +kernel

theorem dead_g2 : Dead .G2 0 3 := by decide +kernel

theorem dead_unitary_four : Dead .PSU 4 3 := by decide +kernel

end CFSG.HardMathSupport.Dickson.I271.B3BLeaf
