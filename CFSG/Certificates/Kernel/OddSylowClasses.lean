module

public import CFSG.Certificates.Kernel.OddSylowSound

public section

namespace CFSG.KS.OddSyl

open CFSG.KD.OddSyl CFSG.Sporadic.Schreier CFSG.GroupTheory.SylowOddClasses

variable {n : ℕ}

theorem factorization_pow_mul {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    (p ^ k * m).factorization p = k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hm0, Finsupp.add_apply,
    hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

theorem mem_of_prime_dvd_prod {q : ℕ} (hq : q.Prime) :
    ∀ {l : List ℕ}, (∀ p ∈ l, p.Prime) → q ∣ l.prod → q ∈ l
  | [], _, h => (hq.ne_one (Nat.dvd_one.1 (by simpa using h))).elim
  | a :: l, hl, h => by
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact List.mem_cons.2 (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (hl a List.mem_cons_self)).1 h))
    · exact List.mem_cons_of_mem _
        (mem_of_prime_dvd_prod hq (fun p hp => hl p (List.mem_cons_of_mem _ hp)) h)

theorem exists_conj_mem_list_of_le {p : ℕ} [Fact p.Prime] {H : Subgroup (Equiv.Perm (Fin n))}
    {V : List (Equiv.Perm (Fin n))} (hVH : ∀ x ∈ V, x ∈ H) (h1 : (1 : Equiv.Perm (Fin n)) ∈ V)
    (hmul : ∀ x ∈ V, ∀ y ∈ V, x * y ∈ V) (hV : V.Nodup)
    (hcard : V.length = p ^ (Nat.card H).factorization p) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ H) {k : ℕ} (hgk : orderOf g = p ^ k) : ∃ c ∈ H, c * g * c⁻¹ ∈ V := by
  have hle : listSubgroup V h1 hmul ≤ H := fun x hx => hVH x hx
  have hP : Nat.card ((listSubgroup V h1 hmul).subgroupOf H) =
      p ^ (Nat.card H).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_listSubgroup h1 hmul hV,
      hcard]
  obtain ⟨c, hc⟩ := exists_conj_mem_of_card ((listSubgroup V h1 hmul).subgroupOf H) hP
    (g := ⟨g, hg⟩) (k := k) (by rw [Subgroup.orderOf_mk]; exact hgk)
  rw [Subgroup.mem_subgroupOf, mem_listSubgroup] at hc
  exact ⟨c, c.2, by simpa using hc⟩

theorem syl_facts {S : List (Equiv.Perm (Fin n))} {L Li : List (List ℕ)}
    (hL : ∀ j, Img n (S.getD j 1) (L.getD j (List.range n)))
    (hLi : ∀ j, Img n (S.getD j 1)⁻¹ (Li.getD j (List.range n)))
    {H : Subgroup (Equiv.Perm (Fin n))} (hSH : ∀ w, evalCodes S w ∈ H)
    {reps : List (List ℤ)} {p card : ℕ} {W : List (List ℤ × List ℤ × ℕ)}
    (h : sylOK n L Li reps p card W = true) :
    (∀ x ∈ sylElts S W, x ∈ H) ∧ (1 : Equiv.Perm (Fin n)) ∈ sylElts S W ∧
      (∀ x ∈ sylElts S W, ∀ y ∈ sylElts S W, x * y ∈ sylElts S W) ∧ (sylElts S W).Nodup ∧
      (sylElts S W).length = card ∧ (∀ x ∈ sylElts S W, x ^ p = 1) ∧
      ∀ x ∈ sylElts S W, x = 1 ∨ ∃ r ∈ reps.map (evalCodes S), ∃ d ∈ H, x = d * r * d⁻¹ := by
  obtain ⟨h1, hmul, hnd, hlen, hexp, hw⟩ := sylOK_sound hL hLi h
  refine ⟨fun x hx => ?_, h1, hmul, hnd, hlen, hexp, fun x hx => ?_⟩
  · rcases mem_sylElts.1 hx with rfl | ⟨t, -, rfl⟩
    · exact H.one_mem
    · exact hSH _
  · rcases mem_sylElts.1 hx with rfl | ⟨t, ht, rfl⟩
    · exact Or.inl rfl
    · obtain ⟨r, hr, e⟩ := hw t ht
      refine Or.inr ⟨r, hr, evalCodes S t.2.1, hSH _, ?_⟩
      calc evalCodes S t.1 = evalCodes S t.1 * evalCodes S t.2.1 * (evalCodes S t.2.1)⁻¹ := by
            group
        _ = evalCodes S t.2.1 * r * (evalCodes S t.2.1)⁻¹ := by rw [e]

theorem odd_classes {H : Subgroup (Equiv.Perm (Fin n))} {reps : List (Equiv.Perm (Fin n))}
    {P : List ℕ} (hPp : ∀ p ∈ P, p.Prime)
    (hodd : ∀ q, q.Prime → q ∣ Nat.card H → q ≠ 2 → q ∈ P) (V : ℕ → List (Equiv.Perm (Fin n)))
    (hVH : ∀ p ∈ P, ∀ x ∈ V p, x ∈ H) (h1 : ∀ p ∈ P, (1 : Equiv.Perm (Fin n)) ∈ V p)
    (hmul : ∀ p ∈ P, ∀ x ∈ V p, ∀ y ∈ V p, x * y ∈ V p) (hnd : ∀ p ∈ P, (V p).Nodup)
    (hcard : ∀ p ∈ P, (V p).length = p ^ (Nat.card H).factorization p)
    (hexp : ∀ p ∈ P, ∀ x ∈ V p, x ^ p = 1)
    (hconj : ∀ p ∈ P, ∀ x ∈ V p, x = 1 ∨ ∃ r ∈ reps, ∃ d ∈ H, x = d * r * d⁻¹)
    (F : ℕ → List ℕ) (hF : ∀ r ∈ reps, fixCard r ∈ F (orderOf r))
    (hex : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → pqExcl p q (F p) (F q) = true) :
    ∀ g ∈ H, Odd (orderOf g) → g = 1 ∨ ∃ r ∈ reps, ∃ c ∈ H, g = c * r * c⁻¹ := by
  have hin : ∀ p ∈ P, ∀ g ∈ H, ∀ k, orderOf g = p ^ k → ∃ c ∈ H, c * g * c⁻¹ ∈ V p := by
    intro p hp g hg k hk
    have : Fact p.Prime := ⟨hPp p hp⟩
    exact exists_conj_mem_list_of_le (hVH p hp) (h1 p hp) (hmul p hp) (hnd p hp) (hcard p hp) hg hk
  have hrep : ∀ p ∈ P, ∀ g ∈ H, orderOf g = p → ∃ r ∈ reps, ∃ c ∈ H, g = c * r * c⁻¹ := by
    intro p hp g hg ho
    obtain ⟨c, hc, hx⟩ := hin p hp g hg 1 (by rw [ho, pow_one])
    rcases hconj p hp _ hx with h | ⟨r, hr, d, hd, e⟩
    · exfalso
      have hg1 : g = 1 := by
        calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
          _ = 1 := by rw [h]; group
      rw [hg1, orderOf_one] at ho
      exact (hPp p hp).one_lt.ne ho
    · refine ⟨r, hr, c⁻¹ * d, H.mul_mem (H.inv_mem hc) hd, ?_⟩
      calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
        _ = c⁻¹ * d * r * (c⁻¹ * d)⁻¹ := by rw [e]; group
  have hfix : ∀ p ∈ P, ∀ x ∈ H, orderOf x = p → fixCard x ∈ F p := by
    intro p hp x hx ho
    obtain ⟨r, hr, c, -, rfl⟩ := hrep p hp x hx ho
    have e : orderOf (c * r * c⁻¹) = orderOf r := (MulAut.conj c).orderOf_eq r
    rw [fixCard_conj, ← ho, e]
    exact hF r hr
  have hpq : ∀ x ∈ H, ∀ p q, p.Prime → q.Prime → p ∈ P → q ∈ P → orderOf x ≠ p * q := by
    intro x hx p q hp hq hpP hqP ho
    by_cases e : p = q
    · subst e
      obtain ⟨c, -, hcx⟩ := hin p hpP x hx 2 (by rw [ho, sq])
      have e0 : orderOf (c * x * c⁻¹) = orderOf x := (MulAut.conj c).orderOf_eq x
      have h2 : orderOf x ∣ p := by
        rw [← e0]
        exact orderOf_dvd_of_pow_eq_one (hexp p hpP _ hcx)
      rw [ho] at h2
      have := Nat.le_of_dvd hp.pos h2
      have := hp.two_le
      nlinarith
    · exact orderOf_ne_of_pqExcl hp hq e (hfix p hpP) (hfix q hqP) (hex p hpP q hqP e) hx ho
  intro g hg hg2
  have hgd : orderOf g ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hg
  have hS : ∀ p, p.Prime → p ∣ orderOf g → p ∈ P := by
    intro p hp hpd
    refine hodd p hp (hpd.trans hgd) ?_
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hg2) (even_iff_two_dvd.2 hpd)
  rcases orderOf_eq_one_or_prime (S := fun p => p ∈ P) hg hS
    (fun x hx p q hp hq hpP hqP => hpq x hx p q hp hq hpP hqP) with h | h
  · exact Or.inl (orderOf_eq_one_iff.1 h)
  · exact Or.inr (hrep _ (hS _ h dvd_rfl) g hg rfl)

end CFSG.KS.OddSyl

end
