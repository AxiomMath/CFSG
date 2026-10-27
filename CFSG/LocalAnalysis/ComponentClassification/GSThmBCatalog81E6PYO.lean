module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PYT
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.Ly
public import CFSG.Sporadic.Schreier.M12

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211Y

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer P211 P211X

theorem p211For_J1 :
    P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .J1 := by
  intro X _ _ hsimp hC ⟨e⟩ p f hp hp2 hf a J D _ _ _ _ hJt hJF hDJ hDsyl hbound b K hb hb1
    hKC hK hKt
  exfalso
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  have hcard : Nat.card (generalizedFitting X) = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
  have h1 := ordA_dvd_card_fstar hJt hJF
  rw [hcard, show p ^ (2 * f) = (p ^ f) ^ 2 by ring] at h1
  have h2 : (p ^ f) ^ 2 ∣ 21945 := by
    refine sq_dvd_of_sq_dvd_two_pow_mul hq (a := 3) ?_
    exact (sq_dvd_ordA' hq).trans (by norm_num [h1])
  have h4 : p ^ f < 149 := by
    by_contra hc
    have hc' : 149 ≤ p ^ f := not_lt.mp hc
    have h5 : 149 * 149 ≤ p ^ f * p ^ f := Nat.mul_le_mul hc' hc'
    have h6 := Nat.le_of_dvd (by norm_num) h2
    rw [pow_two] at h6
    omega
  have key : ∀ r < 149, r ^ 2 ∣ 21945 → r ≤ 1 := by decide
  have := key _ h4 h2
  omega

theorem prime_dvd_card_Ly {p : ℕ} (hp : p.Prime) (h : p ∣ 51765179004000000) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 31 ∨ p = 37 ∨ p = 67 := by
  rw [show (51765179004000000 : ℕ) = 2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67 by
    norm_num] at h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · rcases hp.dvd_mul.1 h with h | h
      · rcases hp.dvd_mul.1 h with h | h
        · rcases hp.dvd_mul.1 h with h | h
          · rcases hp.dvd_mul.1 h with h | h
            · rcases hp.dvd_mul.1 h with h | h
              · exact Or.inl (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h))
              · exact Or.inr (Or.inl (hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h)))
            · exact Or.inr (Or.inr (Or.inl (hq 5 Nat.prime_five (hp.dvd_of_dvd_pow h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 11 (by norm_num) h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 31 (by norm_num) h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 37 (by norm_num) h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hq 67 (by norm_num) h)))))))

theorem p211For_Ly :
    P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .Ly := by
  intro X _ _ hsimp hC ⟨e⟩ p f hp hp2 hf a J D _ _ _ _ hJt hJF hDJ hDsyl hbound b K hb hb1
    hKC hK hKt
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (generalizedFitting X) = 51765179004000000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ly.card_Ly
  obtain ⟨-, -, hFv⟩ := p211_two_adic hp hp2 hf hJt hDJ hDsyl hbound hKt
  have h8 : 8 ≤ padicValNat 2 (Nat.card (generalizedFitting X)) := by
    rw [hcard]
    exact (padicValNat_dvd_iff_le (by norm_num)).1 (by norm_num)
  have h16 : 2 ^ 4 ∣ (p ^ f) ^ 2 - 1 :=
    (pow_dvd_pow 2 (by omega : 4 ≤ padicValNat 2 ((p ^ f) ^ 2 - 1))).trans pow_padicValNat_dvd
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h1 := ordA_dvd_card_fstar hJt hJF
  rw [hcard] at h1
  have hsq : (p ^ f) ^ 2 ∣ 51765179004000000 := by
    rw [show p ^ (2 * f) = (p ^ f) ^ 2 by ring] at h1
    exact (sq_dvd_ordA' hq).trans h1
  have hpsq : p ^ 2 ∣ 51765179004000000 :=
    (pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 2).trans hsq
  have hbound3 : (p ^ 8 ∣ 51765179004000000 → False) → f ≤ 3 := by
    intro hn
    by_contra hc
    refine hn ((?_ : p ^ 8 ∣ (p ^ f) ^ 2).trans hsq)
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)
  rcases prime_dvd_card_Ly hp ((dvd_pow_self p two_ne_zero).trans hpsq) with
    h | h | h | h | h | h | h | h
  · exact hp2 h
  · subst h
    have hf3 := hbound3 (fun h => absurd h (by decide))
    interval_cases f
    · exact absurd h16 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h16 (by decide)
  · subst h
    have hf3 := hbound3 (fun h => absurd h (by decide))
    interval_cases f
    · exact absurd h16 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h16 (by decide)
  all_goals (subst h; exact absurd hpsq (by decide))

theorem p211For_M12 :
    P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .M12 := by
  intro X _ _ hsimp hC ⟨e⟩ p f hp hp2 hf a J D _ _ _ _ hJt hJF hDJ hDsyl hbound b K hb hb1
    hKC hK hKt
  exfalso
  have hKF := le_fstar_of_solvable hC
    (outer_solvable_of_equiv e Sporadic.Schreier.at_m12_schreier.2.2) hKC hK
  have hcard : Nat.card (generalizedFitting X) = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12
  have hdvd : Nat.card (K ⧸ pPrimeCore 2 K) ∣ 95040 :=
    hcard ▸ (card_quotient_dvd_card _).trans (card_dvd_of_le hKF)
  rcases card_socle_cases hp2 hKt with h | h
  · have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hq3 : 3 ≤ p ^ f :=
      le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
    have h4 : (p ^ f) ^ 4 ∣ 190080 := by
      rw [h] at hdvd
      have h2 : Open.ordBC 2 (p ^ f) * 2 ∣ 95040 * 2 := Nat.mul_dvd_mul_right hdvd 2
      rw [ordBC_two_mul hq] at h2
      exact (dvd_mul_right _ _).trans h2
    have hlt : p ^ f < 21 := by
      by_contra hc
      have hc' : 21 ≤ p ^ f := not_lt.mp hc
      have h5 : 21 ^ 4 ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hc' 4
      have h6 := Nat.le_of_dvd (by norm_num) h4
      omega
    have key : ∀ r < 21, r ^ 4 ∣ 190080 → r % 2 = 1 → r ≤ 1 := by decide
    have := key _ hlt h4 (Nat.odd_iff.mp hq)
    omega
  · rw [h] at hdvd
    exact absurd hdvd (by decide)

end P211Y

end CFSG.ComponentClassification.GSThmB
