module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafExcOrd

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

@[expose] def ordL4U4 (q : ℕ) : ℕ :=
  if q % 4 = 3 then q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)
  else q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)

theorem two_mul_card_eq_ordL4U4 {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hX : (p ^ f % 4 = 3 ∧ LieModel X .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel X .PSU 4 p f)) :
    Nat.card X * 2 = ordL4U4 (p ^ f) := by
  rcases hX with ⟨h3, hX⟩ | ⟨h1, hX⟩
  · have h := card_psl4 hp2 hX
    rw [(gcd_four_of_mod_three h3).1] at h
    rw [h, ordL4U4, if_pos h3]
  · have h := card_psu4 hp2 hX
    rw [(gcd_four_of_mod_one h1).2] at h
    rw [h, ordL4U4, if_neg (by omega)]

theorem leaf_card_dvd {S : Type} [Group S] [Finite S] {P : Subgroup S} {p f : ℕ}
    (hp2 : p ≠ 2)
    (hX : (p ^ f % 4 = 3 ∧ LieModel (P ⧸ pPrimeCore 2 P) .PSL 4 p f) ∨
      (p ^ f % 4 = 1 ∧ LieModel (P ⧸ pPrimeCore 2 P) .PSU 4 p f)) :
    ordL4U4 (p ^ f) ∣ 2 * Nat.card S ∧ p ^ (6 * f) ∣ Nat.card S := by
  have hXS : Nat.card (P ⧸ pPrimeCore 2 P) ∣ Nat.card S :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card P)
  refine ⟨?_, ?_⟩
  · rw [← two_mul_card_eq_ordL4U4 hp2 hX, mul_comm 2]
    exact Nat.mul_dvd_mul_right hXS 2
  · have hfac := (two_mul_card_l4u4 hp2 hX).2
    have h1 : p ^ (6 * f) ∣ Nat.card (P ⧸ pPrimeCore 2 P) := by
      rw [← hfac]
      exact Nat.ordProj_dvd _ _
    exact h1.trans hXS

theorem exists_eq_of_prime_dvd_prod {p : ℕ} (hp : p.Prime) :
    ∀ L : List (ℕ × ℕ), (∀ x ∈ L, x.1.Prime) → p ∣ (L.map fun x => x.1 ^ x.2).prod →
      ∃ x ∈ L, p = x.1
  | [], _, h => by
    rw [List.map_nil, List.prod_nil] at h
    exact absurd (Nat.dvd_one.mp h) hp.one_lt.ne'
  | x :: L, hL, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact ⟨x, List.mem_cons_self .., (Nat.prime_dvd_prime_iff_eq hp
        (hL x List.mem_cons_self)).mp (hp.dvd_of_dvd_pow h1)⟩
    · obtain ⟨y, hy, rfl⟩ := exists_eq_of_prime_dvd_prod hp L
        (fun y hy => hL y (List.mem_cons_of_mem _ hy)) h1
      exact ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

@[expose] def FilterOK (N : ℕ) (Qs : Finset ℕ) (x : ℕ × ℕ) : Prop :=
  x.1 = 2 ∨ (¬ x.1 ^ (x.2 + 1) ∣ N ∧
    ∀ f ∈ Finset.Icc 1 (x.2 / 6), ¬ ordL4U4 (x.1 ^ f) ∣ 2 * N ∨ x.1 ^ f ∈ Qs)

instance (N : ℕ) (Qs : Finset ℕ) (x : ℕ × ℕ) : Decidable (FilterOK N Qs x) := by
  unfold FilterOK
  infer_instance

theorem pow_mem_of_filter {S : Type} [Group S] [Finite S] {N : ℕ} (hN : Nat.card S = N)
    (L : List (ℕ × ℕ)) (hL : ∀ x ∈ L, x.1.Prime) (hNL : (L.map fun x => x.1 ^ x.2).prod = N)
    {Qs : Finset ℕ} (hF : ∀ x ∈ L, FilterOK N Qs x) {P : Subgroup S} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hX : (p ^ f % 4 = 3 ∧ LieModel (P ⧸ pPrimeCore 2 P) .PSL 4 p f) ∨
      (p ^ f % 4 = 1 ∧ LieModel (P ⧸ pPrimeCore 2 P) .PSU 4 p f)) : p ^ f ∈ Qs := by
  obtain ⟨hord, hpow⟩ := leaf_card_dvd hp2 hX
  rw [hN] at hord hpow
  have hpN : p ∣ N := (dvd_pow_self p (by omega)).trans hpow
  rw [← hNL] at hpN
  obtain ⟨x, hx, rfl⟩ := exists_eq_of_prime_dvd_prod hp L hL hpN
  rcases hF x hx with h2 | ⟨hlt, hall⟩
  · exact absurd h2 hp2
  · have h6 : 6 * f ≤ x.2 := by
      by_contra hc
      exact hlt ((pow_dvd_pow x.1 (by omega)).trans hpow)
    rcases hall f (Finset.mem_Icc.mpr ⟨hf, by omega⟩) with h | h
    · exact absurd hord h
    · exact h

end CFSG.ComponentClassification.GSThmB.Pump516
