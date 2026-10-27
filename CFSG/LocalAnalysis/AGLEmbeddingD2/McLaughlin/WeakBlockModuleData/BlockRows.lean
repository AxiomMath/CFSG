module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensusPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CentreTransfer

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def L5Atlas : Prop :=
  ∀ (X : Type) [Group X], IsL5Two X →
    Nat.card X = 9999360 ∧ ∀ H : Subgroup X, ¬ 3 ∣ Nat.card H → Nat.card H ≤ 1024

theorem IsUThreeThree.of_center_bot {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (h : IsUThreeThree (X ⧸ Subgroup.center X)) : IsUThreeThree X := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := mulEquiv_of_center_eq_bot hZ e
  exact ⟨d, hd, ⟨e'⟩⟩

theorem center_eq_bot_of_card {X : Type} [Group X] [Finite X] (hX : Open.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X))) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center X))
    (hN : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 2 ∣ Nat.card (X ⧸ Subgroup.center X)) :
    Subgroup.center X = ⊥ := by
  by_contra hne
  have hgt : Nat.card (Subgroup.center X) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgt
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3 hpd
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p <;> first | exact absurd hp (by decide) | exact absurd rfl hp2 | exact absurd rfl hp3
    · exact h
  have : Fact p.Prime := ⟨hp⟩
  exact not_dvd_card_center_of_perfect hX.1 (hN p hp hp5) hpd

private theorem not_sq_dvd_of_five_le (p n : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : ∀ q : ℕ, q.Prime → q ∣ n → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 31)
    (hsq : ∀ q ∈ ({5, 7, 31} : Finset ℕ), ¬ q ^ 2 ∣ n) : ¬ p ^ 2 ∣ n := by
  intro h
  have hpn : p ∣ n := (dvd_pow_self p (by norm_num)).trans h
  rcases hn p hp hpn with h2 | h3 | h5 | h7 | h31
  · omega
  · omega
  · exact hsq 5 (by simp) (h5 ▸ h)
  · exact hsq 7 (by simp) (h7 ▸ h)
  · exact hsq 31 (by simp) (h31 ▸ h)

private theorem primes_dvd_of_card (n : ℕ) (hn : n = 360 ∨ n = 2520 ∨ n = 20160 ∨ n = 6048 ∨
    n = 9999360) (q : ℕ) (hq : q.Prime) (hqn : q ∣ n) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 31 := by
  have key : ∀ m : ℕ, (∀ r ∈ ({2, 3, 5, 7, 31} : Finset ℕ), True) → q ∣ m →
      m = 2 ^ 10 * 3 ^ 3 * 5 * 7 * 31 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 31 := by
    intro m _ hqm hm
    subst hm
    have hdvd : ∀ r : ℕ, r.Prime → q ∣ r → q = r := fun r hr h =>
      (Nat.prime_dvd_prime_iff_eq hq hr).mp h
    simp only [Nat.Prime.dvd_mul hq] at hqm
    rcases hqm with (((h | h) | h) | h) | h
    · left; exact hdvd 2 Nat.prime_two (hq.dvd_of_dvd_pow h)
    · right; left; exact hdvd 3 Nat.prime_three (hq.dvd_of_dvd_pow h)
    · right; right; left; exact hdvd 5 (by norm_num) h
    · right; right; right; left; exact hdvd 7 (by norm_num) h
    · right; right; right; right; exact hdvd 31 (by norm_num) h
  refine key (2 ^ 10 * 3 ^ 3 * 5 * 7 * 31) (fun _ _ => trivial) ?_ rfl
  have hdvdN : n ∣ 2 ^ 10 * 3 ^ 3 * 5 * 7 * 31 := by
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> norm_num
  exact hqn.trans hdvdN

private theorem not_sq_dvd_row (n : ℕ) (hn : n = 360 ∨ n = 2520 ∨ n = 20160 ∨ n = 6048 ∨
    n = 9999360) (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ^ 2 ∣ n := by
  refine not_sq_dvd_of_five_le p n hp hp5 (fun q hq h => primes_dvd_of_card n hn q hq h) ?_
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> norm_num

theorem tightCentreTrivial_of_atlas (hU : U33Atlas) : TightCentreTrivial := by
  intro X _ _ hX hKP hodd h3
  refine center_eq_bot_of_card hX hodd h3 fun p hp hp5 => ?_
  rcases hKP with ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl <;>
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      refine not_sq_dvd_row _ ?_ p hp hp5
      simp [Nat.factorial]
  · obtain ⟨hcard, -⟩ := hU _ ⟨d, hd, ⟨e⟩⟩
    rw [hcard]
    exact not_sq_dvd_row _ (by norm_num) p hp hp5

end CFSG.AGLEmbeddingD2.McLaughlin
