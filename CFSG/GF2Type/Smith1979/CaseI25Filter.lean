module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case25

open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3 CFSG.Assembly.LowTwoRank

@[expose] def orthPlus12Ord : ℕ := 2 ^ 31 * 3 ^ 8 * 5 ^ 2 * 7 ^ 2 * 11 * 17 * 31

@[expose] def orthPlus12Primes : List (ℕ × ℕ) :=
  [(2, 31), (3, 8), (5, 2), (7, 2), (11, 1), (17, 1), (31, 1)]

@[expose] def filterCheckX (t : StatedLieTag) (n p f o : ℕ) : Bool :=
  decide (25920 ∣ o → 2 ^ 7 ∣ o → ¬ 2 ^ 9 ∣ o → t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1)

theorem eq_orthPlus12Ord_of_formula {N q : ℕ} (hq : q = 2)
    (h : (N : ℤ) = 2 * (q : ℤ) ^ (5 * (5 + 1)) * ((q : ℤ) ^ (5 + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 5, (((q : ℤ) ^ 2) ^ i - 1)) : N = orthPlus12Ord := by
  subst hq
  have h' : (N : ℤ) = (orthPlus12Ord : ℤ) := by
    rw [h]
    decide +kernel
  exact_mod_cast h'

theorem primes_orthPlus12Ord : ∀ p : ℕ, p.Prime → p ∣ orthPlus12Ord →
    ∃ e, (p, e) ∈ orthPlus12Primes ∧ ¬ p ^ (e + 1) ∣ orthPlus12Ord := by
  refine primes_of_factorization ?_ (by decide +kernel) (by decide +kernel)
  simp only [orthPlus12Primes, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  norm_num

theorem lieSearch_orthPlus12 :
    lieSearchV orthPlus12Primes orthPlus12Ord filterCheckX = true := by
  decide +kernel

theorem filterX_lieTuple {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags) (hp : p.Prime)
    (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1)
    (hadm : lieAdm t p f = true) (hord : lieOrd t n (p ^ f) ∣ orthPlus12Ord)
    (h1 : 25920 ∣ lieOrd t n (p ^ f)) (h2 : 2 ^ 7 ∣ lieOrd t n (p ^ f))
    (h3 : ¬ 2 ^ 9 ∣ lieOrd t n (p ^ f)) : t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1 := by
  have hC := lieSearchV_sound primes_orthPlus12Ord lieSearch_orthPlus12 ht hp hf hn hn0 hnB hadm
    hord
  simp only [filterCheckX, decide_eq_true_eq] at hC
  exact hC h1 h2 h3

theorem filterX_alt {n : ℕ} (hn : 5 ≤ n) (hord : n.factorial / 2 ∣ orthPlus12Ord)
    (h1 : 25920 ∣ n.factorial / 2) (h2 : 2 ^ 7 ∣ n.factorial / 2)
    (h3 : ¬ 2 ^ 9 ∣ n.factorial / 2) : n = 10 ∨ n = 11 := by
  have h13 : ¬ 13 ∣ orthPlus12Ord := by decide +kernel
  have hle : n ≤ 12 := le_twelve_of_factorial_div_two_dvd (by omega) h13 hord
  interval_cases n
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (exfalso; revert hord h1 h2 h3; decide +kernel)

theorem filterX_false_of_sporadic : ∀ s : TauCeti.SporadicName, s ≠ .Th → s ≠ .M →
    sporadicCard s ∣ orthPlus12Ord → 25920 ∣ sporadicCard s → 2 ^ 7 ∣ sporadicCard s →
      ¬ 2 ^ 9 ∣ sporadicCard s → False := by
  decide +kernel

theorem filterX_not_two_pow_sixtySeven_dvd : ¬ 2 ^ 67 ∣ orthPlus12Ord := by decide +kernel

theorem filterX_not_thirtySeven_dvd : ¬ 37 ∣ orthPlus12Ord := by decide +kernel

theorem filterX_not_fortyOne_dvd : ¬ 41 ∣ orthPlus12Ord := by decide +kernel

theorem filterX_not_nineteen_dvd : ¬ 19 ∣ orthPlus12Ord := by decide +kernel

theorem filterX_not_twentyNine_dvd : ¬ 29 ∣ orthPlus12Ord := by decide +kernel

theorem filterX_not_dvd_titsOrd : ¬ 25920 ∣ 35942400 := by decide +kernel

end CFSG.GF2Type.Smith1979.Case25
