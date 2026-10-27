module

public import CFSG.GF2Type.Smith1979.CaseI25Filter

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open CFSG.EvenSmallLie.CatalogOrders CFSG.EvenSmallLie.Child3 CFSG.Assembly.LowTwoRank
open CFSG.GF2Type.Smith1979.Case25 (orthPlus12Ord orthPlus12Primes primes_orthPlus12Ord)

@[expose] def lieTuplesII : List (StatedLieTag × ℕ × ℕ × ℕ) :=
  [(.PSL, 3, 2, 2), (.PSL, 4, 2, 1), (.PSL, 5, 2, 1), (.PSp, 3, 2, 1), (.POmegaOdd, 3, 2, 1),
    (.PSU, 4, 3, 1), (.G2, 0, 2, 1)]

@[expose] def filterCheckII (t : StatedLieTag) (n p f o : ℕ) : Bool :=
  decide (1344 ∣ o → ¬ 2 ^ 11 ∣ o → (t, n, p, f) ∈ lieTuplesII)

theorem lieSearch_orthPlus12_II :
    lieSearchV orthPlus12Primes orthPlus12Ord filterCheckII = true := by
  decide +kernel

theorem filterII_lieTuple {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ searchTags) (hp : p.Prime)
    (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hn0 : lieMin t = 0 → n = 0) (hnB : n ≤ lieExp t n + 1)
    (hadm : lieAdm t p f = true) (hord : lieOrd t n (p ^ f) ∣ orthPlus12Ord)
    (h1 : 1344 ∣ lieOrd t n (p ^ f)) (h2 : ¬ 2 ^ 11 ∣ lieOrd t n (p ^ f)) :
    (t, n, p, f) ∈ lieTuplesII := by
  have hC := lieSearchV_sound primes_orthPlus12Ord lieSearch_orthPlus12_II ht hp hf hn hn0 hnB
    hadm hord
  simp only [filterCheckII, decide_eq_true_eq] at hC
  exact hC h1 h2

theorem filterII_alt {n : ℕ} (hn : 5 ≤ n) (hord : n.factorial / 2 ∣ orthPlus12Ord)
    (h1 : 1344 ∣ n.factorial / 2) (h2 : ¬ 2 ^ 11 ∣ n.factorial / 2) : 8 ≤ n ∧ n ≤ 12 := by
  have h13 : ¬ 13 ∣ orthPlus12Ord := by decide +kernel
  have hle : n ≤ 12 := le_twelve_of_factorial_div_two_dvd (by omega) h13 hord
  refine ⟨?_, hle⟩
  by_contra hlt
  interval_cases n
  all_goals (revert h1; decide +kernel)

theorem filterII_sporadic : ∀ s : TauCeti.SporadicName, s ≠ .Th → s ≠ .M →
    sporadicCard s ∣ orthPlus12Ord → 1344 ∣ sporadicCard s → ¬ 2 ^ 11 ∣ sporadicCard s →
      s = .J2 ∨ s = .M22 := by
  decide +kernel

theorem filterII_not_dvd_titsOrd : ¬ 1344 ∣ 35942400 := by decide +kernel

end CFSG.GF2Type.Smith1979.Case2
