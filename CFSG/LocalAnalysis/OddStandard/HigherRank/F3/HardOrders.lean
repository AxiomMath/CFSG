module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG
open CFSG.Open
open CFSG.ComponentClassification.CatLeaf

private lemma not_lieModel_of_orders
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (Q : Type) [Group Q] [Finite Q] (n k s : ℕ) (hn : n = 4 ∨ n = 6)
    (hΩ : Blueprint.LieModel Q .POmegaPlus n 3 1) (t : StatedLieTag)
    (ht : t = .PSL ∨ t = .PSU) (hL : Blueprint.LieModel Q t k 3 s) : False := by
  obtain ⟨-, hΩnum, hΩfac⟩ :=
    hO Q .POmegaPlus n 3 1 (Blueprint.LieModel.admissible hΩ) hΩ
  obtain ⟨-, hLnum, hLfac⟩ :=
    hO Q t k 3 s (Blueprint.LieModel.admissible hL) hL
  have hSylow : lieSylowExponent t k = k * (k - 1) / 2 := by
    rcases ht with rfl | rfl <;> rfl
  have hfacΩ : (Nat.card Q).factorization 3 = n * (n - 1) := by
    rw [hΩfac]
    simp [lieSylowExponent]
  have hfacL : (Nat.card Q).factorization 3 = k * (k - 1) / 2 * s := by
    rw [hLfac, hSylow]
  have hfac : k * (k - 1) / 2 * s = n * (n - 1) := by omega
  have hpos : 0 < n * (n - 1) := by rcases hn with rfl | rfl <;> norm_num
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      simp only [Nat.mul_zero] at hfac
      omega
    · exact h
  have h30 : n * (n - 1) ≤ 30 := by rcases hn with rfl | rfl <;> norm_num
  have hm : k * (k - 1) / 2 ≤ 30 := by
    calc k * (k - 1) / 2 = k * (k - 1) / 2 * 1 := (Nat.mul_one _).symm
      _ ≤ k * (k - 1) / 2 * s := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hs)
      _ = n * (n - 1) := hfac
      _ ≤ 30 := h30
  have hb : k * (k - 1) ≤ 61 := (Nat.div_le_iff_le_mul (by norm_num : 0 < 2)).mp hm
  have hk : k ≤ 8 := by
    by_contra h
    push Not at h
    have hk9 : 9 ≤ k := h
    have hk8 : 8 ≤ k - 1 := by omega
    have h72 : 72 ≤ k * (k - 1) := by simpa using Nat.mul_le_mul hk9 hk8
    omega
  have h4 : lieOrderDivisor .POmegaPlus n 3 = 4 := by rcases hn with rfl | rfl <;> decide
  have hΩ' : Nat.card Q * 4 = lieOrderNumerator .POmegaPlus n 3 := by
    rw [← h4]
    exact hΩnum
  have hkey : lieOrderNumerator .POmegaPlus n 3 * lieOrderDivisor t k (3 ^ s)
      = lieOrderNumerator t k (3 ^ s) * 4 := by
    calc lieOrderNumerator .POmegaPlus n 3 * lieOrderDivisor t k (3 ^ s)
        = (Nat.card Q * 4) * lieOrderDivisor t k (3 ^ s) := by rw [hΩ']
      _ = (Nat.card Q * lieOrderDivisor t k (3 ^ s)) * 4 := by ring
      _ = lieOrderNumerator t k (3 ^ s) * 4 := by rw [hLnum]
  rcases hn with rfl | rfl
  all_goals
    interval_cases k
    all_goals
      have hs30 : s ≤ 30 := by omega
      interval_cases s <;> try omega
    all_goals
      rcases ht with rfl | rfl <;> exact absurd hkey (by decide)

theorem pOmegaPlusNotLinUnit_of_orders
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) : POmegaPlusNotLinUnit := by
  unfold POmegaPlusNotLinUnit
  intro Q _ _ n k s hn hΩ
  constructor
  · intro hL
    exact not_lieModel_of_orders hO Q n k s hn hΩ .PSL (Or.inl rfl) hL
  · intro hL
    exact not_lieModel_of_orders hO Q n k s hn hΩ .PSU (Or.inr rfl) hL

end CFSG.OddStandard.HigherRank.F3
