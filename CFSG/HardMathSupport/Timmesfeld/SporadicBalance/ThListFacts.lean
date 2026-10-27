module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveData

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThList

open CFSG.Sporadic.Th CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative

theorem lt_of_all {A : Array (List ℕ)} {n m : ℕ}
    (h : (A.toList.all fun l => l.all fun j => decide (j < m)) = true) (hs : A.size = n) :
    ∀ i < n, ∀ j ∈ A[i]!, j < m := by
  intro i hi j hj
  have hl : i < A.toList.length := by simpa [hs] using hi
  have h1 := List.all_eq_true.1 h _ (List.getElem_mem hl)
  simp only [Array.getElem_toList] at h1
  rw [getElem!_pos A i (by simpa using hl)] at hj
  simpa using List.all_eq_true.1 h1 j hj

theorem words7_size : list7.words.size = 1176 := by decide +kernel

theorem words7_lt : ∀ i < 1176, ∀ r ∈ list7.words[i]!, r < 43 :=
  lt_of_all (by decide +kernel) words7_size

theorem wit7_lt : ∀ i < 1176, ∀ j ∈ list7.wit[i]!, j < 1176 :=
  lt_of_all (by decide +kernel) (by decide +kernel)

theorem words5_size : list5.words.size = 3000 := by decide +kernel

theorem words5_lt : ∀ i < 3000, ∀ r ∈ list5.words[i]!, r < 118 :=
  lt_of_all (by decide +kernel) words5_size

theorem wit5_lt : ∀ i < 3000, ∀ j ∈ list5.wit[i]!, j < 3000 :=
  lt_of_all (by decide +kernel) (by decide +kernel)


@[expose] noncomputable def el7 (i : ℕ) : J := ((list7.words[i]!).map (slpJ a b prog7)).prod

@[expose] noncomputable def el5 (i : ℕ) : J := ((list5.words[i]!).map (slpJ a b prog5)).prod

@[expose] noncomputable def z7 : J := slpJ a b prog7 24 * slpJ a b prog7 25 ^ 6

@[expose] noncomputable def c5 : J :=
  slpJ a b prog5 94 * slpJ a b prog5 105 * slpJ a b prog5 94 ^ 4 * slpJ a b prog5 105 ^ 4

structure ThSevenFacts : Prop where
  x_pow : slpJ a b prog7 24 ^ 7 = 1
  y_pow : slpJ a b prog7 25 ^ 7 = 1
  comm : slpJ a b prog7 24 * slpJ a b prog7 25 = slpJ a b prog7 25 * slpJ a b prog7 24
  x_ne : slpJ a b prog7 24 ≠ 1
  y_ne : ∀ k < 7, slpJ a b prog7 25 ≠ slpJ a b prog7 24 ^ k
  conj : ∀ i j : ℕ, i < 7 → j < 7 → i + j ≠ 0 →
    ∃ m : J, m * (slpJ a b prog7 24 ^ i * slpJ a b prog7 25 ^ j) = z7 * m
  list_comm : ∀ i < 1176, el7 i * z7 = z7 * el7 i
  list_ne : ∀ i < 1176, ∀ j < i, el7 i ≠ el7 j
  list_wit : ∀ i < 1176, el7 i ≠ 1 →
    (el7 i * ((list7.wit[i]!).map fun j => el7 j * el7 i * (el7 j)⁻¹).prod) ^ 24 ≠ 1

structure ThFiveFacts : Prop where
  x_pow : slpJ a b prog5 94 ^ 5 = 1
  y_pow : slpJ a b prog5 105 ^ 5 = 1
  cx : c5 * slpJ a b prog5 94 = slpJ a b prog5 94 * c5
  cy : c5 * slpJ a b prog5 105 = slpJ a b prog5 105 * c5
  inj : ∀ i j k i' j' k' : ℕ, i < 5 → j < 5 → k < 5 → i' < 5 → j' < 5 → k' < 5 →
    slpJ a b prog5 94 ^ i * slpJ a b prog5 105 ^ j * c5 ^ k =
      slpJ a b prog5 94 ^ i' * slpJ a b prog5 105 ^ j' * c5 ^ k' → i = i' ∧ j = j' ∧ k = k'
  conj : ∀ i j k : ℕ, i < 5 → j < 5 → k < 5 → i + j + k ≠ 0 →
    ∃ m : J, m * (slpJ a b prog5 94 ^ i * slpJ a b prog5 105 ^ j * c5 ^ k) = c5 * m
  list_comm : ∀ i < 3000, el5 i * c5 = c5 * el5 i
  list_ne : ∀ i < 3000, ∀ j < i, el5 i ≠ el5 j
  list_wit : ∀ i < 3000, el5 i ≠ 1 →
    (el5 i * ((list5.wit[i]!).map fun j => el5 j * el5 i * (el5 j)⁻¹).prod) ^ 24 ≠ 1

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThList

end
