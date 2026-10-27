module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
open CFSG.OddStandard.SmallF3.HypA2 (KDatum Chev3DatumEnd InSB classSBound)

theorem a2l_card_lt_of_formula {S : Type} [Group S] {t : Open.StatedLieTag} {n p f : ℕ}
    (hO : LieOrderFormulasInput) (h : LieModel S t n p f)
    (hlt : lieOrderNumerator t n (p ^ f) < classSBound * lieOrderDivisor t n (p ^ f)) :
    Nat.card S < classSBound := by
  obtain ⟨-, h1, -⟩ := hO S t n p f h.admissible h
  by_contra hge
  exact absurd (h1 ▸ Nat.mul_le_mul_right (lieOrderDivisor t n (p ^ f)) (not_lt.1 hge))
    (not_le.2 hlt)

theorem a2l_two_pow_cases (j : ℕ) : 2 ^ j = 1 ∨ 2 ≤ 2 ^ j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact Or.inl rfl
  · exact Or.inr (Nat.one_lt_two_pow hj.ne')

theorem a2l_chev3DatumEnd_of_rows (hGA : TBLit.GriessMultipliersOdd)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) (hO : LieOrderFormulasInput)
    (hR : a2lRows) : Chev3DatumEnd := by
  intro K _ _ hK h2 hS hnL2
  have key : a2lDatum (K ⧸ center K) → KDatum K :=
    fun h => Or.inr (a2l_noncentralDatum_of_quotient hGA hSchur h2 h)
  obtain ⟨-, hbig, ⟨j, τ, n, hm⟩, -, hnP, hnM⟩ := hS
  have hbig' : ¬ Nat.card (K ⧸ center K) < classSBound := not_lt.2 hbig
  obtain ⟨-, hf1, hmatch⟩ := hm.admissible
  generalize hfj : 2 ^ j = f at hm hf1 hmatch hnL2
  have hf : f = 1 ∨ 2 ≤ f := hfj ▸ a2l_two_pow_cases j
  cases τ with
  | PSL =>
    obtain ⟨hn2, -, -⟩ := hmatch
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact absurd ⟨f, hm⟩ hnL2
    · by_cases hc : 2 ≤ f ∨ 5 ≤ n
      · exact key (hR.psl _ n f hn3 hc hm)
      · exfalso
        obtain rfl : f = 1 := by omega
        rcases (show n = 3 ∨ n = 4 by omega) with rfl | rfl
        · exact hbig' (a2l_card_lt_of_formula hO hm (by decide))
        · exact hbig' (a2l_card_lt_of_formula hO hm (by decide))
  | PSU =>
    obtain ⟨hn3, -⟩ := hmatch
    by_cases hc : 2 ≤ f ∨ 5 ≤ n
    · exact key (hR.psu _ n f hn3 hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      rcases (show n = 3 ∨ n = 4 by omega) with rfl | rfl
      · exact hbig' (a2l_card_lt_of_formula hO hm (by decide))
      · exact hbig' (a2l_card_lt_of_formula hO hm (by decide))
  | PSp =>
    obtain ⟨hn2, -⟩ := hmatch
    by_cases hc : 2 ≤ f ∨ 3 ≤ n
    · exact key (hR.psp _ n f hn2 hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      obtain rfl : n = 2 := by omega
      exact hbig' (a2l_card_lt_of_formula hO hm (by decide))
  | POmegaOdd =>
    obtain ⟨hn3, -⟩ := hmatch
    by_cases hc : 2 ≤ f ∨ 4 ≤ n
    · exact key (hR.oOdd _ n f hn3 hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      obtain rfl : n = 3 := by omega
      exact hbig' (a2l_card_lt_of_formula hO hm (by decide))
  | POmegaPlus =>
    by_cases hc : 2 ≤ f ∨ 5 ≤ n
    · exact key (hR.oPlus _ n f hmatch hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      obtain rfl : n = 4 := by omega
      exact hnP hm
  | POmegaMinus =>
    by_cases hc : 2 ≤ f ∨ 5 ≤ n
    · exact key (hR.oMinus _ n f hmatch hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      obtain rfl : n = 4 := by omega
      exact hnM hm
  | G2 =>
    obtain ⟨rfl, -⟩ := hmatch
    by_cases hc : 2 ≤ f
    · exact key (hR.g2 _ f hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      exact hbig' (a2l_card_lt_of_formula hO hm (by decide))
  | F4 => obtain rfl := hmatch; exact key (hR.f4 _ f hm)
  | E6 => obtain rfl := hmatch; exact key (hR.e6 _ f hm)
  | E7 => obtain rfl := hmatch; exact key (hR.e7 _ f hm)
  | E8 => obtain rfl := hmatch; exact key (hR.e8 _ f hm)
  | twistedE6 => obtain rfl := hmatch; exact key (hR.twistedE6 _ f hm)
  | trialityD4 => obtain rfl := hmatch; exact key (hR.trialityD4 _ f hm)
  | twistedB2 => exact absurd hmatch.2.1 (by norm_num)
  | twistedF4 => exact absurd hmatch.2.1 (by norm_num)
  | twistedG2 =>
    exfalso
    obtain ⟨-, -, hodd, h3⟩ := hmatch
    rcases hf with rfl | h2f
    · omega
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp at hfj; omega
      · rw [← hfj] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (Even.pow_of_ne_zero even_two hj.ne')
  | Tits => exact absurd hmatch.2.1 (by norm_num)

end CFSG.OddStandard.SmallF3.HypA2Leaves
