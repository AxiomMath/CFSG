module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lLift

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.OddStandard.SmallF3.HypA2 (FStarSimple Chev3Datum)

theorem a2l_fStarSimple_psl33 {S : Type} [Group S] (h : LieModel S .PSL 3 3 1) :
    FStarSimple S := Or.inr (Or.inr (Or.inl h))

theorem a2l_fStarSimple_psu33 {S : Type} [Group S] (h : LieModel S .PSU 3 3 1) :
    FStarSimple S := Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem a2l_fStarSimple_psp23 {S : Type} [Group S] (h : LieModel S .PSp 2 3 1) :
    FStarSimple S := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem a2l_fStarSimple_psl43 {S : Type} [Group S] (h : LieModel S .PSL 4 3 1) :
    FStarSimple S := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem a2l_fStarSimple_psu43 {S : Type} [Group S] (h : LieModel S .PSU 4 3 1) :
    FStarSimple S := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem a2l_fStarSimple_pOmegaOdd33 {S : Type} [Group S] (h : LieModel S .POmegaOdd 3 3 1) :
    FStarSimple S := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem a2l_fStarSimple_pOmegaPlus43 {S : Type} [Group S] (h : LieModel S .POmegaPlus 4 3 1) :
    FStarSimple S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem a2l_fStarSimple_pOmegaMinus43 {S : Type} [Group S] (h : LieModel S .POmegaMinus 4 3 1) :
    FStarSimple S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))

theorem a2l_chev3Datum_of_rows (hGA : TBLit.GriessMultipliersOdd)
    (hSchur : SolAltLit.SchurAlternatingMultiplierInput) (hR : a2lRows)
    (hE : a2lChev3Exceptions) : Chev3Datum := by
  intro K _ _ hK h2 hS hnF σ hσ X hXσ hXc hXF
  have key : a2lDatum (K ⧸ center K) →
      (center K = ⊥ ∧ LieModel K .PSL 2 3 8) ∨ HypA2.KDatum K :=
    fun h => Or.inr (Or.inr (a2l_noncentralDatum_of_quotient hGA hSchur h2 h))
  obtain ⟨τ, n, f, hm⟩ := hS
  obtain ⟨-, hf1, hmatch⟩ := hm.admissible
  cases τ with
  | PSL =>
    obtain ⟨hn2, -, -⟩ := hmatch
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact hE.l2 K hK h2 ⟨_, _, _, hm⟩ hnF ⟨f, hm⟩ σ hσ X hXσ hXc hXF
    · by_cases hc : 2 ≤ f ∨ 5 ≤ n
      · exact key (hR.psl _ n f hn3 hc hm)
      · exfalso
        obtain rfl : f = 1 := by omega
        rcases (show n = 3 ∨ n = 4 by omega) with rfl | rfl
        · exact hnF (a2l_fStarSimple_psl33 hm)
        · exact hnF (a2l_fStarSimple_psl43 hm)
  | PSU =>
    obtain ⟨hn3, -⟩ := hmatch
    by_cases hc : 2 ≤ f ∨ 5 ≤ n
    · exact key (hR.psu _ n f hn3 hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      rcases (show n = 3 ∨ n = 4 by omega) with rfl | rfl
      · exact hnF (a2l_fStarSimple_psu33 hm)
      · exact hnF (a2l_fStarSimple_psu43 hm)
  | PSp =>
    obtain ⟨hn2, -⟩ := hmatch
    by_cases hc : 2 ≤ f ∨ 3 ≤ n
    · exact key (hR.psp _ n f hn2 hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      obtain rfl : n = 2 := by omega
      exact hnF (a2l_fStarSimple_psp23 hm)
  | POmegaOdd =>
    obtain ⟨hn3, -⟩ := hmatch
    by_cases hc : 2 ≤ f ∨ 4 ≤ n
    · exact key (hR.oOdd _ n f hn3 hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      obtain rfl : n = 3 := by omega
      exact hnF (a2l_fStarSimple_pOmegaOdd33 hm)
  | POmegaPlus =>
    by_cases hc : 2 ≤ f ∨ 5 ≤ n
    · exact key (hR.oPlus _ n f hmatch hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      obtain rfl : n = 4 := by omega
      exact hnF (a2l_fStarSimple_pOmegaPlus43 hm)
  | POmegaMinus =>
    by_cases hc : 2 ≤ f ∨ 5 ≤ n
    · exact key (hR.oMinus _ n f hmatch hc hm)
    · exfalso
      obtain rfl : f = 1 := by omega
      obtain rfl : n = 4 := by omega
      exact hnF (a2l_fStarSimple_pOmegaMinus43 hm)
  | G2 =>
    obtain ⟨rfl, -⟩ := hmatch
    by_cases hc : 2 ≤ f
    · exact key (hR.g2 _ f hc hm)
    · obtain rfl : f = 1 := by omega
      exact hE.g23 K hK h2 ⟨_, _, _, hm⟩ hnF hm σ hσ X hXσ hXc hXF
  | F4 => obtain rfl := hmatch; exact key (hR.f4 _ f hm)
  | E6 => obtain rfl := hmatch; exact key (hR.e6 _ f hm)
  | E7 => obtain rfl := hmatch; exact key (hR.e7 _ f hm)
  | E8 => obtain rfl := hmatch; exact key (hR.e8 _ f hm)
  | twistedE6 => obtain rfl := hmatch; exact key (hR.twistedE6 _ f hm)
  | trialityD4 => obtain rfl := hmatch; exact key (hR.trialityD4 _ f hm)
  | twistedB2 => exact absurd hmatch.2.1 (by norm_num)
  | twistedF4 => exact absurd hmatch.2.1 (by norm_num)
  | twistedG2 =>
    obtain ⟨rfl, -⟩ := hmatch
    exact hE.ree K hK h2 ⟨_, _, _, hm⟩ hnF ⟨f, hm⟩ σ hσ X hXσ hXc hXF
  | Tits => exact absurd hmatch.2.1 (by norm_num)

end CFSG.OddStandard.SmallF3.HypA2Leaves
