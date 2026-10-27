module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenData
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.FixCount
public import CFSG.Sporadic.Fi24.Simple

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven

open CFSG.Open CFSG.Perm CFSG.Sporadic.Fi24 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (fixS)


@[expose] noncomputable def g7 (j : ℕ) : J := CFSG.Sporadic.Fi23.slpG genG fi24SevenData.words j

@[expose] def conjTs : List ℕ := [3, 21, 49, 56, 63, 70, 77, 84, 91]

structure SevenFacts : Prop where
  pow_x : g7 fi24SevenData.ix ^ 7 = 1
  pow_y : g7 fi24SevenData.iy ^ 7 = 1
  comm : g7 fi24SevenData.ic =
    g7 fi24SevenData.ix * g7 fi24SevenData.iy * g7 fi24SevenData.ix ^ 6 * g7 fi24SevenData.iy ^ 6
  comm_x : g7 fi24SevenData.ic * g7 fi24SevenData.ix = g7 fi24SevenData.ix * g7 fi24SevenData.ic
  comm_y : g7 fi24SevenData.ic * g7 fi24SevenData.iy = g7 fi24SevenData.iy * g7 fi24SevenData.ic
  inj : ∀ i j k i' j' k' : ℕ, i < 7 → j < 7 → k < 7 → i' < 7 → j' < 7 → k' < 7 →
    g7 fi24SevenData.ix ^ i * g7 fi24SevenData.iy ^ j * g7 fi24SevenData.ic ^ k =
      g7 fi24SevenData.ix ^ i' * g7 fi24SevenData.iy ^ j' * g7 fi24SevenData.ic ^ k' →
    i = i' ∧ j = j' ∧ k = k'
  conj : ∀ s : J, orderOf s = 7 →
    ∃ t : J, t * s * t⁻¹ = g7 fi24SevenData.iy ∨ t * s * t⁻¹ = g7 fi24SevenData.ic
  card_y : Nat.card (Subgroup.centralizer ({g7 fi24SevenData.iy} : Set J)) = 17640
  card_c : Nat.card (Subgroup.centralizer ({g7 fi24SevenData.ic} : Set J)) = 2058
  core_y : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({g7 fi24SevenData.iy} : Set J)) = ⊥
  core_c : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({g7 fi24SevenData.ic} : Set J)) = ⊥
  conj_lt : ∀ t ∈ conjTs, ∀ l ∈ (fi24SevenData.conj[t]!).2, l < 2 * 1087
  rel : ∀ t ∈ conjTs, ((fi24SevenData.conj[t]!).2.map (pairG g7)).prod *
      (g7 fi24SevenData.ix ^ (t / 49) * g7 fi24SevenData.iy ^ (t / 7 % 7) *
        g7 fi24SevenData.ic ^ (t % 7)) =
    (if (fi24SevenData.conj[t]!).1 == 0 then g7 fi24SevenData.iy else g7 fi24SevenData.ic) *
      ((fi24SevenData.conj[t]!).2.map (pairG g7)).prod

structure CentFacts : Prop where
  three_y : ∀ u : J, u ^ 3 = 1 → u ≠ 1 → u * g7 fi24SevenData.iy = g7 fi24SevenData.iy * u →
    (fixS u : Finset (Fin 306936)).card = 3240 ∨ (fixS u : Finset (Fin 306936)).card = 0
  three_c : ∀ u : J, u ^ 3 = 1 → u ≠ 1 → u * g7 fi24SevenData.ic = g7 fi24SevenData.ic * u →
    (fixS u : Finset (Fin 306936)).card = 378
  root_y : ∀ g : J, g ^ 7 ≠ g7 fi24SevenData.iy
  root_c : ∀ g : J, g ^ 7 ≠ g7 fi24SevenData.ic
  fix_y : (fixS (g7 fi24SevenData.iy) : Finset (Fin 306936)).card = 21
  fix_c : (fixS (g7 fi24SevenData.ic) : Finset (Fin 306936)).card = 0

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven

end
