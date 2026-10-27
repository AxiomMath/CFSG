module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.LieOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Common

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem factorial_div_two_ne_of_between {n₀ N : ℕ} (h1 : n₀.factorial / 2 < N)
    (h2 : N < (n₀ + 1).factorial / 2) (n : ℕ) : n.factorial / 2 ≠ N := by
  intro h
  rcases Nat.lt_or_ge n₀ n with hn | hn
  · have : (n₀ + 1).factorial ≤ n.factorial := Nat.factorial_le hn
    have : (n₀ + 1).factorial / 2 ≤ n.factorial / 2 := Nat.div_le_div_right this
    omega
  · have : n.factorial ≤ n₀.factorial := Nat.factorial_le hn
    have : n.factorial / 2 ≤ n₀.factorial / 2 := Nat.div_le_div_right this
    omega

theorem thm24Hex_of_card (lo : LieModelOrders) {s : TauCeti.SporadicName} {N : ℕ}
    (hs : ∀ (Y : Type) [Group Y], IsSporadic Y s → Nat.card Y = N)
    (hN : 251596800 < N) (halt : ∀ n : ℕ, n.factorial / 2 ≠ N)
    (X : Type) [Group X] (hq : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (center X)))
    (hX : IsSporadic (X ⧸ center X) s) :
    (¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∧
      ¬ LieModel X .PSL 3 2 2 ∧ ¬ SuzukiModel X 2 3 ∧ ¬ LieModel X .G2 0 2 2 := by
  have hcq : Nat.card (X ⧸ center X) = N := hs _ hX
  have hZfin : Finite ↥(center X) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hQfin : Finite (X ⧸ center X) := Nat.finite_of_card_ne_zero (by omega)
  have : Finite X := Finite.of_subgroup_quotient (center X)
  have hle : Nat.card (X ⧸ center X) ≤ Nat.card X :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  obtain ⟨hP, hS, hG⟩ := lo
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rintro ⟨n, hn5, ⟨e⟩⟩
    have h4 : 4 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    have hZ : Nat.card (center X) = 1 := by
      rw [card_center_of_mulEquiv' e, alternatingGroup.center_eq_bot h4, Subgroup.card_bot]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    rw [hcq, hZ, mul_one] at h1
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h2 : Nat.card X = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
    exact halt n (by omega)
  · have := hP X h
    omega
  · have := hS X h
    omega
  · have := hG X h
    omega

end CFSG.EvenSporadicStandard.Induction
