module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Parts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.OddQuot

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

variable {D X : Type} [Group D] [Group X]

theorem IsOddCentralExt.finite [Finite D] (hX : IsOddCentralExt D X) : Finite X := by
  obtain ⟨-, π, hπ, -, hodd⟩ := hX
  have hk : Finite π.ker := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hq : Finite (X ⧸ π.ker) :=
    Finite.of_equiv D (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toEquiv
  exact Finite.of_subgroup_quotient π.ker

theorem IsOddCentralExt.quasisimple_target [Finite D] (hX : IsOddCentralExt D X) :
    CFSG.IsQuasisimple D := by
  obtain ⟨hq, π, hπ, hk, -⟩ := hX
  have hperfX : Group.IsPerfect X := hq.1
  have hperfD : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := π) hπ
  obtain ⟨e⟩ := cqEquiv_of_cover π hπ hk
  exact isQuasisimple_of_perfect_simple_quotient hperfD e.symm hq.2.1

theorem IsOddCentralExt.self (hD : CFSG.IsQuasisimple D) : IsOddCentralExt D D :=
  ⟨hD, MonoidHom.id D, Function.surjective_id, by simp, by simp⟩

theorem IsOddCentralExt.oddCore_eq_ker [Finite D] [Finite X] (hD : CFSG.oddCore D = ⊥)
    {π : X →* D} (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker)) :
    CFSG.oddCore X = π.ker := by
  apply le_antisymm
  · have hO : Odd (Nat.card (CFSG.oddCore X)) := odd_card_oddCore' X
    have hn : ((CFSG.oddCore X).map π).Normal :=
      (inferInstance : (CFSG.oddCore X).Normal).map π hπ
    have hodd' : Odd (Nat.card ((CFSG.oddCore X).map π)) :=
      hO.of_dvd_nat (Subgroup.card_map_dvd _ _)
    have hle : (CFSG.oddCore X).map π ≤ CFSG.oddCore D := le_sSup ⟨hn, hodd'⟩
    rw [hD, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
    exact hle
  · exact le_sSup ⟨inferInstance, hodd⟩

theorem IsOddCentralExt.quot_equiv [Finite D] (hD : CFSG.oddCore D = ⊥)
    (hX : IsOddCentralExt D X) : Nonempty ((X ⧸ CFSG.oddCore X) ≃* D) := by
  have := hX.finite
  obtain ⟨-, π, hπ, -, hodd⟩ := hX
  have h := IsOddCentralExt.oddCore_eq_ker hD hπ hodd
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩

theorem isOddCentralExt_quot [Finite D] (hD : CFSG.oddCore D = ⊥) (hX : IsOddCentralExt D X) :
    IsOddCentralExt D (X ⧸ CFSG.oddCore X) := by
  obtain ⟨e⟩ := hX.quot_equiv hD
  exact IsOddCentralExt.isoInv D D (X ⧸ CFSG.oddCore X) e.symm
    (IsOddCentralExt.self hX.quasisimple_target)

noncomputable def quotientOddCoreEquiv'' {Z : Type} [Group Z] (h : CFSG.oddCore Z = ⊥) :
    Z ⧸ CFSG.oddCore Z ≃* Z :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem isOddCentralExt_iso [Finite D] {Y : Type} [Group Y] (hD : CFSG.oddCore D = ⊥)
    (hX : IsOddCentralExt D X) (hY : IsOddCentralExt D Y) (hXo : CFSG.oddCore X = ⊥)
    (hYo : CFSG.oddCore Y = ⊥) : Nonempty (X ≃* Y) := by
  obtain ⟨e1⟩ := hX.quot_equiv hD
  obtain ⟨e2⟩ := hY.quot_equiv hD
  exact ⟨(quotientOddCoreEquiv'' hXo).symm.trans
    (e1.trans (e2.symm.trans (quotientOddCoreEquiv'' hYo)))⟩

theorem isOddCentralExt_cq {Y : Type} [Group Y] (hX : IsOddCentralExt D X)
    (hY : IsOddCentralExt D Y) : Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) := by
  obtain ⟨hqX, π, hπ, hk, -⟩ := hX
  obtain ⟨hqY, π', hπ', hk', -⟩ := hY
  have : Group.IsPerfect X := hqX.1
  have : Group.IsPerfect Y := hqY.1
  obtain ⟨e⟩ := cqEquiv_of_cover π hπ hk
  obtain ⟨e'⟩ := cqEquiv_of_cover π' hπ' hk'
  exact ⟨e.trans e'.symm⟩

theorem IsOddCentralExt.even_center [Finite D] (hD : Even (Nat.card (center D)))
    (hX : IsOddCentralExt D X) : Even (Nat.card (center X)) := by
  have := hX.finite
  obtain ⟨hq, π, hπ, hk, -⟩ := hX
  have : Group.IsPerfect X := hq.1
  exact even_card_center_of_cover π hπ hk hD

end CFSG.EvenSporadicStandard.Induction
