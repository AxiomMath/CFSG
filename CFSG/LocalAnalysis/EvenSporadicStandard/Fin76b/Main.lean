module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Center
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)
open CFSG.Sporadic.Schreier (j3P j3PermEquiv card_j3P)
open CFSG.Sporadic.SmallOddCore (ctuc_j3_full_automorphism_permutation_model)

theorem index_dvd_two_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite Y]
    (e : Y ≃* X) (hX : center X = ⊥) (hcard : Nat.card (MulAut X) = 2 * Nat.card X) :
    (innAut Y).index ∣ 2 := by
  have : Finite X := Finite.of_equiv Y e.toEquiv
  have hY : center Y = ⊥ := HypOne.center_eq_bot_of_mulEquiv e.symm hX
  have hinj := HypOne.conj_injective_of_center_eq_bot hY
  have h1 : Nat.card (MulAut Y) = Nat.card (MulAut X) := Nat.card_congr (MulAut.congr e).toEquiv
  have h2 : Nat.card Y = Nat.card X := Nat.card_congr e.toEquiv
  exact HypOne.index_dvd_two_of_card_le hinj (by omega)

theorem isSporadic_quotient_of_center_eq_bot {Y : Type} [Group Y] (h : center Y = ⊥)
    {s : TauCeti.SporadicName} (hs : IsSporadic Y s) : IsSporadic (Y ⧸ center Y) s := by
  obtain ⟨e⟩ := hs
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).trans e⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

end CFSG.EvenSporadicStandard.Fin76b
