module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Ord
public import CFSG.Sporadic.Schreier.J1Outer

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.false_of_J1
    (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (h : NativeSporadic.IsSporadic (↥J ⧸ center ↥J) .J1) : False := by
  obtain ⟨e⟩ := h
  have hN : Nat.card (↥J ⧸ center ↥J) = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  refine hfr.false_of_order hJ hN (by decide) ?_
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hJ.1
  have hZ : center (↥J ⧸ center ↥J) = ⊥ := center_eq_bot_of_not_solvable hns
  have hOut : Nat.card (OuterAutomorphisms.Outer NativeSporadic.J1) = 1 :=
    (CFSG.Sporadic.Schreier.at_j1_schreier).1
  have hle := card_mulAut_le_of_outer (G := NativeSporadic.J1) hOut.le
  have hY : Nat.card (MulAut (↥J ⧸ center ↥J)) ≤ 1 * 175560 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    rw [CFSG.Sporadic.J1.card_J1] at hle
    exact hle
  exact not_dvd_card_mulAut hZ hN hY (fun m h1 h2 => by
    obtain rfl : m = 1 := by omega
    decide)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
