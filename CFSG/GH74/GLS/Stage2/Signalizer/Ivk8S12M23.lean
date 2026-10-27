module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Ord
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.false_of_M23
    (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (h : NativeSporadic.IsSporadic (↥J ⧸ center ↥J) .M23) : False := by
  obtain ⟨e⟩ := h
  have hN : Nat.card (↥J ⧸ center ↥J) = 10200960 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.m23_card
  refine hfr.false_of_order hJ hN (by decide) ?_
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hJ.1
  have hZ : center (↥J ⧸ center ↥J) = ⊥ := center_eq_bot_of_not_solvable hns
  have hle := CFSG.Sporadic.Schreier.m23_mulAut_card
  have hY : Nat.card (MulAut (↥J ⧸ center ↥J)) ≤ 1 * 10200960 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    rw [CFSG.Sporadic.Schreier.m23_card] at hle
    exact le_of_le_of_eq hle (one_mul _).symm
  exact not_dvd_card_mulAut hZ hN hY (fun m h1 h2 => by
    obtain rfl : m = 1 := by omega
    decide)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
