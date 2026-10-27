module

public import CFSG.GH74.GLS.C3.Layer1.EvenSelFin

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.EvenSelP CFSG.GH74.GLS.C3.Layer1 CFSG.Blueprint
open CFSG.Open (ordA)

theorem b_even_select_of_leaves
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (h79 : B_ivk_7_9_pump)
    (h14 : B_prop14) (h5 : B_even_five) : B_even_select := by
  intro G _ _ hG hE hV
  have hClass : FM9Class := fun L _ _ hP hC hU hno =>
    PumpClass.c2_u2_fm9 hGKF hE2 hP hC hU hno
  obtain ⟨x, K, T, Q, hpre, hmax⟩ := exists_evenSelPre hClass h79 h14 hG hE
  refine ⟨x, K, T, Q, hpre.toEvenSel ?_⟩
  intro hA5 hTR
  by_contra hnS
  have hB : EvenBCond x K := h5 G hG hE hV x K T Q hpre hmax hA5 hTR hnS
  rcases hpre.violation with ⟨p, f, hp, hp2, hL, hbad⟩ | hnB
  ·
    obtain ⟨e⟩ := hA5
    have hcard : Nat.card ↥K = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    have h60 : Nat.card ↥K = ordA 1 (p ^ f) := card_of_lieModel_psl2' hL
    have h5' : ordA 1 5 = 60 := by simpa using PumpClass.ordA_one_odd 2
    have hq : p ^ f = 5 :=
      eq_of_ordA_one_eq (hp.odd_of_ne_two hp2).pow (by decide)
        ((h60.symm.trans hcard).trans h5'.symm)
    exact hbad (Or.inl hq)
  · exact hnB hB

end CFSG.GH74.GLS
