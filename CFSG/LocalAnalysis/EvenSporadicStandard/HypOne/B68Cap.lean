module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.B68Defs
public import CFSG.Monster.Existence.StdOdd.Reduce
public import CFSG.Monster.Existence.StdOdd.Cert.Cent17
public import CFSG.Monster.B.Pinned.Primes.SeedGL

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.B.TwoA.Amalgam


theorem cap_baby : Cap (G := B) babyCentOrder := by
  intro u x hu hx hux
  have hfin : Finite B := CFSG.Monster.B.Pinned.finite_B
  have h3 : Nat.card ↥(centralizer ({babyRep 3} : Set B)) ≠ babyCentOrder 0 := by
    have h3' : Nat.card ↥(centralizer ({babyRep 3} : Set B)) = babyCentOrder 2 :=
      natCard_centralizer_rep_three
    rw [h3']
    decide
  obtain ⟨ψ⟩ := StdOdd.nonempty_centralizer_mulEquiv_Eam_of_babyInv_zero h3
    (show BabyInv 0 u from hu)
  have hxC : x ∈ centralizer ({u} : Set B) := (mem_centralizer_singleton_iff (G := B)).2 hux.symm
  let x' : ↥(centralizer ({u} : Set B)) := ⟨x, hxC⟩
  have hx' : orderOf x' = 17 := by
    rw [← hx]
    exact Subgroup.orderOf_mk _ _
  have hfinE : Finite ↥Eam := Finite.of_equiv _ ψ.toEquiv
  have hy : orderOf (ψ x') = 17 := by
    rw [MulEquiv.orderOf_eq]
    exact hx'
  obtain ⟨hidx, -, -, -, hZ2, ⟨e⟩, -⟩ := short_F4_derived_standard_perfect_cover
  have hfinS : Finite ↥stdGroup := StdOdd.Cert.rgrp_finite
  have hp2 : ¬ 17 ^ 2 ∣ Nat.card ↥stdGroup := by
    rw [card_stdGroup]
    norm_num
  have hT : ∀ y : ↥stdGroup, orderOf y = 17 →
      Nat.card (centralizer ({y} : Set ↥stdGroup)) ≤ 17 := by
    intro y hy17
    have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    rw [StdOdd.Cert.card_centralizer_eq_of_sylow_prime hp2 StdOdd.Cert.orderOf_rep17 hy17,
      StdOdd.Cert.card_centralizer_rep17]
  have hE := card_centralizer_le_of_cover hidx hZ2 e hT hy
  exact (card_inf_centralizer_le_of_mulEquiv (G := B) hxC ψ).trans hE

end CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68
