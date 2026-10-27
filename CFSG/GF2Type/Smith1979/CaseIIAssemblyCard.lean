module

public import CFSG.GF2Type.Smith1979.CaseI25Filter
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GF2Type.Smith1979.CaseIIA0
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.Open CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Data

variable (D : Data S g t)
include D

theorem card_O_eq_orthPlus12 : Nat.card S.O = Case25.orthPlus12Ord := by
  have h12 : finrank (ZMod 2) S.Qt = 12 := by rw [S.finrank_Qt_eq_two_mul_width, D.hw]
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType S.q :=
    ⟨commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), by rw [D.finrank_commSpace, h12],
      fun _ hx => D.q_eq_zero hx⟩
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2) (Q := S.q)
    S.q_nondegenerate (m := 5) (by omega) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  exact Case25.eq_orthPlus12Ord_of_formula (q := Nat.card (ZMod 2)) (by simp) h

theorem card_layer_quotient_dvd_orthPlus12 :
    Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∣
      Case25.orthPlus12Ord := by
  rw [← D.card_O_eq_orthPlus12]
  have h1 : Nat.card (timmesfeldLayer S.Mbar ⧸ center (timmesfeldLayer S.Mbar)) ∣
      Nat.card (timmesfeldLayer S.Mbar) :=
    ⟨_, Subgroup.card_eq_card_quotient_mul_card_subgroup (center (timmesfeldLayer S.Mbar))⟩
  exact h1.trans ((Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _))

end Data

end CFSG.GF2Type.Smith1979.Case2
