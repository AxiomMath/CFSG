module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueCases
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueColumns
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeAdicAuxClasses
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeAdicCentralizer

public section

namespace CFSG.Semidihedral.UnitaryDValue

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem not_exceptional (hpair : D.PrincipalPair) (hgw : D.GWStep) (E : D.Exceptional) :
    False := by
  have hsyl : ∀ v ∈ D.QT, v ∉ D.primaryPart 3 →
      (Nat.card (Subgroup.centralizer ({v} : Set G))).factorization 3 = E.h :=
    fun v hv hvP => E.factorization_card_centralizer hgw hv hvP
  refine D.false_of_exceptional_columns hpair E.h E.three_le_h rfl D.QT (D.primaryPart 3)
    D.P_le_QT E.card_QT_eq E.card_P_eq D.tThree D.tThree_mem_QT D.tThree_not_mem_P3 ?_ ?_ ?_ ?_
  · intro v hv hvP
    rw [centralizer_zpowers_eq]
    exact E.odd_card_centralizer hgw hv hvP
  · intro v hv hvP
    rw [centralizer_zpowers_eq]
    exact hsyl v hv hvP
  · intro v hv hvP
    exact E.hasNormalPComplement_centralizer hgw hv hvP
  · intro v hv hvP
    exact E.ncard_conj_coset hgw hsyl hv hvP

theorem d_value (hext : D.CharacterExtend) (htriv : D.CharacterTrivial)
    (hpair : D.PrincipalPair) (hgw : D.GWStep) :
    D.m * Nat.card D.A * Nat.gcd (D.q + 1) 3 = D.q + 1 := by
  rcases D.d_cases hext htriv with h | ⟨hk, hh⟩
  · exact h
  · obtain ⟨E⟩ := D.exists_exceptional hext htriv hk hh
    exact (D.not_exceptional hpair hgw E).elim

end DValueData

end CFSG.Semidihedral.UnitaryDValue
