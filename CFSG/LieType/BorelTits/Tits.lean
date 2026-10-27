module

public import CFSG.LieType.Ree.TitsQuotient
public import CFSG.LieType.BorelTits.Classical
public import CFSG.LieType.BorelTits.DerivedQuotient

public section

namespace CFSG.LieType.BorelTits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem holdsTits_of_reeTitsModel_tits {G : Type} [Group G] {p f : ℕ}
    (h : ReeTitsModel G .Tits p f) : HoldsTits G p := by
  obtain ⟨⟨-, -, -, hp, hf1⟩, a, hf, hmodel⟩ := h
  subst hp
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have ha : a = 0 := by omega
  subst ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card K = 2 := by rw [hK, hf1, pow_one]
  have hc : CharP K 2 := charP_of_natCard_eq hK
  have : CharP K ReeTag.F4.prime := hc
  exact (holdsTits_derivedCentralQuotient _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed .F4 K 0)).trans
      ((reeFixed .F4 K 0).equivMapOfInjective _ Subtype.val_injective).symm)
    (holds_reeFixed .F4 K 0) (isPGroup_reeFixed_quotient rfl hK2)).of_mulEquiv e.symm

end CFSG.LieType.BorelTits
