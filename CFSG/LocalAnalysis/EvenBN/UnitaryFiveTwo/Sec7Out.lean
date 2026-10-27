module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelGlobalAut

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Fischer

theorem isSolvable_outer_SU52 : Group.IsSolvable (Outer SU52) := by
  have hker : inner SU52 ≤ (fieldFactor : MulAut SU52 →* (F4 ≃+* F4)).ker := by
    rintro _ ⟨s, rfl⟩
    exact fieldFactor_conj s
  let φ : Outer SU52 →* (F4 ≃+* F4) := QuotientGroup.lift (inner SU52) fieldFactor hker
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : fieldFactor α = 1 := hx
    obtain ⟨s, hs⟩ := (fieldFactor_eq_one_iff α).1 h1
    exact (QuotientGroup.eq_one_iff _).2 ⟨s, hs.symm⟩
  have hcyc : IsCyclic (F4 ≃+* F4) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card (p := 2) card_ringEquiv_F4
  exact Group.isSolvable_of_isSolvable_injective hinj

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
