module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.OmegaPilot (exists_component_centralizer_of_conj exists_component_fixSub
  orderOf_eq_two_of_conj)

variable {S : Type} [Group S] [Finite S]

theorem orderOf_eq_two_of_properFixedComponent [IsSimpleGroup S] {σ : MulAut S}
    {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P) : orderOf σ = 2 :=
  orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one

theorem component_of_properFixedComponent_sporadic [IsSimpleGroup S]
    {s : TauCeti.SporadicName} (hs : CatalogueU.SporadicOddCoreFree s)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S}
    {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P) :
    IsComponent (P.subgroupOf (fixedSubgroup σ)) ∧
      Nonempty (P ⧸ Open.fusionZStar P ≃* (P.subgroupOf (fixedSubgroup σ)) ⧸
        center (P.subgroupOf (fixedSubgroup σ))) :=
  h.isComponent_of_oddCore (CatLeaf.oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (CatLeaf.mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hs hna e)
    (orderOf_eq_two_of_properFixedComponent h))

section Rows

open CFSG.Sporadic.FischerOddCore

omit [Finite S] in
theorem card_quotient_center_of_fi22
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .Fi22) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 9196830720 ∨ Nat.card (D ⧸ center D) = 174182400 ∨
      Nat.card (D ⧸ center D) = 1451520 := by
  rcases CatLeaf.exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
    rw [← hcard]
    exact .inl (CTI_Fi22_involution_local_components_unitary_quotient_order e u
      (orderOf_eq_two_of_conj hS hna hσ) B hB)
  · obtain ⟨B, hB, hcard⟩ := exists_component_fixSub σ hD
    have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    rw [← hcard]
    exact .inr (fi22OuterComponentsInput_holds S ⟨e⟩ σ hσ2 hout B hB)

omit [Finite S] in
theorem card_quotient_center_of_fi23
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .Fi23) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 64561751654400 ∨ Nat.card (D ⧸ center D) = 9196830720 := by
  obtain ⟨u, rfl⟩ := BMCase.inner_of_equiv e fi23_mulAut_eq_conj σ
  obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
  have h := RestrictedStd.Spor.fi23_inner_comps e u (orderOf_eq_two_of_conj hS hna hσ) B hB
  rw [← hcard]
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

end Rows

omit [Finite S] in
theorem card_quotient_center_of_co1
    (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .Co1) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 251596800 := by
  obtain ⟨u, rfl⟩ := BMCase.inner_of_equiv e RankThree.PartOne.SPOR.allInner_Co1 σ
  obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
  rw [← hcard]
  exact (RestrictedStd.Spor.co1LocalComponentsInput_holds S e u
    (orderOf_eq_two_of_conj hS hna hσ) B hB).1

end CFSG.ComponentClassification.GrSLit.L34Sec5S
