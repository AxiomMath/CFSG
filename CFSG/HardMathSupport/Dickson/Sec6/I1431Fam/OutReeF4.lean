module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Rank

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement

theorem t6outreef4_commutator_le_inner {G : Type} [Group G] (hc : IsCyclic (Outer G)) :
    commutator (MulAut G) ≤ inner G := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  have h : (QuotientGroup.mk' (inner G)) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2
      (hc.isMulCommutative.is_comm.comm _ _)]
  exact (QuotientGroup.eq_one_iff _).1 h

section


theorem t6outreef4_innAutDerived_le_inner {P : Type} [Group P] {p f : ℕ}
    (hR : ReeTitsModel P .twistedF4 p f) : innAutDerived P ≤ inner P := by
  obtain ⟨-, -, -, hc, -⟩ := large_Ree_model_field_outer_group_and_inner_involutions P p f hR
  exact sup_le le_rfl (t6outreef4_commutator_le_inner hc)

theorem outDerived3_reeF4 : OutDerived3At FamReeF4 := by
  intro P _ _ t n p f hadm ht hF hm τ hτ _
  obtain rfl := hF
  have hR : ReeTitsModel P .twistedF4 p f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
  exact t6outreef4_innAutDerived_le_inner hR hτ

end

end CFSG.HardMathSupport.Dickson.Sec6.I1431
