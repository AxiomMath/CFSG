module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup

variable {M : Type*} [Group M] [Finite M] {x : M} {K K' : Subgroup M}

theorem PairConfig.false_of_equiv_unique (hc : PairConfig M x K K') {X : Type*} [Group X]
    [Finite X] (e : ↥(centralizer ({x} : Set M)) ≃* X)
    (hu : ∀ L L' : Subgroup X, IsPComponent 2 L → IsPComponent 2 L' → L = L') : False := by
  have ht := (LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    e).1
  have h1 := (ht _).1 hc.isPComponent_K
  have h2 := (ht _).1 hc.isPComponent_K'
  have h3 := Subgroup.map_injective e.injective (hu _ _ h1 h2)
  have h4 := subgroupOf_inj.mp h3
  rw [inf_of_le_left hc.K_le, inf_of_le_left hc.K'_le] at h4
  exact hc.ne h4

theorem PairConfig.false_of_equiv_simple_normal (hc : PairConfig M x K K') {X : Type*} [Group X]
    [Finite X] (e : ↥(centralizer ({x} : Set M)) ≃* X) (N : Subgroup X) [N.Normal]
    [IsSimpleGroup N] [Group.IsSolvable (X ⧸ N)] : False :=
  hc.false_of_equiv_unique e fun L L' hL hL' =>
    (CatalogueBLinearTwo.pComponent_eq_simple_normal 2 N L hL).trans
      (CatalogueBLinearTwo.pComponent_eq_simple_normal 2 N L' hL').symm

end CFSG.ComponentClassification.Sp4Rec
