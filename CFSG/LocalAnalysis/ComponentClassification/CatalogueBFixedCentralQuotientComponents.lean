module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime

public section

namespace CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

variable {G : Type*} [Group G] [Finite G]

theorem pComponent_restrict_normal (p : ℕ) [Fact p.Prime]
    (N L : Subgroup G) [N.Normal] (hle : L ≤ N) (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.subgroupOf N) := by
  apply (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p N L hle).mpr
  apply (LBalance.pComponent_iff_minimal_image p N L hle).mpr
  have hnative := (CatalogueBAlternating.pComponent_iff_minimal_image p L).mp hL
  refine ⟨?_, ?_, ?_⟩
  · apply (LBalance.subnormal_subgroupOf_iff hle).mp
    exact Components.chain_of_mathlib_subnormal (hL.choose_spec.2.1.subgroupOf)
  · let q := QuotientGroup.mk' (CFSG.pPrimeCore p G)
    let I := N.map q
    have hI : CFSG.Open.IsComponentOf ((L.map q).subgroupOf I) ⊤ :=
      LocalComponents.of_overgroup hnative.2.1 (Subgroup.map_mono hle)
    have heq : (L.map q).subgroupOf I =
        (LBalance.quotientImage p N L).map (LBalance.normalQuotientEquivImage p N).toMonoidHom := by
      have h := congrArg (Subgroup.comap I.subtype)
        (LBalance.quotientImage_normal_transport p N L hle)
      change (((LBalance.quotientImage p N L).map
        (LBalance.normalQuotientEquivImage p N).toMonoidHom).map I.subtype).comap I.subtype =
          (L.map q).subgroupOf I at h
      rw [Subgroup.comap_map_eq_self_of_injective I.subtype_injective] at h
      exact h.symm
    rw [heq] at hI
    exact (LocalComponents.equiv_iff (LBalance.normalQuotientEquivImage p N)
      (LBalance.quotientImage p N L)).mp hI
  · intro J hJL hJ hmap
    have hJtop : CFSG.Open.IsSubnormal J ⊤ :=
      Components.chain_of_mathlib_subnormal
        (Components.mathlib_subnormal_of_chain hJ (inferInstance : N.Normal).isSubnormal)
    exact hnative.2.2 J hJL hJtop
      ((LBalance.normal_quotientImage_eq_iff p N J L (hJL.trans hle) hle).mp hmap)

theorem pComponent_in_normal_of_solvable_quotient (p : ℕ) [Fact p.Prime]
    (N L : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (hL : CFSG.IsPComponent p L) :
    L ≤ N ∧ CFSG.IsPComponent p (L.subgroupOf N) := by
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  have hle := CatalogueBLinearTwo.perfect_le_normal_of_solvable_quotient N L
  exact ⟨hle, pComponent_restrict_normal p N L hle hL⟩

theorem pComponent_normal_iff (p : ℕ) [Fact p.Prime]
    (N L : Subgroup G) [N.Normal] (hle : L ≤ N) :
    CFSG.IsPComponent p (L.subgroupOf N) ↔ CFSG.IsPComponent p L := by
  constructor
  · intro hL
    have h := CatalogueBAlternating.pComponent_of_normal_subgroup p N (L.subgroupOf N) hL
    simpa only [Subgroup.map_subgroupOf_eq_of_le hle] using h
  · exact pComponent_restrict_normal p N L hle

theorem p_components_solvable_quotient_invariance (p : ℕ) (hp : p.Prime)
    (N L : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)] :
    CFSG.IsPComponent p L ↔ L ≤ N ∧ CFSG.IsPComponent p (L.subgroupOf N) := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · exact pComponent_in_normal_of_solvable_quotient p N L
  · rintro ⟨hle, hL⟩
    exact (pComponent_normal_iff p N L hle).mp hL

theorem pComponent_quasisimple_of_normal_solvable_quotient
    (p : ℕ) [Fact p.Prime] (N : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (hN : ∀ J : Subgroup N, CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (L : Subgroup G) (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  obtain ⟨hle, hrestricted⟩ := pComponent_in_normal_of_solvable_quotient p N L hL
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
      (CatalogueBAlternating.quasisimple_iff_native.mp (hN _ hrestricted)))

end CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
