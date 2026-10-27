module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiBender
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
import CFSG.LieType.BorelTits.SylowTI
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevBenderTypes

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools Subgroup

private theorem isSylowOf_top_ise {X : Type*} [Group X] (P : Sylow 2 X) :
    IsSylowOf 2 (P : Subgroup X) ⊤ := by
  refine ⟨P.subtype le_top, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_top_eq]

private theorem isSylowOf_top_exists {X : Type*} [Group X] [Finite X] {A : Subgroup X}
    (hA : IsSylowOf 2 A ⊤) : ∃ P : Sylow 2 X, (P : Subgroup X) = A := by
  obtain ⟨-, hP, hdvd⟩ := (isSylowOf_iff.mp hA)
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hP.toSylow hdvd, hP.toSylow_coe hdvd⟩

theorem isGomiL2_or_isGomiU3_or_isGomiSz_of_isGomiAtom_self (hBT : GomiChevBorelTits)
    (hB : GomiBender) {G : Type} [Group G] [Finite G] {L U : Subgroup G} (hL : IsGomiChevTwo ↥L)
    (hU : IsSylowOf 2 U L) (hA : IsGomiAtom L U L) :
    IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨ IsGomiSz (↥L ⧸ center ↥L) := by
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
  have hAtomQ : IsGomiAtom ⊤ (Q : Subgroup ↥L) ⊤ := by
    have h := (isGomiAtom_iff_subgroupOf hU.le le_rfl).mp hA
    rwa [← hQ, Subgroup.subgroupOf_self] at h
  have hcov : Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) ⋖ ⊤ :=
    (isGomiAtom_top_iff_covBy (Q : Subgroup ↥L) ⊤).mp hAtomQ
  have hex : ∃ g : ↥L, g ∉ Subgroup.normalizer ((Q : Subgroup ↥L) : Set ↥L) := by
    by_contra h
    rw [not_exists] at h
    refine (ne_of_lt hcov.lt) (by rw [Subgroup.eq_top_iff']; intro x; exact not_not.mp (h x))
  obtain ⟨g, hg⟩ := hex
  have hgQ : g • Q ≠ Q := fun h =>
    hg (by simpa only [Sylow.coe_coe] using (Sylow.smul_eq_iff_mem_normalizer.mp h))
  have hiso : IsPIsolatedOver 2 (⊤ : Subgroup ↥L) ⊥ := by
    refine ⟨(Q : Subgroup ↥L), ((g • Q : Sylow 2 ↥L) : Subgroup ↥L),
      isSylowOf_top_ise Q, isSylowOf_top_ise (g • Q), ?_⟩
    have hRle : (fun A B : Subgroup ↥L =>
        IsSylowOf 2 A ⊤ ∧ IsSylowOf 2 B ⊤ ∧ ⊥ < A ⊓ B) ≤ (· = ·) := by
      intro A B hAB
      obtain ⟨hA', hB', hlt⟩ := hAB
      obtain ⟨P₁, hP₁⟩ := isSylowOf_top_exists hA'
      obtain ⟨P₂, hP₂⟩ := isSylowOf_top_exists hB'
      have hinf : (P₁ : Subgroup ↥L) ⊓ (P₂ : Subgroup ↥L) ≠ ⊥ := by
        rw [hP₁, hP₂]
        exact ne_of_gt hlt
      have heq : P₁ = P₂ :=
        CFSG.LieType.BorelTits.Holds.eq_of_inf_ne_bot (hBT ↥L hL) hcov hinf
      exact hP₁.symm.trans
        ((congrArg (fun S : Sylow 2 ↥L => (S : Subgroup ↥L)) heq).trans hP₂)
    intro h
    have hEq : (Q : Subgroup ↥L) = ((g • Q : Sylow 2 ↥L) : Subgroup ↥L) :=
      Relation.EqvGen.eqvGen_le hRle _ _ h
    exact hgQ (Sylow.ext hEq.symm)
  exact isGomiL2_or_isGomiU3_or_isGomiSz_of_isPIsolatedOver_top hB hL hiso

end CFSG.GroupTheory
