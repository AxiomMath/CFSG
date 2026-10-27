module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRowsLarge
public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic

@[expose] def IsTwoBCover (L : Type) [Group L] : Prop :=
  Group.IsPerfect L ∧ Nat.card (center L) = 2 ∧ IsSporadic (L ⧸ center L) .B

theorem IsTwoBCover.of_stdHyp {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : EvenSporadicStandard.StdHyp G L) (h2 : Nat.card (center L) = 2)
    (hB : IsSporadic (L ⧸ center L) .B) : IsTwoBCover L :=
  ⟨Group.isPerfect_def.2 h.standard.1.1, h2, hB⟩

variable {L : Type} [Group L]

theorem IsTwoBCover.exists_hom (h : IsTwoBCover L) :
    ∃ φ : L →* Carrier .B, Function.Surjective φ ∧ Nat.card φ.ker = 2 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center L)), ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    exact ⟨l, rfl⟩
  · have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).ker = center L := by
      ext c
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [hker, hc]

section Certified


theorem IsTwoBCover.nonempty_mulEquiv_R433 (h : IsTwoBCover L) :
    Nonempty (L ≃* CFSG.YGroups.R433) := by
  obtain ⟨φ, hφ, hk⟩ := h.exists_hom
  exact nonempty_mulEquiv_R433_of_doubleCover φ hφ h.1 hk

theorem IsTwoBCover.nonempty_mulEquiv {L' : Type} [Group L'] (h : IsTwoBCover L)
    (h' : IsTwoBCover L') : Nonempty (L ≃* L') := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_R433
  obtain ⟨e'⟩ := h'.nonempty_mulEquiv_R433
  exact ⟨e.trans e'.symm⟩

end Certified

section Inner


theorem IsTwoBCover.allInner (h : IsTwoBCover L) (α : MulAut L) : ∃ l : L, α = MulAut.conj l := by
  obtain ⟨hp, -, ⟨e⟩⟩ := h
  refine EvenSporadicStandard.mulAut_inner_of_inner_centerQuotient (Group.isPerfect_def.1 hp)
    ?_ α
  exact CFSG.ComponentClassification.BMCase.inner_of_equiv e
    CFSG.RankThree.PartOne.SPOR.allInner_B

end Inner

end CFSG.EvenSporadicStandard.TwoB
