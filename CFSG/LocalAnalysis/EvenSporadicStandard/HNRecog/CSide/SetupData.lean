module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.GrpOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.BaseLe

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog.Fpf
  CFSG.EvenSporadicStandard.HNRecog

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

private theorem setupData_mem_commutator_iff {Γ : Type*} [Group Γ] (e : Γ ≃* A5WrTwo) (u : Γ) :
    u ∈ commutator Γ ↔ e u ∈ commutator A5WrTwo := by
  have hmap : (commutator Γ).map e.toMonoidHom = commutator A5WrTwo := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← hmap, Subgroup.mem_map_equiv]
  simp

theorem CSideSetup.odd_data [Finite C] (hC : WeakHyp C Q) (S : CSideSetup C Q) {p : ℕ}
    (hp : p = 3 ∨ p = 5) {σ : C} (hσ : orderOf σ = p) :
    ∃ hσL : σ ∈ commutator C, orderOf (S.θ ⟨σ, hσL⟩) = p := by
  have hQ : IsPGroup 2 Q := IsPGroup.of_card hC.plus.2.1
  have hσodd : Odd (orderOf σ) := by
    rw [hσ]
    rcases hp with rfl | rfl <;> decide
  have hmk : orderOf (σ : C ⧸ Q) = p := by
    rw [cSide_orderOf_mk_of_odd hQ hσodd, hσ]
  have hmkodd : Odd (orderOf (σ : C ⧸ Q)) := by
    rw [hmk]
    rcases hp with rfl | rfl <;> decide
  have hcommQ : (σ : C ⧸ Q) ∈ commutator (C ⧸ Q) := by
    rw [setupData_mem_commutator_iff S.e]
    exact cSide_mem_commutator_of_odd (by rw [MulEquiv.orderOf_eq]; exact hmkodd)
  have hσL : σ ∈ commutator C := mem_commutator_of_mk_mem hC.le_commutator hcommQ
  refine ⟨hσL, ?_⟩
  rw [← orderOf_injective A5WrTwo.baseEmb A5WrTwo.baseEmb_injective (S.θ ⟨σ, hσL⟩),
    S.emb ⟨σ, hσL⟩, MulEquiv.orderOf_eq, hmk]

theorem CSideSetup.exists_odd_lift [Finite C] (hC : WeakHyp C Q) (S : CSideSetup C Q) {p : ℕ}
    (hp : p = 3 ∨ p = 5) {g : A5 × A5} (hg : orderOf g = p) :
    ∃ (σ : C) (hσL : σ ∈ commutator C), orderOf σ = p ∧ S.θ ⟨σ, hσL⟩ = g := by
  have hQ : IsPGroup 2 Q := IsPGroup.of_card hC.plus.2.1
  have hbg : orderOf (A5WrTwo.baseEmb g) = p := by
    rw [orderOf_injective A5WrTwo.baseEmb A5WrTwo.baseEmb_injective g, hg]
  have hbgmem : A5WrTwo.baseEmb g ∈ commutator A5WrTwo := by
    rw [← A5WrTwo.range_baseEmb]
    exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
  let r : C ⧸ Q := S.e.symm (A5WrTwo.baseEmb g)
  have her : S.e r = A5WrTwo.baseEmb g := S.e.apply_symm_apply _
  have hro : orderOf r = p := by
    rw [← MulEquiv.orderOf_eq S.e r, her, hbg]
  have hrodd : Odd (orderOf r) := by
    rw [hro]
    rcases hp with rfl | rfl <;> decide
  obtain ⟨σ, hσord, hσmk⟩ := cSide_exists_lift_of_odd hQ hrodd
  have hrcomm : r ∈ commutator (C ⧸ Q) := by
    rw [setupData_mem_commutator_iff S.e, her]
    exact hbgmem
  have hσcomm : σ ∈ commutator C := by
    refine mem_commutator_of_mk_mem hC.le_commutator ?_
    rwa [hσmk]
  refine ⟨σ, hσcomm, ?_, ?_⟩
  · rw [hσord, hro]
  · apply A5WrTwo.baseEmb_injective
    rw [S.emb ⟨σ, hσcomm⟩, hσmk, her]

end CFSG.EvenSporadicStandard.HNRecog.CSide
