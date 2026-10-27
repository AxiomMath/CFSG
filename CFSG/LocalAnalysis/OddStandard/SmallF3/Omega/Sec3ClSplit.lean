module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Inputs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82ClosureAt (P : (Q : Type) → [Group Q] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (w : G), InF L → P (↥L ⧸ oddCore ↥L) →
    orderOf w = 2 → w ∈ normalizer (L : Set G) →
      ∀ J : Subgroup G, IsComponentIn J (L ⊓ centralizer ({w} : Set G)) → InFStar J

@[expose] def ShapeO5 (Q : Type) [Group Q] : Prop := LieModel Q .PSp 2 3 1

@[expose] def ShapeO6P (Q : Type) [Group Q] : Prop := LieModel Q .PSL 4 3 1

@[expose] def ShapeO6M (Q : Type) [Group Q] : Prop := LieModel Q .PSU 4 3 1

@[expose] def ShapeO7 (Q : Type) [Group Q] : Prop := LieModel Q .POmegaOdd 3 3 1

@[expose] def ShapeO8P (Q : Type) [Group Q] : Prop := LieModel Q .POmegaPlus 4 3 1

theorem asc82OmegaPlusClosure_iff_at : Asc82OmegaPlusClosure ↔ Asc82ClosureAt ShapeO8P :=
  ⟨fun h G _ _ L w hL hP hw hwN J hJ => h G L ⟨hL, hP⟩ w hw hwN J hJ,
    fun h G _ _ Y hY s hs hsN J hJ => h G Y s hY.1 hY.2 hs hsN J hJ⟩

theorem asc82Lemma37_of_parts (h36 : Asc82Lemma36) (h37F : Asc82Lemma37F)
    (h5 : Asc82ClosureAt ShapeO5) (h6p : Asc82ClosureAt ShapeO6P)
    (h6m : Asc82ClosureAt ShapeO6M) (h6m2 : Asc82ClosureAt IsTwoU43)
    (h7 : Asc82ClosureAt ShapeO7) (h38 : Asc82Lemma38) (h311 : Asc82Lemma311) :
    Asc82Lemma37 := by
  intro G _ _ t L hS z g hz hw
  apply inSubgroup_layer_eq_bot_of_forall
  intro J hJ
  have hnorm := conjugate_eq_self_of_lemma36 h36 hS
  have hwN : (g⁻¹ * z * g) ∈ normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have := hnorm (g⁻¹ * z * g)⁻¹ (inv_mem hw)
    rw [conjugate_inv_eq_map_conj] at this
    simpa using this
  have hw2 : orderOf (g⁻¹ * z * g) = 2 := by
    rw [show g⁻¹ * z * g = (MulAut.conj g⁻¹) z by simp [MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq, hz.1]
  have hJF : InFStar J := by
    have hL := hS.inF
    rcases hL.2 with (h | h | h | h | h | h) | h
    · exact h5 G L _ hL h hw2 hwN J hJ
    · exact h6p G L _ hL h hw2 hwN J hJ
    · exact h6m G L _ hL h hw2 hwN J hJ
    · exact h7 G L _ hL h hw2 hwN J hJ
    · exact absurd h (h311 G t L hS)
    · exact absurd h (h38 G t L hS)
    · exact h6m2 G L _ hL h hw2 hwN J hJ
  exact h37F G t L hS z g hz hw J ⟨hJ, hJF⟩

end CFSG.OddStandard.SmallF3.Omega
