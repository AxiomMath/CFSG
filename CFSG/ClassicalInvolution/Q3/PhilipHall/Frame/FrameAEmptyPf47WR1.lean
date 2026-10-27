module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf17Inst
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WR1Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Disconnected.AschTight

section Struct

variable {Y : Type} [Group Y] [Finite Y]

theorem aStar_restrict_top {Δ : Set (Subgroup Y)} (hΔ : HypOmegaGen Δ) {K : Subgroup Y}
    (hall : aStar Δ K = Δ) :
    aStar (restrictFamily Δ ⊤) (K.subgroupOf ⊤) = restrictFamily Δ ⊤ := by
  have hK : K ∈ Δ := by
    rw [← hall]
    exact Relation.ReflTransGen.refl
  have hK' : K.subgroupOf ⊤ ∈ restrictFamily Δ ⊤ := subgroupOf_mem_restrictFamily hK le_top
  have key : ∀ M ∈ aStar Δ K, M.subgroupOf ⊤ ∈ aStar (restrictFamily Δ ⊤) (K.subgroupOf ⊤) := by
    intro M hM
    induction hM with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      refine ih.tail ?_
      obtain ⟨hcΔ, hA | hA | ⟨htw, hne⟩⟩ := hbc
      · obtain ⟨zb, zc, hv⟩ := hA
        exact ⟨subgroupOf_mem_restrictFamily hcΔ le_top,
          Or.inl ⟨_, _, aViol_restrict_gen hΔ le_top le_top hv⟩⟩
      · obtain ⟨zc, zb, hv⟩ := hA
        exact ⟨subgroupOf_mem_restrictFamily hcΔ le_top,
          Or.inr (Or.inl ⟨_, _, aViol_restrict_gen hΔ le_top le_top hv⟩)⟩
      · exact ⟨subgroupOf_mem_restrictFamily hcΔ le_top,
          Or.inr (Or.inr ⟨twinSet_subgroupOf le_top le_top htw,
            subgroupOf_ne_of_ne le_top le_top hne⟩)⟩
  refine Set.Subset.antisymm (fun L hL => (mem_aStar_symm hK' hL).1) ?_
  rintro _ ⟨L, hL, -, rfl⟩
  refine key L ?_
  rw [hall]
  exact hL

theorem w_struct {Δ : Set (Subgroup Y)} (hΔ : TypeRHyp Δ) {K : Subgroup Y} (hK : K ∈ Δ)
    (hA : ¬ AEmpty Δ K) (hall : aStar Δ K = Δ) (hV : vStar Δ K = Δ) (hgen : omegaGen Δ = ⊤)
    {W : Subgroup (SecQuot (⊤ : Subgroup Y))} [W.Normal]
    (hW : WSet (oddQuotientFamily (restrictFamily Δ ⊤)) = {W})
    (hD : Nonempty ((SecQuot (⊤ : Subgroup Y) ⧸ W) ≃* DihedralGroup 6)) :
    Nonempty (↥W ≃* Multiplicative (ZMod 4 × ZMod 4)) ∧
      Subgroup.centralizer (W : Set (SecQuot (⊤ : Subgroup Y))) = W := by
  have hK' : K.subgroupOf ⊤ ∈ restrictFamily Δ ⊤ := subgroupOf_mem_restrictFamily hK le_top
  have hA' : ¬ AEmpty (restrictFamily Δ ⊤) (K.subgroupOf ⊤) := by
    obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
    exact not_aEmpty_iff.mpr ⟨J.subgroupOf ⊤, _, _, aViol_restrict_gen hΔ.hyp le_top le_top hv⟩
  exact WR1.w_struct_gen (hΔ.restrict ⊤) hK' hA' (aStar_restrict_top hΔ.hyp hall) hW hD

end Struct

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
