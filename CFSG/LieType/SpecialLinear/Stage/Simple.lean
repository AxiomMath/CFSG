module

public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtendScalars

public section

namespace CFSG.LieType.SpecialLinear

open CFSG.Quasithin.SmithCurtis

variable {E k G X : Type*} [Field E] [Field k] [Algebra E k] [Group G]
  [AddCommGroup X] [Module E X]

theorem isSimpleRep_of_isSimpleRep_extendScalars (σ : Representation E G X)
    (h : IsSimpleRep (CFSG.Theory.Representation.extendScalars k σ)) :
    IsSimpleRep σ := by
  classical
  refine ⟨?_, ?_⟩
  · exact (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right (R := E) (M := k)).mp h.1
  · intro W hW
    have hWb : ∀ g, ∀ y ∈ W.baseChange k,
        (CFSG.Theory.Representation.extendScalars k σ g) y ∈ W.baseChange k := by
      intro g y hy
      rw [Submodule.baseChange_eq_span] at hy ⊢
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨w, hw, rfl⟩ := hy
          rw [CFSG.Theory.Representation.extendScalars_apply, TensorProduct.mk_apply,
            LinearMap.baseChange_tmul]
          exact Submodule.subset_span ⟨σ g w, hW g w hw, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
    rcases h.2 (W.baseChange k) hWb with hbot | htop
    · left
      exact Submodule.baseChange_injective (by simpa using hbot)
    · right
      exact Submodule.baseChange_injective (by simpa using htop)

end CFSG.LieType.SpecialLinear
