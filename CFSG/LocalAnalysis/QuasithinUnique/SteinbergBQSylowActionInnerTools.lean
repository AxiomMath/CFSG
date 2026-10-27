module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.QuasithinUnique

open CFSG.ComponentClassification.PerfectAutomorphisms

namespace SteinbergBQ.SylowActionInner

variable {L X : Type*} [Group L] [Group X]

noncomputable abbrev modelAut (η : L ⧸ Subgroup.center L ≃* X) : MulAut L →* MulAut X :=
  (MulAut.congr η).toMonoidHom.comp (centerQuotientHom L)

theorem modelAut_apply (η : L ⧸ Subgroup.center L ≃* X) (α : MulAut L) (x : L) :
    modelAut η α (η (QuotientGroup.mk x)) = η (QuotientGroup.mk (α x)) := by
  change η (onCenterQuotient α (η.symm (η (QuotientGroup.mk x)))) = _
  rw [MulEquiv.symm_apply_apply]
  exact congrArg η (onCenterQuotient_apply_mk α x)

theorem mem_range_conj_of_modelAut [Group.IsPerfect L] (η : L ⧸ Subgroup.center L ≃* X)
    {α : MulAut L} (h : modelAut η α ∈ (MulAut.conj : X →* MulAut X).range) :
    α ∈ (MulAut.conj : L →* MulAut L).range := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨ℓ, hℓ⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) (η.symm y)
  refine ⟨ℓ, ?_⟩
  have hinj : Function.Injective (modelAut η) :=
    (MulAut.congr η).injective.comp (centerQuotientHom_injective L)
  apply hinj
  rw [← hy]
  ext w
  obtain ⟨z, rfl⟩ := η.surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) z
  rw [QuotientGroup.mk'_apply, modelAut_apply, MulAut.conj_apply, MulAut.conj_apply,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv]
  have hyℓ : η (QuotientGroup.mk ℓ) = y := by
    rw [← QuotientGroup.mk'_apply, hℓ, MulEquiv.apply_symm_apply]
  rw [hyℓ]

variable {K : Type*} [Field K]

end SteinbergBQ.SylowActionInner

end CFSG.QuasithinUnique
