module

public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionSupport

public noncomputable section

namespace CFSG.Wreathed.ReducedInvolution

variable {G : Type*} [Group G]

theorem centralizer_map_mulEquiv (γ : G ≃* G) (y : G) :
    (Subgroup.centralizer {y}).map γ.toMonoidHom = Subgroup.centralizer {γ y} := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg γ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
  · intro h
    apply γ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]

@[expose] def centralizerEquiv (γ : G ≃* G) (y : G) :
    Subgroup.centralizer {y} ≃* Subgroup.centralizer {γ y} :=
  (Subgroup.equivMapOfInjective _ γ.toMonoidHom γ.injective).trans
    (MulEquiv.subgroupCongr (centralizer_map_mulEquiv γ y))

theorem centralizerEquiv_apply (γ : G ≃* G) (y : G) (k : Subgroup.centralizer {y}) :
    (centralizerEquiv γ y k : G) = γ k := rfl

theorem oddCore_centralizer_map (γ : G ≃* G) (y : G) :
    ((CFSG.oddCore (Subgroup.centralizer {y})).map (Subgroup.centralizer {y}).subtype).map
        γ.toMonoidHom =
      (CFSG.oddCore (Subgroup.centralizer {γ y})).map (Subgroup.centralizer {γ y}).subtype := by
  rw [← oddCore_map_mulEquiv (centralizerEquiv γ y), Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem exists_oddCore_equiv {Q : Type*} [Group Q] (γ : G ≃* G) (y : G) {K : Subgroup G}
    (Ψ : Q ≃* K)
    (hK : ((CFSG.oddCore (Subgroup.centralizer {y})).map (Subgroup.centralizer {y}).subtype).map
      γ.toMonoidHom = K) :
    ∃ ψ : CFSG.oddCore (Subgroup.centralizer {y}) ≃* Q,
      ∀ k, (Ψ (ψ k) : G) = γ ((k : Subgroup.centralizer {y}) : G) := by
  let e₁ := Subgroup.equivMapOfInjective (CFSG.oddCore (Subgroup.centralizer {y}))
    (Subgroup.centralizer {y}).subtype (Subgroup.subtype_injective _)
  let e₂ := Subgroup.equivMapOfInjective
    ((CFSG.oddCore (Subgroup.centralizer {y})).map (Subgroup.centralizer {y}).subtype)
    γ.toMonoidHom γ.injective
  refine ⟨e₁.trans (e₂.trans ((MulEquiv.subgroupCongr hK).trans Ψ.symm)), fun k => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

end CFSG.Wreathed.ReducedInvolution
