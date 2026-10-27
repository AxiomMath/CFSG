module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.E6FourFine

open CFSG.Blueprint

@[expose] def OmegaMinus8Fine (ℓ f : ℕ) {G : Type} [Group G] (X : Subgroup G) : Prop :=
  LieModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus 4 ℓ f

theorem OmegaMinus8Fine.of_equiv {G G' : Type} [Group G] [Group G'] {ℓ f : ℕ} {R : Subgroup G}
    {C : Subgroup G'} (e : ↥R ≃* ↥C) (h : OmegaMinus8Fine ℓ f C) : OmegaMinus8Fine ℓ f R :=
  LieModel.of_mulEquiv (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) h

theorem OmegaMinus8Fine.map_conj {G : Type} [Group G] {ℓ f : ℕ} {R : Subgroup G} (φ : G ≃* G)
    (h : OmegaMinus8Fine ℓ f R) : OmegaMinus8Fine ℓ f (R.map φ.toMonoidHom) :=
  OmegaMinus8Fine.of_equiv (R.equivMapOfInjective φ.toMonoidHom φ.injective).symm h

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.E6FourFine

end
