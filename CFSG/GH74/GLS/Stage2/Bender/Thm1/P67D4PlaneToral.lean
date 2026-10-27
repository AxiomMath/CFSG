module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneLeaf

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Toral

@[expose] def D4PlaneToral : Prop :=
    ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) → (p ^ f) % 3 = 2 →
    ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
      (∀ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p R → R ≠ ⊥ →
        ¬ E ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) →
      ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        ((∃ F : D4PhiFrame K σ (p ^ f) (-1), F.Contains (E.map (β⁻¹).toMonoidHom)) ∧
          ∃ F : D4SteinbergFrame K σ (p ^ f) (-1), F.Contains (E.map (β⁻¹).toMonoidHom)) ∨
        D4PlaneGood σ (p ^ f) (E.map (β⁻¹).toMonoidHom)

end Toral

end CFSG.GH74.GLS.Stage2.Bender.Thm1
