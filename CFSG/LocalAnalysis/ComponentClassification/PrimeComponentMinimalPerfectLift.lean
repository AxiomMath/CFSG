module

public import CFSG.LocalAnalysis.ComponentClassification.CanonicalPrimeComponentLift

public section

namespace CFSG.ComponentClassification.PrimeComponentLift

open CFSG

variable {X : Type*} [Group X] [Finite X]

theorem prime_component_minimal_perfect_lift (p : ℕ) [Fact p.Prime] :
    (∀ J : Subgroup (X ⧸ pPrimeCore p X), IsComponent J →
      ∃ L : Subgroup X, IsPComponent p L ∧
        L.map (QuotientGroup.mk' (pPrimeCore p X)) = J ∧ Group.IsPerfect L) ∧
    ∀ L : Subgroup X, IsPComponent p L →
      Group.IsPerfect L ∧
      (∃ e : L ⧸ pPrimeCore p L ≃* L.map (QuotientGroup.mk' (pPrimeCore p X)),
        ∀ l : L, (e (QuotientGroup.mk' (pPrimeCore p L) l) : X ⧸ pPrimeCore p X) =
          QuotientGroup.mk' (pPrimeCore p X) (l : X)) ∧
      IsComponent (L.map (QuotientGroup.mk' (pPrimeCore p X))) := by
  have hperfect : ∀ L : Subgroup X, IsPComponent p L → Group.IsPerfect L :=
    fun L hL => CatalogueBHeldSmallCore.pComponent_perfect p L hL
  refine ⟨fun J hJ => ?_, fun L hL => ?_⟩
  · obtain ⟨hL, hLJ, -, -⟩ := (CatalogueBPrimeJoin.canonical_prime_component_lift p).1 J hJ
    exact ⟨_, hL, hLJ, hperfect _ hL⟩
  · obtain ⟨K, hK, hsub, hLK, -⟩ := id hL
    refine ⟨hperfect L hL, ⟨CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage p L hsub,
      CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage_mk p L hsub⟩, ?_⟩
    rw [hLK]
    exact hK

end CFSG.ComponentClassification.PrimeComponentLift
