module

public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census228Spor

open Subgroup CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

theorem exists_hom_range_eq_closure {G : Type*} [Group G] {m : ℕ} (g : Fin m → G)
    (ws : List (List (Fin m × Bool))) (hws : ∀ w ∈ ws, evalW g w = 1) :
    ∃ φ : PG m ws →* G, φ.range = closure (Set.range g) := by
  have hrel : ∀ r ∈ ({r | r ∈ ws.map FreeGroup.mk} : Set (FreeGroup (Fin m))),
      FreeGroup.lift g r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [lift_mk_eq_evalW]
    exact hws w hw
  refine ⟨PresentedGroup.toGroup hrel, ?_⟩
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 2
  funext i
  exact PresentedGroup.toGroup.of _

theorem nonempty_mulEquiv_of_presented {G₁ G₂ : Type*} [Group G₁] [Group G₂] {m : ℕ}
    (g₁ : Fin m → G₁) (g₂ : Fin m → G₂) (ws : List (List (Fin m × Bool)))
    (h₁ : ∀ w ∈ ws, evalW g₁ w = 1) (h₂ : ∀ w ∈ ws, evalW g₂ w = 1)
    (hfin : Finite (PG m ws)) (N : ℕ) (hP : Nat.card (PG m ws) ≤ N)
    (hN₁ : N ≤ Nat.card (closure (Set.range g₁))) (hN₂ : N ≤ Nat.card (closure (Set.range g₂))) :
    Nonempty (closure (Set.range g₁) ≃* closure (Set.range g₂)) := by
  obtain ⟨φ₁, hφ₁⟩ := exists_hom_range_eq_closure g₁ ws h₁
  obtain ⟨φ₂, hφ₂⟩ := exists_hom_range_eq_closure g₂ ws h₂
  have e₁ : PG m ws ≃* closure (Set.range g₁) := by
    have hb : Function.Bijective φ₁.rangeRestrict :=
      φ₁.rangeRestrict_surjective.bijective_of_nat_card_le
        (hP.trans (hN₁.trans (Nat.card_congr (MulEquiv.subgroupCongr hφ₁).symm.toEquiv).le))
    exact (MulEquiv.ofBijective φ₁.rangeRestrict hb).trans (MulEquiv.subgroupCongr hφ₁)
  have e₂ : PG m ws ≃* closure (Set.range g₂) := by
    have hb : Function.Bijective φ₂.rangeRestrict :=
      φ₂.rangeRestrict_surjective.bijective_of_nat_card_le
        (hP.trans (hN₂.trans (Nat.card_congr (MulEquiv.subgroupCongr hφ₂).symm.toEquiv).le))
    exact (MulEquiv.ofBijective φ₂.rangeRestrict hb).trans (MulEquiv.subgroupCongr hφ₂)
  exact ⟨e₁.symm.trans e₂⟩

end CFSG.AGLEmbeddingD2.Wilson.Census228Spor
