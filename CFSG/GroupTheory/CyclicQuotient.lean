module

public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierBrauer

public section

namespace CFSG

theorem not_dvd_card_range_of_no_normal_index
    {Γ G : Type*} [Group Γ] [Finite Γ] [Group G]
    (δ : Γ →* G) [IsCyclic δ.range]
    {n : ℕ} (hn : 0 < n)
    (hno : ∀ N : Subgroup Γ, N.Normal → N.index ≠ n) :
    ¬ n ∣ Nat.card δ.range := by
  intro hnrange
  haveI : Finite δ.range :=
    Finite.of_surjective δ.rangeRestrict (MonoidHom.rangeRestrict_surjective δ)
  have hcard : Nat.card (Multiplicative (ZMod n)) = n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  obtain ⟨χ, hχ⟩ :=
    CFSG.Semidihedral.SimpleLayerFrontier.exists_surjective_hom_of_cyclic
      (A := δ.range) (B := Multiplicative (ZMod n)) (by simpa [hcard] using hnrange)
  let ψ : Γ →* Multiplicative (ZMod n) := χ.comp δ.rangeRestrict
  have hψ : Function.Surjective ψ :=
    hχ.comp (MonoidHom.rangeRestrict_surjective δ)
  have hidx : ψ.ker.index = n := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top,
      hcard]
  exact hno ψ.ker (MonoidHom.normal_ker ψ) hidx

end CFSG
