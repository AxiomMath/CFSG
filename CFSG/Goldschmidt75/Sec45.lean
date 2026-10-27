module

public import CFSG.Goldschmidt75.Sig31Main

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

omit [Finite G] in
theorem normalizer_zpowers_eq {s : G} (hs : orderOf s = 2) :
    normalizer ((zpowers s : Subgroup G) : Set G) = centralizer ({s} : Set G) := by
  apply le_antisymm
  · intro g hg
    rw [mem_centralizer_singleton_iff]
    have h1 := (mem_normalizer_iff.mp hg s).mp (mem_zpowers s)
    rcases eq_one_or_eq_of_mem_zpowers hs h1 with h2 | h2
    · exfalso
      have h3 : s = g⁻¹ * (g * s * g⁻¹) * g := by group
      rw [h2] at h3
      exact ne_one_of_orderOf_eq_two hs (by rw [h3]; group)
    · calc g * s = g * s * g⁻¹ * g := by group
        _ = s * g := by rw [h2]
  · rw [← centralizer_zpowers_eq]
    exact centralizer_le_normalizer _

theorem mem_normalizer_of_unique {W : Subgroup G}
    (hW : ∀ B₁ B₂ : Subgroup G, B₁ ≤ S₁ → B₂ ≤ S₂ → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
      W ∈ NSet (B₁ ⊔ B₂) ∧ ∀ X ∈ NSet (B₁ ⊔ B₂), X ≤ W)
    {B₁ B₂ : Subgroup G} (hB₁ : B₁ ≤ S₁) (hB₂ : B₂ ≤ S₂) (hB₁1 : B₁ ≠ ⊥) (hB₂1 : B₂ ≠ ⊥) {g : G}
    (hg₁ : g ∈ normalizer (B₁ : Set G)) (hg₂ : g ∈ normalizer (B₂ : Set G)) :
    g ∈ normalizer (W : Set G) := by
  obtain ⟨hWN, hle⟩ := hW B₁ B₂ hB₁ hB₂ hB₁1 hB₂1
  have h1 := NSet_conjSub g hWN
  rw [conjSub_sup, conjSub_eq_of_mem_normalizer hg₁, conjSub_eq_of_mem_normalizer hg₂] at h1
  have hcard : Nat.card W ≤ Nat.card (conjSub g W) := by
    unfold conjSub
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  exact mem_normalizer_of_conjSub_eq (Subgroup.eq_of_le_of_card_ge (hle _ h1) hcard)

omit [Finite G] in
theorem zpowers_ne_bot {s : G} (hs : orderOf s = 2) : zpowers s ≠ ⊥ := fun h0 =>
  ne_one_of_orderOf_eq_two hs (by
    have := mem_zpowers s
    rwa [h0, mem_bot] at this)

end CFSG.Goldschmidt75
