module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def OverGood {G : Type*} [Group G] (R X₀ : Subgroup G) : Prop :=
  ∃ U : Subgroup G, U ≤ X₀ ∧ X₀ ≤ Subgroup.normalizer (U : Set G) ∧ ⁅U, U⁆ = U ∧ R ≤ U ∧
    (∀ W : Subgroup G, W ≤ U → U ≤ Subgroup.normalizer (W : Set G) → W = ⊥ ∨ W = U) ∧
    (∀ W : Subgroup G, W ≤ X₀ → ⁅W, W⁆ = W → W ≤ U) ∧ ¬ 5 ∣ Nat.card (Outer U) ∧
    ∃ E : Subgroup G, E ≤ U ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2

variable {G G' : Type*} [Group G] [Group G']

theorem OverGood.comap_of_injective {R X₀ : Subgroup G'} (h : OverGood R X₀) (φ : G →* G')
    (hφ : Function.Injective φ) (hX₀ : X₀ ≤ φ.range) :
    OverGood (R.comap φ) (X₀.comap φ) := by
  obtain ⟨U, hUX, hXN, hUU, hRU, hUs, hUp, hUo, E, hEU, hE, hEc⟩ := h
  have hUr : U ≤ φ.range := hUX.trans hX₀
  have hmapU : (U.comap φ).map φ = U := Subgroup.map_comap_eq_self hUr
  refine ⟨U.comap φ, Subgroup.comap_mono hUX, ?_, ?_, Subgroup.comap_mono hRU, ?_, ?_, ?_, ?_⟩
  ·
    rw [← Subgroup.comap_normalizer_eq_of_le_range hUr]
    exact Subgroup.comap_mono hXN
  ·
    apply Subgroup.map_injective hφ
    rw [Subgroup.map_commutator, hmapU, hUU]
  ·
    intro W hWU hUW
    have h1 : W.map φ ≤ U := by
      rw [← hmapU]
      exact Subgroup.map_mono hWU
    have h2 : U ≤ Subgroup.normalizer ((W.map φ : Subgroup G') : Set G') := by
      rw [← hmapU]
      exact (Subgroup.map_mono hUW).trans (Subgroup.le_normalizer_map φ)
    rcases hUs _ h1 h2 with h3 | h3
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective W hφ).mp h3
    · right
      apply Subgroup.map_injective hφ
      rw [h3, hmapU]
  ·
    intro W hWX hWW
    rw [← Subgroup.map_le_iff_le_comap]
    refine hUp _ ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact hWX
    · rw [← Subgroup.map_commutator, hWW]
  ·
    have e : ↥(U.comap φ) ≃* ↥U :=
      (Subgroup.equivMapOfInjective (U.comap φ) φ hφ).trans (MulEquiv.subgroupCongr hmapU)
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact hUo
  ·
    have hEr : E ≤ φ.range := hEU.trans hUr
    have hmapE : (E.comap φ).map φ = E := Subgroup.map_comap_eq_self hEr
    have eE : ↥(E.comap φ) ≃* ↥E :=
      (Subgroup.equivMapOfInjective (E.comap φ) φ hφ).trans (MulEquiv.subgroupCongr hmapE)
    refine ⟨E.comap φ, Subgroup.comap_mono hEU, ⟨?_, ?_⟩, ?_⟩
    · have hcomm := hE.1
      rw [isMulCommutative_iff] at hcomm ⊢
      intro a b
      apply eE.injective
      rw [map_mul, map_mul]
      exact hcomm (eE a) (eE b)
    · intro x hx
      apply hφ
      rw [map_pow, map_one]
      exact hE.2 (φ x) hx
    · rw [Nat.card_congr eE.toEquiv]
      exact hEc

theorem OverGood.map_equiv {R X₀ : Subgroup G} (h : OverGood R X₀) (φ : G ≃* G') :
    OverGood (R.map φ.toMonoidHom) (X₀.map φ.toMonoidHom) := by
  have h' := h.comap_of_injective φ.symm.toMonoidHom φ.symm.injective (by
    rw [MonoidHom.range_eq_top.mpr φ.symm.surjective]
    exact le_top)
  rwa [← Subgroup.map_equiv_eq_comap_symm', ← Subgroup.map_equiv_eq_comap_symm'] at h'

theorem exists_conj_eq_of_card_eq [Finite G] {p : ℕ} [Fact p.Prime] {H P₁ P₂ : Subgroup G}
    (h₁ : P₁ ≤ H) (h₂ : P₂ ≤ H) (hc₁ : Nat.card P₁ = p ^ (Nat.card H).factorization p)
    (hc₂ : Nat.card P₂ = p ^ (Nat.card H).factorization p) :
    ∃ c ∈ H, P₁ = P₂.map (MulAut.conj c).toMonoidHom := by
  let S₁ : Sylow p H := Sylow.ofCard (P₁.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv, hc₁])
  let S₂ : Sylow p H := Sylow.ofCard (P₂.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv, hc₂])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S₂ S₁
  refine ⟨g, g.2, ?_⟩
  have h1 : (S₁ : Subgroup H) = (P₂.subgroupOf H).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  have h2 : (P₁.subgroupOf H) = (P₂.subgroupOf H).map (MulAut.conj g).toMonoidHom := h1
  calc P₁ = (P₁.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le h₁).symm
    _ = ((P₂.subgroupOf H).map (MulAut.conj g).toMonoidHom).map H.subtype := by rw [h2]
    _ = ((P₂.subgroupOf H).map H.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    _ = P₂.map (MulAut.conj (g : G)).toMonoidHom := by
      rw [Subgroup.map_subgroupOf_eq_of_le h₂]

end CFSG.AGLEmbeddingD2
