module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Three

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools

@[expose] def N1PCfg (p : ℕ) {G : Type*} [Group G] (I : Subgroup G) : Prop :=
  ∃ P W : Subgroup G, IsSylowOf 2 P I ∧ IsPGroup p ↥W ∧ W ≠ ⊥ ∧ P ≤ normalizer (W : Set G)

theorem pCfg_map {p : ℕ} {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (Θ : G ≃* G') {I : Subgroup G} (h : N1PCfg p I) : N1PCfg p (I.map Θ.toMonoidHom) := by
  obtain ⟨P, W, hP, hWp, hWne, hPW⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨P.map Θ.toMonoidHom, W.map Θ.toMonoidHom,
    (isSylowOf_map_iff Θ.toMonoidHom Θ.injective).2 hP, ?_, ?_, ?_⟩
  · exact hWp.of_equiv (W.equivMapOfInjective Θ.toMonoidHom Θ.injective)
  · intro hb
    exact hWne ((Subgroup.map_eq_bot_iff_of_injective W Θ.injective).1 hb)
  · exact (Subgroup.map_mono hPW).trans (Subgroup.le_normalizer_map Θ.toMonoidHom)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
