module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

theorem isCentralProductOfSL2_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {K : Subgroup X}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (h : IsCentralProductOfSL2 K F₁ F₂) :
    IsCentralProductOfSL2 (K.map e.toMonoidHom) F₁ F₂ := by
  obtain ⟨A, B, hAB, hcomm, hcard, ⟨eA⟩, ⟨eB⟩⟩ := h
  refine ⟨A.map e.toMonoidHom, B.map e.toMonoidHom, ?_, ?_, ?_,
    ⟨(Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).symm.trans eA⟩,
    ⟨(Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).symm.trans eB⟩⟩
  · rw [← Subgroup.map_sup, hAB]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg e (hcomm a ha b hb)
  · rw [← Subgroup.map_inf_eq A B e.toMonoidHom e.injective,
      Subgroup.card_map_of_injective e.injective]
    exact hcard

theorem hasSL2ProductOfIndexTwoCh6_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {C₁ : Subgroup X} {q : ℕ} (h : HasSL2ProductOfIndexTwoCh6 C₁ q) :
    HasSL2ProductOfIndexTwoCh6 (C₁.map e.toMonoidHom) q := by
  obtain ⟨F, F₁, F₂, i1, i2, i3, i4, i5, i6, hF, h1, h2, h3, h4, h5, h6, K, hKC, hidx, hK⟩ := h
  refine ⟨F, F₁, F₂, i1, i2, i3, i4, i5, i6, hF, h1, h2, h3, h4, h5, h6, K.map e.toMonoidHom,
    Subgroup.map_mono hKC, ?_, isCentralProductOfSL2_map e hK⟩
  have := Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) K C₁ e.injective
  change (K.map e.toMonoidHom).relIndex (C₁.map e.toMonoidHom) = 2
  rw [this]
  exact hidx

theorem sylow_of_sylowTop {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) : ∃ P : Sylow 2 G, (P : Subgroup G) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.ABGLocalTools.isSylowOf_iff).1 hS
  have hidx : ¬ 2 ∣ S.index := by
    have := h.2.2
    rwa [Subgroup.relIndex_top_right] at this
  exact ⟨h.2.1.toSylow hidx, IsPGroup.toSylow_coe _ _⟩

end CFSG.GH74.GLS.Stage2.Final
