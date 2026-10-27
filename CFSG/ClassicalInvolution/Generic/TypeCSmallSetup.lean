module

import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem oddLieType_of_lieSystem {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    {Ω : Set (Subgroup F)} (hp2 : p ≠ 2) (hnab : ∃ a b : F, a * b ≠ b * a)
    (h : LieSystem p f F Ω) : CFSG.Blueprint.OddLieType F := by
  obtain ⟨D⟩ := h
  obtain ⟨t, n, e, hp, ψ, hsurj, hker, hFT, hadm, -⟩ := D.exists_model_of_simple hnab
  obtain ⟨-, hmodel⟩ := ModelFacts.modelClauseZero t n p e hp hFT hadm
  let eF : (modelUniv t n p e hp).K ⧸ Subgroup.center (modelUniv t n p e hp).K ≃* F :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)
  exact ⟨t, n, p, e, hp, hp2, hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eF hmodel⟩

@[expose] def SmallTypeCSetup (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G → CFSG.ClassicalInvolution.DeltaConnected K →
      ¬ BootData p f (conjClass K) → ¬ A2Configuration z K →
      ExactMembers (conjClass K) ∧ LocalOddCentral (conjClass K) {z}

theorem smallTypeC_of_setup (hs : SmallTypeCSetup p f)
    (hshape : ∀ (a : ℕ) (t : StatedLieTag) (n : ℕ), ShapePiece p f a t n)
    (hmulti : MultiPiece p f) : SmallTypeC p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
  obtain ⟨hex, hp1⟩ := hs G hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
  have S : RouteDSetup p f K z :=
    mk_routeDSetup hp2 hq hz hBelow ((deltaConnected_iff K).mp hΔ) hex hp1
  refine Or.inl (oddLieType_of_lieSystem (f := f) (Ω := conjClass K) hp2 hnab ?_)
  rcases exists_shape_or_multi S.ih (mem_conjClass_self K) hz
    (singleton_not_subset_center hnab hz.ne_one) with ⟨a, t, n, hsh⟩ | hm
  · exact hshape a t n G hnab K z S hsh
  · exact hmulti G hnab K z S hm

end CFSG.ClassicalInvolution.Generic.CoreAssembly
