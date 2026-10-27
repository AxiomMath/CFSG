module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6Three
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSplitTorus

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley

@[expose] def E6ThreeInnerNonsplit :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.E6 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def E6ThreeDiagonalNonsplit :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → 3 ∣ ℓ ^ f - 1 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ e6Inndiag K → ¬ D ≤ innerAut (adjointGroup Tag.E6 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
          localDeltaIn 3 H D = ⊥

section Reductions


theorem e6ThreeDiagonal_of_nonsplit (h : E6ThreeDiagonalNonsplit) : E6ThreeDiagonal := by
  intro ℓ f hℓ hℓ3 hf h3 K _ _ hK D hD hcard hDd hDin H hH hDH
  by_cases hs : HasSplitToralPlane 3 D
  · exact localDeltaIn_eq_bot_of_hasSplitToralPlane Nat.prime_three (by norm_num) hs hH
  · exact h ℓ f hℓ hℓ3 hf h3 K hK D hD hcard hDd hDin hs H hH hDH

end Reductions

section Family


theorem crossCharInnerAt_E6_three_of_nonsplit (h : E6ThreeInnerNonsplit) :
    CrossCharInnerAt .E6 fun _ p => p = 3 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc rfl
  obtain ⟨q, hq⟩ : ∃ q, d = TauCeti.LieTypeIndex.E6 q := hk
  subst hq
  have hℓ3 : q.p ≠ 3 := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  intro D hD hcard hDin H hH hDH
  by_cases hs : HasSplitToralPlane 3 D
  · exact localDeltaIn_eq_bot_of_hasSplitToralPlane Nat.prime_three (by norm_num) hs hH
  · exact h q.p q.exponent q.prime_p hℓ3 q.exponent_pos K hK' D hD hcard hDin hs H hH hDH

theorem crossCharFamAt_E6_three_of_nonsplit (hin : E6ThreeInnerNonsplit)
    (hdiag : E6ThreeDiagonalNonsplit) : CrossCharFamAt .E6 fun _ p => p = 3 :=
  crossCharFamAt_E6_three_of (crossCharInnerAt_E6_three_of_nonsplit hin)
    (e6ThreeDiagonal_of_nonsplit hdiag)

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
