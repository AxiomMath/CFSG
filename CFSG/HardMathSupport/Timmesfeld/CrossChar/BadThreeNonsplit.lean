module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSplitTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley

@[expose] def F4ThreeInnerNonsplit :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.F4 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.F4 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.F4 K)), innerAut (adjointGroup Tag.F4 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.F4 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def E7ThreeInnerNonsplit :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E7 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.E7 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E7 K)), innerAut (adjointGroup Tag.E7 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E7 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def E8ThreeInnerNonsplit :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E8 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ innerAut (adjointGroup Tag.E8 K) → ¬ HasSplitToralPlane 3 D →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E8 K)), innerAut (adjointGroup Tag.E8 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E8 K))) →
          localDeltaIn 3 H D = ⊥

section Reductions


theorem f4InnerResidualThree_of_nonsplit (h : F4ThreeInnerNonsplit) : F4InnerResidualThree := by
  intro K _ _ h3 D hD hcard hDin _ H hH hDH
  by_cases hs : HasSplitToralPlane 3 D
  · exact localDeltaIn_eq_bot_of_hasSplitToralPlane Nat.prime_three (by norm_num) hs hH
  · exact h K h3 D hD hcard hDin hs H hH hDH

end Reductions

section Families


theorem crossCharInnerAt_E7_three_of_nonsplit (h : E7ThreeInnerNonsplit) :
    CrossCharInnerAt .E7 fun _ p => p = 3 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc rfl
  obtain ⟨q, hq⟩ : ∃ q, d = TauCeti.LieTypeIndex.E7 q := hk
  subst hq
  have hℓ3 : q.p ≠ 3 := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  intro D hD hcard hDin H hH hDH
  by_cases hs : HasSplitToralPlane 3 D
  · exact localDeltaIn_eq_bot_of_hasSplitToralPlane Nat.prime_three (by norm_num) hs hH
  · exact h q.p q.exponent q.prime_p hℓ3 q.exponent_pos K hK' D hD hcard hDin hs H hH hDH

theorem crossCharInnerAt_E8_three_of_nonsplit (h : E8ThreeInnerNonsplit) :
    CrossCharInnerAt .E8 fun _ p => p = 3 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc rfl
  obtain ⟨q, hq⟩ : ∃ q, d = TauCeti.LieTypeIndex.E8 q := hk
  subst hq
  have hℓ3 : q.p ≠ 3 := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  intro D hD hcard hDin H hH hDH
  by_cases hs : HasSplitToralPlane 3 D
  · exact localDeltaIn_eq_bot_of_hasSplitToralPlane Nat.prime_three (by norm_num) hs hH
  · exact h q.p q.exponent q.prime_p hℓ3 q.exponent_pos K hK' D hD hcard hDin hs H hH hDH

end Families

end CFSG.HardMathSupport.Timmesfeld.CrossChar
