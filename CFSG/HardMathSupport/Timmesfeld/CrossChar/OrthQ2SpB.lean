module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2SpFamily
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3ResidualQ

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem isLocallyBalancedAbs_psp_three_two {r : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2)
    (hr : 3 ≤ r) : IsLocallyBalancedAbs 3 3 (StatedProj (StatedSp r K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  intro D hD hcard H hH _
  exact localDeltaIn_eq_bot_psp_three_two hK hr hD hcard hH

@[expose] def regimeBThreeTwo (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧ q.card = 2

theorem crossCharFamAt_B_threeTwo : CrossCharFamAt .B regimeBThreeTwo := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨rfl, r, q, hd, hq2⟩
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = 2 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simpa [TauCeti.ValidLieTypeIndex.fieldOrder] using hq2
  have hqp : q.p = 2 := primePower_p_eq_two_of_card_eq_two hq2
  have hr3 : 3 ≤ r := by
    have h1 := hrange.1
    have h2 := hrange.2
    by_contra hlt
    have : r = 2 := by omega
    exact h2 ⟨this, hq2⟩
  exact IsLocallyBalancedAbs.of_mulEquiv
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hqp hr3)
    (isLocallyBalancedAbs_psp_three_two hK hr3)

theorem crossCharFamCat_B : CrossCharFamCat .B :=
  crossCharFamCat_of_at regimeBAll4 crossCharFamAt_B_all4
    (crossCharFamAt_not_regimeBAll4_iff.2 crossCharFamAt_B_threeTwo)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
