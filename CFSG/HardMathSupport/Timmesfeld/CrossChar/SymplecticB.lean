module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticFamily
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def regimeBSp (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .B r q ∧ (r = 2 ∨ q.p = 2) ∧
    ¬ (p = 3 ∧ q.card = 2)

theorem crossCharFamAt_B_symplectic : CrossCharFamAt .B regimeBSp := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨r, q, hd, hsp, h32⟩
  change d = _ at hd
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)
  have hK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField
      (⟨.B r q, hv⟩ : TauCeti.ValidLieTypeIndex)) = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have h32' : ¬ (p = 3 ∧ q.p ^ q.exponent = 2) := by rwa [← hcard]
  by_cases hr2 : r = 2
  · subst hr2
    have hrq : ¬ (2 = 2 ∧ q.p ^ q.exponent = 2) := by rw [← hcard]; exact hrange.2
    exact IsLocallyBalancedAbs.of_mulEquiv
      (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      (isLocallyBalancedAbs_psp_of_odd q.prime_p q.exponent_pos hK le_rfl hrq hp hp2 hpq h32')
  · have hq2 : q.p = 2 := hsp.resolve_left hr2
    have hr3 : 3 ≤ r := by have := hrange.1; omega
    exact IsLocallyBalancedAbs.of_mulEquiv
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      (isLocallyBalancedAbs_psp_of_odd q.prime_p q.exponent_pos hK (by omega) (by omega) hp hp2
        hpq h32')

end CFSG.HardMathSupport.Timmesfeld.CrossChar
