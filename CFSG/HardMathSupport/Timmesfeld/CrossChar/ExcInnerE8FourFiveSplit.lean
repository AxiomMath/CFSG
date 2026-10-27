module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveSmall
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ3

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


theorem langTorusPlaneBalance_or {τ : Tag} {w : WeylGroup τ} {p : ℕ} {Q₁ Q₂ : ℕ → Prop}
    (h₁ : LangTorusPlaneBalance τ w p Q₁) (h₂ : LangTorusPlaneBalance τ w p Q₂) :
    LangTorusPlaneBalance τ w p fun q => Q₁ q ∨ Q₂ q := by
  intro K _ _ hQ
  rcases hQ with h | h
  · exact h₁ K h
  · exact h₂ K h

theorem langTorusPlaneBalance_E8_four_five_three (hcp : LangComponentPieces) :
    LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => q = 3 :=
  langTorusPlaneBalance_of_setupRigidAt (Or.inr (Or.inr (Or.inr rfl)))
    (fun K _ _ => commutator_adjointGroup_E8_eq_top K) e8PhiFourWeyl Nat.prime_five
    (fun q _ hQ => ⟨by rw [hQ]; norm_num, Or.inl le_rfl⟩)
    (fun K _ _ Fr hFr g0 hg0C hg0 S hSD hQK =>
      setupRigidAtFrobenius_E8_four_five_three anyKindCommuteThreeFull_holds K Fr hFr g0 hg0C hg0
        S hSD hQK)
    hcp.subnormal hcp.inner hcp.suN hcp.twoD hcp.exc

theorem langTorusPlaneBalance_E8_four_five_small_of_two' (hcp : LangComponentPieces)
    (h2 : LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => q = 2) :
    LangTorusPlaneBalance Tag.E8 e8PhiFourWeyl 5 fun q => q = 2 ∨ q = 3 :=
  langTorusPlaneBalance_or h2 (langTorusPlaneBalance_E8_four_five_three hcp)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
