module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangSeven
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwVacuity
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeGraphProof
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsAll
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_adjointE8_three_large (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) (h2 : Nat.card K ≠ 2) (h4 : Nat.card K ≠ 4) :
    InnerPlaneBalance 3 (adjointGroup Tag.E8 K) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  exact steinbergLang_innerPlaneBalance_of_toralPlane Nat.prime_three
    langToralPlane_E8_three
    (steinbergLang_langTorusPlaneBalance_E8_three hsub hin hsu htw hex) K h3 ⟨h3, h2, h4⟩

theorem innerPlaneBalance_adjointE7_three_large (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) (h2 : Nat.card K ≠ 2) :
    InnerPlaneBalance 3 (adjointGroup Tag.E7 K) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  exact steinbergLang_innerPlaneBalance_of_toralPlane Nat.prime_three
    langToralPlane_E7_three
    (steinbergLang_langTorusPlaneBalance_E7_three hsub hin hsu htw hex) K h3 ⟨h3, h2⟩

theorem innerPlaneBalance_adjointF4_three_large (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) (h2 : Nat.card K ≠ 2) (h4 : Nat.card K ≠ 4) :
    InnerPlaneBalance 3 (adjointGroup Tag.F4 K) := by
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  have hF4T13 := langTorusPlaneBalance_F4_three_of_ne hsub hin hsu htw hex fun w _ _ => by
    intro K _ _ hQ
    rcases Nat.even_or_odd (Nat.card K) with he | ho
    · exact f4Three_langTorusPlaneBalance_even hsub hin hsu htw hex f4ThreeEvenGraphRigid_holds
        w K ⟨hQ, he⟩
    · exact f4Three_langTorusPlaneBalance_odd hsub hin hsu htw hex w K ⟨hQ, ho⟩
  exact steinbergLang_innerPlaneBalance_of_toralPlane Nat.prime_three
    langToralPlane_F4_three hF4T13 K h3 ⟨h3, h2, h4⟩

section Small


theorem innerPlaneBalance_adjointF4_three_small (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ∨ Nat.card K = 4) : InnerPlaneBalance 3 (adjointGroup Tag.F4 K) :=
  innerPlaneBalance_three_of_innerOneBalanceThree (innerOneBalanceThree_F4_small K hK)

theorem innerPlaneBalance_adjointE7_three_small (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : InnerPlaneBalance 3 (adjointGroup Tag.E7 K) :=
  innerPlaneBalance_three_of_innerOneBalanceThree (innerOneBalanceThree_E7_small K hK)

theorem innerPlaneBalance_adjointE8_three_small (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ∨ Nat.card K = 4) : InnerPlaneBalance 3 (adjointGroup Tag.E8 K) :=
  innerPlaneBalance_three_of_innerOneBalanceThree (innerOneBalanceThree_E8_small K hK)

theorem innerPlaneBalance_adjointE8_three (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) : InnerPlaneBalance 3 (adjointGroup Tag.E8 K) := by
  by_cases h : Nat.card K = 2 ∨ Nat.card K = 4
  · exact innerPlaneBalance_adjointE8_three_small K h
  · push Not at h
    exact innerPlaneBalance_adjointE8_three_large K h3 h.1 h.2

theorem innerPlaneBalance_adjointE7_three (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) : InnerPlaneBalance 3 (adjointGroup Tag.E7 K) := by
  by_cases h : Nat.card K = 2
  · exact innerPlaneBalance_adjointE7_three_small K h
  · exact innerPlaneBalance_adjointE7_three_large K h3 h

theorem innerPlaneBalance_adjointF4_three (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) : InnerPlaneBalance 3 (adjointGroup Tag.F4 K) := by
  by_cases h : Nat.card K = 2 ∨ Nat.card K = 4
  · exact innerPlaneBalance_adjointF4_three_small K h
  · push Not at h
    exact innerPlaneBalance_adjointF4_three_large K h3 h.1 h.2

end Small

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
