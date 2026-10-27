module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineFiveFamilies

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType oPPrimeHull)
open CFSG.LocalAnalysis.AGL81I.Section3 (ThreeNineHyp)

@[expose] def ThreeNineSocleCase {X : Type} [Group X] [Finite X] (K X₁ : Subgroup X)
    (p d : ℕ) : Prop :=
  (p = 3 ∧ d = 13 ∧ ReeTitsModel ↥K .Tits 2 1 ∧
      IsPSLType 3 (ZMod 3) (oPrimeModPrimeComplement d X₁)) ∨
    (p = 5 ∧ d = 7 ∧ IsSporadic ↥K .HS ∧
      CFSG.Open.StatedClassicalModel (oPrimeModPrimeComplement d X₁) .PSU 3 5 1) ∨
    (p = 5 ∧ d = 31 ∧ IsSporadic ↥K .Ly ∧
      ChevalleyExceptionalModel (oPrimeModPrimeComplement d X₁) .G2 5 1) ∨
    (p = 7 ∧ d = 19 ∧ IsSporadic ↥K .ONan ∧
      IsPSLType 3 (ZMod 7) (oPrimeModPrimeComplement d X₁)) ∨
    (p = 7 ∧ d = 17 ∧ IsSporadic ↥K .Fi24Prime ∧
      IsSporadic (oPrimeModPrimeComplement d X₁) .He)

@[expose] def KFactThreeNineSocle : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (p d : ℕ),
    ThreeNineHyp K E D X₁ p d → D ≤ K → ThreeNineSocleCase K X₁ p d →
      IsSimpleGroup ↥(oPPrimeHull d X₁) ∧
        Subgroup.centralizer (oPPrimeHull d X₁ : Set X) ⊓ K = ⊥

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
