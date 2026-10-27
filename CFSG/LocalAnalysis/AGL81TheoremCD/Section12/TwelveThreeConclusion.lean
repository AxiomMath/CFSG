module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

@[expose] def TwelveThreeAltTwo (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop :=
  CFSG.ABGLocalTools.IsPConstrained p ↥H ∧ IsSLType 3 (ZMod p) (KStarQuot p M H) ∧
    d ∣ p + 1 ∧ IsPSLType 2 (ZMod p) (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))

@[expose] def TwelveThreeAltThree (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop :=
  p = 3 ∧ IsSimpleOfOrder 17971200 ↥(kStar p M H) ∧ d = 13 ∧
    IsPSLType 3 (ZMod 3) (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))

@[expose] def TwelveThreeAltFour (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop :=
  p = 5 ∧
    ((IsSimpleOfOrder 44352000 ↥(kStar p M H) ∧ d = 7 ∧
        IsSimpleOfOrder 126000 (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))) ∨
      (IsSimpleOfOrder 51765179004000000 ↥(kStar p M H) ∧ d = 31 ∧
        IsSimpleOfOrder 5859000000 (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))))

@[expose] def TwelveThreeAltFive (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop :=
  p = 7 ∧
    ((IsSimpleOfOrder 460815505920 ↥(kStar p M H) ∧ d = 19 ∧
        IsPSLType 3 (ZMod 7) (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))) ∨
      (IsSimpleOfOrder 1255205709190661721292800 ↥(kStar p M H) ∧ d = 17 ∧
        IsSimpleOfOrder 4030387200 (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))))

@[expose] def TwelveThreeAltSix (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop :=
  IsPSLType 3 (ZMod p) ↥(kStar p M H) ∧ d ∣ p + 1 ∧
    IsPSLType 2 (ZMod p) (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
