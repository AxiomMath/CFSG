module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Y
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Four

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open
open CFSG.LieType.ChevTwo (Chev2KDOut Chev2CoreCent OmegaTwoAutTwoPart OmegaTwoAutInduced
  OmegaPlusEightInvolutions OrthOddCentCore)

theorem input19_20_2_of_catalogue (hKD : Chev2KDOut) (hCore : Chev2CoreCent) : Input19_20_2 :=
  Prop95I1920.input19_20_2_of_kdout_corecent hKD hCore

theorem input19_20_3_of_catalogue (hKD : Chev2KDOut) (hCore : Chev2CoreCent)
    (h3 : Input19_20_3Core) : Input19_20_3 :=
  Prop95I1920.input19_20_3_of_kdout_corecent hKD hCore h3
    Prop95I1920.omegaFourComponentCentre_holds

theorem input19_20_3_of_leaves (hKD : Chev2KDOut) (hCore : Chev2CoreCent)
    (h1 : OmegaTwoAutTwoPart)
    (h2 : (∀ n : ℕ, 1 ≤ n → OmegaTwoAutInduced (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) ∧
      (∀ n : ℕ, 2 ≤ n → n ≠ 3 → OmegaTwoAutInduced (StatedQuadPlus (n + 1) (ZMod 2))))
    (h2' : OmegaPlusEightInvolutions)
    (h3 : ∀ n : ℕ, 1 ≤ n → OrthOddCentCore (StatedQuadPlus (n + 1) (ZMod 2)) true n ∧
      OrthOddCentCore (StatedQuadMinus (n + 1) (ZMod 2) 1 1) false n) : Input19_20_3 :=
  input19_20_3_of_catalogue hKD hCore (input19_20_3Core_of h1 h2 h2' h3)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
