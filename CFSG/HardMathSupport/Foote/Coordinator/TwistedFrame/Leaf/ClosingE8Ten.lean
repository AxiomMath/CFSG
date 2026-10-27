module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux16
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux18
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux25
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux29
public import Certificates.Certificate81002

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem e8Ten_opp_case1 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) (H : Subgroup (ModGL Tag.E8 K))
    (hHG : H ≤ adjointGroup Tag.E8 K) (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    (v : ModGL Tag.E8 K) (hvQ : v ∈ Qθ Tag.E8 K)
    (hvB : conjSub v (Heis.Uneg Tag.E8 K) ≤ H)
    (hvM : ∀ β, CoordsAux.κ D v β ≠ 0 → β ∈ DetectE8.mRoots)
    (hY1 : ∃ β, CoordsAux.κ D v β ≠ 0 ∧
      (E8TenAux.cls β = 2 ∨ E8TenAux.cls β = 3)) :
    ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  have h2 : TwClass.e8Ten.minQ ≤ Nat.card K := by
    have : TwClass.e8Ten.minQ = 2 := rfl
    omega
  exact E8TenAux.case1_main D hK hHG (twBasic TwClass.e8Ten K h2 D) hXH hvQ hvB hvM hY1


theorem e8TenTwo_check : E8TenTwo.e8TenTwoCheck () = true :=
  Certificates.certificate81002

theorem e8Ten_opp_case2 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) (H : Subgroup (ModGL Tag.E8 K))
    (hHG : H ≤ adjointGroup Tag.E8 K) (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    (v : ModGL Tag.E8 K) (hvQ : v ∈ Qθ Tag.E8 K)
    (hvB : conjSub v (Heis.Uneg Tag.E8 K) ≤ H)
    (hvM : ∀ β, CoordsAux.κ D v β ≠ 0 →
      β ∈ DetectE8.mRoots ∧ (E8TenAux.cls β = 1 ∨ E8TenAux.cls β = 4))
    (hne : ∃ β, CoordsAux.κ D v β ≠ 0) :
    ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  have h2 : TwClass.e8Ten.minQ ≤ Nat.card K := by
    have : TwClass.e8Ten.minQ = 2 := rfl
    omega
  exact E8TenAux.case2_main D e8TenTwo_check hK (twBasic TwClass.e8Ten K h2 D) hXH hvQ hvB hvM hne

theorem e8Ten_opposite_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) (H : Subgroup (ModGL Tag.E8 K))
    (hHG : H ≤ adjointGroup Tag.E8 K) (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K)
    (hBH : conjSub q (Heis.Uneg Tag.E8 K) ≤ H)
    (hBX : ¬ conjSub q (Heis.Uneg Tag.E8 K) ≤ TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) :
    ∃ m ∈ H, m ∈ Qθ Tag.E8 K ∧
      heisCoord Tag.E8 K m ∉ VS (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  have h2 : TwClass.e8Ten.minQ ≤ Nat.card K := by
    have : TwClass.e8Ten.minQ = 2 := rfl
    omega
  have hb := twBasic TwClass.e8Ten K h2 D
  exact E8TenAux.opposite_two_of_cases D hb hXH hq hBH hBX
    (fun v hvQ hvB hvM hY1 => e8Ten_opp_case1 K hK D H hHG hXH v hvQ hvB hvM hY1)
    (fun v hvQ hvB hvM hne => e8Ten_opp_case2 K hK D H hHG hXH v hvQ hvB hvM hne)

theorem twClosing_e8Ten (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) :
    TwFrameClosing TwClass.e8Ten.tag K (TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D) := by
  by_cases h3 : 3 ≤ Nat.card K
  · exact E8TenAux.twClosing_e8Ten_three K D h3
  · have hK : Nat.card K = 2 := by
      have : 2 ≤ Nat.card K := Finite.one_lt_card
      omega
    exact E8TenAux.twClosing_e8Ten_of_opp K D fun H hHG hXH q hq hBH hBX =>
      e8Ten_opposite_two K hK D H hHG hXH hq hBH hBX

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
