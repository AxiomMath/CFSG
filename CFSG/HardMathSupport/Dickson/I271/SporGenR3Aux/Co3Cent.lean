module

public import Certificates.Certificate17370
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3Three
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.HardMathSupport.Dickson.I271.Co3Cent
  CFSG.HardMathSupport.Dickson.I271.L28Presentation

section Perm


theorem caseB_spec :
    XB ^ 3 = 1 ∧ XB ≠ 1 ∧ XB ∈ co3P ∧ Nat.card (closure (permsA 276 (dGens ()))) = 243 ∧
      closure (permsA 276 (dGens ())) ≤ centralizer {XB} ⊓ co3P ∧
      (∀ g ∈ centralizer {XB} ⊓ co3P, ∀ r ∈ closure (permsA 276 (dGens ())),
        g * r * g⁻¹ ∈ closure (permsA 276 (dGens ()))) ∧
      centralizer (closure (permsA 276 (dGens ())) : Set (Equiv.Perm (Fin 276))) ⊓
        (centralizer {XB} ⊓ co3P) ≤ closure (permsA 276 (dGens ())) :=
  Certificates.certificate17370.1

theorem caseA_spec :
    XA ^ 3 = 1 ∧ XA ≠ 1 ∧ XA ∈ co3P ∧ Nat.card (closure (permsA 276 (rGens ()))) = 243 ∧
      closure (permsA 276 (rGens ())) ≤ centralizer {XA} ⊓ co3P ∧
      (∀ g ∈ centralizer {XA} ⊓ co3P, ∀ r ∈ closure (permsA 276 (rGens ())),
        g * r * g⁻¹ ∈ closure (permsA 276 (rGens ()))) ∧
      centralizer (closure (permsA 276 (rGens ())) : Set (Equiv.Perm (Fin 276))) ⊓
        (centralizer {XA} ⊓ co3P) ≤ closure (permsA 276 (rGens ())) :=
  Certificates.certificate17370.2.1

theorem caseC_spec :
    (closure (permsA 276 (cGens ())) = centralizer {yPerm} ⊓ co3P ∧
      Nat.card (closure (permsA 276 (cGens ()))) = 4536) ∧
    closure (permsA 276 (lGens ())) ≤ closure (permsA 276 (cGens ())) ∧
    ⁅closure (permsA 276 (cGens ())), closure (permsA 276 (cGens ()))⁆ ≤
      closure (permsA 276 (lGens ())) ∧
    Nat.card (closure (permsA 276 (lGens ()))) = 504 ∧
    ∀ w ∈ l28Words,
      CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW
        (fun i : Fin 2 => permOfArr 276 (lGens ())[i.val]!) w = 1 :=
  ⟨Cy_eq, Certificates.certificate17370.2.2⟩

end Perm

end CFSG.HardMathSupport.Dickson.I271
