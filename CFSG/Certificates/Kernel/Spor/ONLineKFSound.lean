module

public import Certificates.Data.Kernel.Spor.ONLineKF
public import CFSG.Certificates.Kernel.Spor.ONKFSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.ONF

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

theorem allBlk_mono' {f g : Nat → Bool} (hfg : ∀ i, f i = true → g i = true) (b : Nat) :
    ∀ len, allBlk b f len = true → allBlk b g len = true
  | 0, _ => rfl
  | len + 1, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    change Bool.rec (motive := fun _ => Bool) false (allBlk b g len) (g (Nat.add b len)) = true
    exact (bAnd_iff _ _).2 ⟨hfg _ h1, allBlk_mono' hfg b len h2⟩

theorem lineRangeF_imp {KL LP TA TB AL BL : Nat → Nat} {CA CB : List (List Nat)}
    {LA LB : List Nat} {cnt n lo len : Nat}
    (htA : tabChk TA CA 0 = true) (hlA : lensOK CA = true) (hcA : colsOK LA = true)
    (hfA : (CA.flatten == LA) = true) (hnA : CA.length = cnt)
    (htB : tabChk TB CB 0 = true) (hlB : lensOK CB = true) (hcB : colsOK LB = true)
    (hfB : (CB.flatten == LB) = true) (hnB : CB.length = cnt)
    (h : lineRangeF KL LP TA TB cnt AL BL n lo len = true) :
    lineRange KL LP LA LB AL BL n lo len = true := by
  refine allBlk_mono' (fun i hi => ?_) lo len h
  have e : lineAtF KL LP TA TB cnt AL BL n i = lineAt KL LP LA LB AL BL n i := by
    simp only [lineAtF, lineAt, mvF_eq htA hlA hcA hfA hnA, mvF_eq htB hlB hcB hfB hnB]
  rwa [← e]

end CFSG.KS.ONF

end
