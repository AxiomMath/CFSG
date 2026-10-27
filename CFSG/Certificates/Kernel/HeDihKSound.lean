module

public import Certificates.Data.Kernel.HeDihK
public import Certificates.Data.K426Checks
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack

public section

namespace CFSG.KC.HeDih

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.KFacts.K426

variable {n w : Nat} (hw : szOK n w = true)
include hw

theorem evalWA_unpack {m : Nat} {gs : Array (Array Nat)} {G : Nat → Nat}
    (hg : ∀ k < m, gs[k]! = unpack n w (G k)) (hp : ∀ k < m, PP n w (G k)) :
    ∀ wd : List (Fin m × Bool),
      evalWA n gs wd = unpack n w (evalWK n w G wd) ∧ PP n w (evalWK n w G wd)
  | [] => ⟨idA_eq hw, PP.id hw⟩
  | x :: wd => by
    obtain ⟨h1, h2⟩ := evalWA_unpack hg hp wd
    have hx := hg x.1.val x.1.isLt
    have hpx := hp x.1.val x.1.isLt
    have e : evalWK n w G (x :: wd) = pcomp n w (mask w)
        (Bool.rec (motive := fun _ => Nat) (pinvS n w (mask w) (G x.1.val)) (G x.1.val) x.2)
        (evalWK n w G wd) := rfl
    rw [evalWA, e, h1, hx]
    cases x.2
    · exact ⟨by rw [if_neg Bool.false_ne_true, invCand_PP hpx, compA_PP hpx.inv h2], hpx.inv.mul h2⟩
    · exact ⟨by rw [if_pos rfl, compA_PP hpx h2], hpx.mul h2⟩

omit hw in
theorem dihWK_eq {m : Nat} (G : Nat → Nat) (wr ws : List (Fin m × Bool)) :
    dihWK n w G wr ws = dihK n w (evalWK n w G wr) (evalWK n w G ws) := by
  unfold dihWK strictB
  cases evalWK n w G wr <;> cases evalWK n w G ws <;> rfl

theorem pow_unpack {r : Nat} (hr : PP n w r) (e : Nat) :
    CFSG.Monster.B.Mathieu.powArr n (unpack n w r) e = unpack n w (powK n w r e) :=
  CFSG.KC.Misc.ArrEnum.pow_unpack' hw (CFSG.KC.Misc.ArrEnum.permB_of_pp hr) e

theorem pp_powK {r : Nat} (hr : PP n w r) (e : Nat) : PP n w (powK n w r e) :=
  CFSG.KC.Misc.ArrEnum.pp_ppow hw hr e

theorem eqA_pow {r s : Nat} (hr : PP n w r) (hs : PP n w s) (e : Nat) :
    eqA n (unpack n w s) (CFSG.Monster.B.Mathieu.powArr n (unpack n w r) e) =
      Nat.beq s (powK n w r e) := by
  rw [pow_unpack hw hr]
  exact eqA_PP hs (pp_powK hw hr e)

end CFSG.KC.HeDih

end
