module

public import CFSG.Certificates.Kernel.DceLoops
public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.Loop CFSG.KC.LL.Ly7 CFSG.KC.LyA.DceS CFSG.Certificates.DceLoop

@[expose] noncomputable def rval {G : Type*} [Group G] (x : ℕ → G) (e : ℕ) : G :=
  ((List.range (bits e 2 10)).map fun i => x (byte (Nat.shiftRight e 12) i)).prod

@[expose] def nOnly (TL VL NL e : ℕ) : Prop :=
  ∀ i < bits e 2 10, isN TL VL NL (byte (Nat.shiftRight e 12) i) = true

theorem runHdr_eq (HB : ℕ → ℕ) (LT TL VL NL : ℕ) (Cs : List ℕ) (S : ℕ) :
    runHdr HB LT TL VL NL Cs S = cntRun (fun k J => hdrOK HB LT TL VL NL k (bits J 0 43))
      (fun _ => 43) 255 8 Cs S := rfl

theorem runGom_eq (HB GB OB : ℕ → ℕ) (I0 nH : ℕ) (Cs : List ℕ) (S : ℕ) :
    runGom HB GB OB I0 nH Cs S = cntRun (fun k J => gomOK HB GB OB I0 nH k (bits J 0 30))
      (fun _ => 30) 65535 16 Cs S := rfl

theorem runT_eq (TB OB RR : ℕ → ℕ) (LT TL VL NL NR nT I0 : ℕ) (Cs : List ℕ) (S : ℕ) :
    runT TB OB RR LT TL VL NL NR nT I0 Cs S = cntRun
      (fun k J => tOK TB OB RR LT TL VL NL NR nT I0 k (bits J 0 59) (bits J 59 (tBits (bits J 0 59))))
      (fun J => Nat.add 59 (tBits (bits J 0 59))) 65535 16 Cs S := rfl

theorem runStab_eq (FB EB : ℕ → ℕ) (sh wd NF D SG : ℕ) (Cs : List ℕ) (S : ℕ) :
    runStab FB EB sh wd NF D SG Cs S = cntRun
      (fun k J => andB (Nat.blt (bits J 0 19) k)
        (Nat.beq (mat EB k) (mul7 (mat EB (bits J 0 19)) (stabGen FB sh wd NF D SG (bits J 19 5)))))
      (fun _ => 24) 65535 16 Cs S := rfl

theorem runSorted_eq (get : ℕ → ℕ) (qb m : ℕ) (Cs : List ℕ) (S : ℕ) :
    runSorted get qb m Cs S = sortRun get qb m Cs S := rfl

theorem runCover_eq (FB OB : ℕ → ℕ) (sh wd NF NO AL : ℕ) (Cs : List ℕ) (S : ℕ) :
    runCover FB OB sh wd NF NO AL Cs S =
      coverRun (fun D w x h => slotOK FB OB sh wd NF AL D w x h) NO AL Cs S := rfl

theorem sumOK_eq (AL MD ND NORD SUM : ℕ) : sumOK AL MD ND NORD SUM = sumG AL MD ND NORD SUM := rfl

theorem runFacts_eq (FB HB GB TB WD : ℕ → ℕ) (sh wd LT TL VL NL ND NO nH nT nW W Wi : ℕ)
    (Cs : List ℕ) (S : ℕ) :
    runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi Cs S =
      factsG (factG (recOK ND NO) (treeOK HB GB) (axiomOK HB nH)
        (fun i Jf R => walkOK FB HB GB TB WD sh wd LT TL VL NL ND nH nT nW W Wi i Jf R)
        (rec FB sh wd)) Cs S := rfl

theorem walkGo_eq (FB HB GB TB : ℕ → ℕ) (sh wd LT TL VL NL nT W Wi i Ri ft fd Wd n k J S : ℕ) :
    walkGo FB HB GB TB sh wd LT TL VL NL nT W Wi i Ri ft fd Wd n k J S =
      walkG (isN TL VL NL) (isUL TL VL) (fun S c => mkSt (sD S) (mul7 (sPi S) (let7 LT c)))
        (fun c R dir e S => stepL HB GB TB TL VL nT W Wi c R dir e S) (rec FB sh wd) bad
        i Ri ft fd Wd n k J S := rfl

end CFSG.Certificates.DS5

end
