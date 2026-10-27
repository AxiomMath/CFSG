module

public import Certificates.Data.Kernel.GMS78RuCzJ
public import CFSG.Certificates.Kernel.GMS78RuGenCzJ
import CFSG.Certificates.Kernel.GMS78RuCzJTable
import CFSG.Certificates.Kernel.GMS78RuCzJRigid
import CFSG.Certificates.Kernel.GMS78RuCzJIdent

public section

namespace CFSG.KC.GMS

open CFSG.ComponentClassification.GMS78.RuCz CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.KLie.CT

theorem czJ_sound (gs : Array (Array ℕ)) (GS : List Nat) (cP : CFSG.KC.Census.ArrCertP)
    (PT RW LK : Nat → Nat) (PAR LAB INV KQ KW : Nat) (FIX D3 D5 CT SOLS : List Nat)
    (relsJ rels1 rels3 rels5 Wq Wv Ww normX hCodes c2J HT HR : List (List ℕ))
    (sols : List (List (List ℕ))) (cls : List ℕ)
    (hgs : gs = (GS.map czUnpack).toArray)
    (hr1 : rels1 = relsJ.filter fun r => r.all fun l => l < 4)
    (hr3 : rels3 = relsJ.filter fun r => (r.all fun l => l < 8) && !(r.all fun l => l < 4))
    (hr5 : rels5 = relsJ.filter fun r => !(r.all fun l => l < 8))
    (hHT : HT = (List.range 6).map fun i => invCodes ((hCodes.getD i []).drop 3))
    (hHR : HR = hCodes.drop 7)
    (hP : kPoints GS PT cP = true) (hPt : ∀ i < 2048, kPointAt GS PT LK PAR LAB i = true)
    (hK : kKeys PT = true) (hC : kCols cP LK = true)
    (hPL : kParLab cP PAR LAB = true) (hR : ∀ a < 2048, kRow LK RW PAR LAB a = true)
    (hI : ∀ a < 2048, kInv RW INV a = true)
    (hPrep : kPrep RW PAR LAB INV ((List.range 6).map fun k => fget (LK k) 0 11) Wq Ww sols KQ KW
      FIX D3 D5 CT SOLS = true)
    (hS : ∀ j < 512, kSearch RW PAR LAB INV ((List.range 6).map fun k => fget (LK k) 0 11) rels1
      rels3 rels5 KQ KW FIX D3 D5 CT SOLS j = true)
    (hId : kIdent RW PAR LAB INV ((List.range 6).map fun k => fget (LK k) 0 11) relsJ Wq Wv Ww
      normX c2J HT HR sols cls = true) :
    (fun c : ArrCert => (fun M => (fun inv gi =>
      enumOK 128 gs [0, 5, 3] c = true ∧ tableOK 2048 c M inv gi = true ∧
        relsHold M inv relsJ gi = true ∧
        Gen.rigidSearchG relsJ Wq Ww sols 2048 M inv c gi = true ∧
        Gen.identSearchG relsJ Wq Wv Ww sols normX hCodes c2J cls 2048 M inv c gi = true)
      (invOf 2048 M) ((List.range 6).map (gIdx c))) (tabOf 2048 c 6))
      ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩ := by
  subst hgs
  have H : CzJ.TabHyps GS cP PT RW LK PAR LAB INV := ⟨hP, hPt, hK, hC, hPL, hR, hI⟩
  have I := CzJ.czJ_tabI H
  have hgi := CzJ.czJ_gIdx H
  exact ⟨CzJ.czJ_enumOK H, CzJ.czJ_tableOK H, CzJ.czJ_relsHold I hgi hId,
    CzJ.czJ_rigid I hgi hr1 hr3 hr5 hPrep hS, CzJ.czJ_ident I hgi hHT hHR hId⟩

end CFSG.KC.GMS

end
