module

public import Certificates.Data.Kernel.CoreD2K.Check
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KD.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CoreD2K Certificates.CoreD2Perm

theorem gensK_perm {n w : Nat} {V : VData} {GP GPI EG GT GTI : Nat → Nat}
    (h : gensK n w V GP GPI EG GT GTI = true) :
    allN (nat_lit 2) (fun j => permOK n w (mask w) (Nat.mul n w) (GP j) (GPI j)) = true := by
  unfold gensK at h
  exact ((bAnd_iff _ _).1 h).1

theorem gensK_of {n w : Nat} {V : VData} {GP GPI EG GT GTI : Nat → Nat}
    (h2 : allN (nat_lit 2) (fun j => permOK n w (mask w) (Nat.mul n w) (GP j) (GPI j)) = true)
    (hE : ∀ k < V.base.eW.length, bAnd(wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2)
      (V.base.eW.getD k []) (EG k), canonK n w (mask w) (Nat.mul n w) (EG k)) = true)
    (hG : ∀ j < V.base.gWs.length, bAnd(wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2)
      (V.base.gWs.getD j []) (GT j), permOK n w (mask w) (Nat.mul n w) (GT j) (GTI j)) = true) :
    gensK n w V GP GPI EG GT GTI = true := by
  unfold gensK
  exact (bAnd_iff _ _).2 ⟨h2, (bAnd_iff _ _).2 ⟨PK.allN_iff.2 hE, PK.allN_iff.2 hG⟩⟩

theorem wordsK_of {n w : Nat} {V : VData} {GP GT GTI : Nat → Nat}
    (hA : V.wAs.length = V.ys.length) (hB : V.wBs.length = V.ys.length)
    (hw : ∀ i < V.ys.length,
      wordEqK n w (mask w) (pidn n w) GT GTI V.base.gWs.length (V.wAs.getD i [])
          (GP (nat_lit 0)) = true ∧
        wordEqK n w (mask w) (pidn n w) GT GTI V.base.gWs.length (V.wBs.getD i [])
          (GP (nat_lit 1)) = true)
    (hok : allN V.ys.length (fun i => bAnd(wordOK V i (V.wAs.getD i []),
      wordOK V i (V.wBs.getD i []))) = true) :
    wordsK n w V GP GT GTI = true := by
  unfold wordsK
  refine (bAnd_iff _ _).2 ⟨Nat.beq_eq.mpr hA, (bAnd_iff _ _).2 ⟨Nat.beq_eq.mpr hB,
    PK.allN_iff.2 fun i hi => (bAnd_iff _ _).2 ⟨(hw i hi).1, (bAnd_iff _ _).2 ⟨(hw i hi).2,
      ?_⟩⟩⟩⟩
  have h := PK.allN_iff.1 hok i hi
  exact (bAnd_iff _ _).1 h |>.elim fun h1 h2 => (bAnd_iff _ _).2 ⟨h1, h2⟩

end CFSG.KD.CoreD2K

end
