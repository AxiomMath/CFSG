module

public import CFSG.Certificates.Kernel.LyOmega.TreeSound
import CFSG.Certificates.Kernel.LyOmega.SoundCNode
import CFSG.Certificates.Kernel.LyOmega.SoundSpread
public import Certificates.Data.Kernel.LyOmega.Chart

public section

namespace CFSG.KS.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop

theorem bVld_sound {C : BConsts} (hC : bConstsOK C = true) {X : ℕ}
    (h : validM 5 9324 C.L7 C.H7 X = true) : LCanon 12 7 111 X := by
  exact CN.bVld_sound hC h

theorem cNode_sound' {C : BConsts} (hC : bConstsOK C = true) {KX PT WT GT WC : ℕ → ℕ} {nc n i : ℕ}
    (hGT : ∀ s < 2, ∀ c < nc, ∀ c' < nc, LCanon 12 111 111 (GT (s + 2 * c + 16 * c')))
    (hWC : ∀ e c, e < c → c < nc → LCanon 12 111 111 (WC (c + 8 * e)))
    (hKX : ∀ j < i, LCanon 12 7 111 (getRec KX 9324 j) ∧ chartOf (getRec PT 32 j) < nc)
    (h : cNode C KX PT WT GT WC nc n i = true) :
    chartOf (getRec PT 32 i) < nc ∧ LCanon 12 7 111 (getRec KX 9324 i) ∧
      lastCols (blkM (getRec KX 9324 i)) = 1 ∧
      (∀ e < chartOf (getRec PT 32 i), ¬ IsUnit (lastCols (blkM (getRec KX 9324 i) *
        bigM (WC (chartOf (getRec PT 32 i) + 8 * e)))).det) ∧
      (0 < i → fldW (getRec PT 32 i) 0 20 < i ∧ fldW (getRec PT 32 i) 20 4 < 2 ∧
        ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
          blkM (getRec KX 9324 (fldW (getRec PT 32 i) 0 20)) *
            bigM (GT (fldW (getRec PT 32 i) 20 4 + 2 * chartOf (getRec PT 32 (fldW (getRec PT 32 i) 0 20))
              + 16 * chartOf (getRec PT 32 i))) = M * blkM (getRec KX 9324 i)) := by
  exact CN.cNode_sound' hC hGT hWC hKX h

theorem spreadB_sound {C : Consts} (hC : constsOK C = true) {k : ℕ} (hk : k < 2 ^ 2331)
    (hf : ∀ e < 777, k / 2 ^ (3 * e) % 8 < 5) :
    LCanon 12 7 111 (spreadB C.MS k) ∧ blkM (spreadB C.MS k) = keyM k := by
  exact SSp.spreadB_sound hC hk hf

end CFSG.KS.LyOm

end
