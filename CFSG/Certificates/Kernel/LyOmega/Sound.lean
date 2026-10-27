module

public import Certificates.Data.Kernel.LyOmega.Base
public import CFSG.Certificates.Kernel.LyOmega.Defs
import CFSG.Certificates.Kernel.LyOmega.SoundB1
import CFSG.Certificates.Kernel.LyOmega.SoundB2
import CFSG.Certificates.Kernel.LyOmega.SoundB3
import CFSG.Certificates.Kernel.LyOmega.SoundB4
import CFSG.Certificates.Kernel.LyOmega.SoundB5
import CFSG.Certificates.Kernel.LyOmega.SoundB6
import CFSG.Certificates.Kernel.LyOmega.SoundMulCore
import CFSG.Certificates.Kernel.LyOmega.SoundCNode
import CFSG.Certificates.Kernel.LyOmega.SoundC1
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.KS.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL

theorem bMul_sound {C : BConsts} (hC : bConstsOK C = true) {X G : ℕ} (hX : LCanon 12 7 111 X)
    (hG : LCanon 12 111 111 G) :
    LCanon 12 7 111 (bMul C X G) ∧ blkM (bMul C X G) = blkM X * bigM G := by
  exact MC.bMul_sound hC hX hG

theorem fMul_sound {C : BConsts} (hC : bConstsOK C = true) {X Y : ℕ} (hX : LCanon 12 111 111 X)
    (hY : LCanon 12 111 111 Y) :
    LCanon 12 111 111 (fMul C X Y) ∧ bigM (fMul C X Y) = bigM X * bigM Y := by
  exact MC.fMul_sound hC hX hY

theorem sMul_sound {C : SConsts} (hC : sConstsOK C = true) {X Y : ℕ} (hX : LCanon 11 7 7 X)
    (hY : LCanon 11 7 7 Y) :
    LCanon 11 7 7 (sMul C X Y) ∧ smM (sMul C X Y) = smM X * smM Y := by
  exact MC.sMul_sound hC hX hY

theorem sBlk_sound {C : SConsts} (hC : sConstsOK C = true) {r X K : ℕ} (hr : r ≤ 64)
    (hX : LCanon 11 r 49 X) (hK : LCanon 11 49 49 K) :
    LCanon 11 r 49 (sBlk C X K) ∧ ∀ q < r, vec49 (sBlk C X K / 2 ^ (539 * q)) =
      Matrix.vecMul (vec49 (X / 2 ^ (539 * q))) (kM K) := by
  exact MC.sBlk_sound hC hr hX hK

theorem sameSpanL_sound {C : BConsts} (hC : bConstsOK C = true) {N Y : ℕ}
    (hN : LCanon 12 7 111 N) (hY : LCanon 12 7 111 Y) (h : sameSpanL C N Y = true) :
    blkM Y = lastCols (blkM Y) * blkM N := by
  exact MC.sameSpanL_sound hC hN hY h

theorem sameSpan_sound {C : BConsts} (hC : bConstsOK C = true) {N Y : ℕ}
    (hN : LCanon 12 7 111 N) (hY : LCanon 12 7 111 Y) (h : sameSpan C N Y = true) :
    blkM Y = firstCols (blkM Y) * blkM N := by
  exact MC.sameSpan_sound hC hN hY h

theorem cNode_sound {C : BConsts} (hC : bConstsOK C = true) {KX PT WT GT WC : ℕ → ℕ} {nc n i : ℕ}
    (hGT : ∀ k, LCanon 12 111 111 (GT k)) (hWC : ∀ k, LCanon 12 111 111 (WC k))
    (hKX : ∀ j < i, LCanon 12 7 111 (getRec KX 9324 j))
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
  exact CN.cNode_sound hC hGT hWC hKX h

theorem cRange_sound {C : BConsts} {KX PT WT GT WC : ℕ → ℕ} {nc n b₀ c : ℕ}
    (h : cRange C KX PT WT GT WC nc n b₀ c = true) :
    ∀ i, 64 * b₀ ≤ i → i < 64 * (b₀ + c) → i < n → cNode C KX PT WT GT WC nc n i = true := by
  exact SC1.cRange_sound h

theorem cSort_sound {KX PT SG : ℕ → ℕ} {n k₀ c : ℕ} (h : cSort KX PT SG n k₀ c = true) :
    ∀ k, k₀ ≤ k → k < k₀ + c → getRec SG 20 k < n ∧ getRec SG 20 (k + 1) < n ∧
      cKey KX PT (getRec SG 20 k) < cKey KX PT (getRec SG 20 (k + 1)) := by
  exact SC1.cSort_sound h

theorem cFix_eq {C : BConsts} {KX PT XM : ℕ → ℕ} {n b₀ c : ℕ} :
    cFix C KX PT XM n b₀ c = ((Finset.Ico (64 * b₀) (64 * (b₀ + c))).filter fun i => i < n ∧
      sameSpanL C (getRec KX 9324 i) (bMul C (getRec KX 9324 i) (XM (chartOf (getRec PT 32 i)))) =
        true).card := by
  exact SC1.cFix_eq

theorem sLeaf_sound {C : SConsts} (hC : sConstsOK C = true) {KX PT : ℕ → ℕ} {Ks : List ℕ}
    {m n b r : ℕ} (hKs : ∀ s < m, LCanon 11 49 49 (pickL Ks s)) (h : sLeaf C KX PT Ks m n b = true)
    (hr : r < 64) (hi0 : 0 < 64 * b + r) (hin : 64 * b + r < n) :
    fldW (sRec PT (64 * b + r)) 0 20 < 64 * b + r ∧ fldW (sRec PT (64 * b + r)) 20 2 < m ∧
      ((∀ j < 64 * b + r, LCanon 11 1 49 (getRec KX 539 j)) →
        LCanon 11 1 49 (getRec KX 539 (64 * b + r)) ∧
        vec49 (getRec KX 539 (64 * b + r)) = Matrix.vecMul
          (vec49 (getRec KX 539 (fldW (sRec PT (64 * b + r)) 0 20)))
          (kM (pickL Ks (fldW (sRec PT (64 * b + r)) 20 2)))) := by
  exact SB6.sLeaf_sound_of hC (fun hr hX hK => sBlk_sound hC hr hX hK) hKs h hr hi0 hin

theorem sSort_sound {KX SG : ℕ → ℕ} {n k₀ c : ℕ} (h : sSort KX SG n k₀ c = true) :
    ∀ k, k₀ ≤ k → k < k₀ + c → getRec SG 20 k < n ∧ getRec SG 20 (k + 1) < n ∧
      getRec KX 539 (getRec SG 20 k) < getRec KX 539 (getRec SG 20 (k + 1)) := by
  exact SB1.sSort_sound h

theorem sClass_sound {C : SConsts} (hC : sConstsOK C = true) {X : ℕ} (hX : LCanon 11 7 7 X) :
    sClass C X = (if smM X ^ 2 = 1 ∧ smM X ≠ 1 then 1 else 0) +
      (if smM X ^ 3 = 1 ∧ smM X ≠ 1 ∧ (smM X).trace = 1 then 2 ^ 16 else 0) +
      (if smM X ^ 5 = 1 ∧ smM X ≠ 1 ∧ (smM X - 1) ^ 2 = 0 then 2 ^ 32 else 0) +
      (if smM X ^ 5 = 1 ∧ smM X ≠ 1 ∧ 2 ≤ ((smM X - 1) ^ 2).rank then 2 ^ 48 else 0) := by
  exact SB5.sClass_sound hC hX

theorem sCountLeaf_eq {C : SConsts} {KX : ℕ → ℕ} {n b : ℕ} :
    sCountLeaf C KX n b = ∑ r ∈ (Finset.range 64).filter (fun r => 64 * b + r < n),
      sClass C (getRec KX 539 (64 * b + r)) := by
  exact SB1.sCountLeaf_eq

theorem kronOK_sound {A B K : ℕ} (h : kronOK A B K = true) :
    LCanon 11 49 49 K ∧ ∀ i j k l : Fin 7, kM K ⟨7 * i + j, by omega⟩ ⟨7 * k + l, by omega⟩ =
      smM A i k * smM B j l := by
  exact SB3.kronOK_sound h

theorem trOK_sound {r c X Y : ℕ} (h : trOK r c X Y = true) :
    ∀ i < r, ∀ j < c, ent 12 1332 Y j i = ent 12 1332 X i j := by
  exact SB1.trOK_sound h

theorem fTr_sound {X : ℕ} (hX : LCanon 12 111 111 X) :
    LCanon 12 111 111 (fTr X) ∧ bigM (fTr X) = (bigM X).transpose := by
  exact SB2.fTr_sound hX

theorem relayOK_sound {X Y : ℕ} (h : relayOK X Y = true) :
    Y < 2 ^ 539 ∧ ∀ i j : Fin 7, smM Y i j = ent 12 1332 X i j := by
  exact SB1.relayOK_sound h

theorem digLanesK_sound {cs : List Char} {X n : ℕ} (hn : n < 2 ^ 20) (h : digLanesK cs X n = true) :
    (cs.filter (· ≠ '\n')).length = n ∧ ∀ t < n,
      (cs.filter (· ≠ '\n')).getD t '0' = Char.ofNat (48 + (X / 2 ^ (1332 * (t / 111) + 12 * (t % 111)) % 2 ^ 12)) := by
  exact SB4.digLanesK_sound hn h

end CFSG.KS.LyOm

end
