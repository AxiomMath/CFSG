module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28SUBase
public import Certificates.Data.ONanG28SU

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28.SU

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28
open scoped Matrix

@[expose] def mP : Matrix (Fin 6) (Fin 6) GF8 := decode suP

@[expose] def mPi : Matrix (Fin 6) (Fin 6) GF8 := decode suPi

@[expose] def aMat (k : Fin 7) : Matrix (Fin 6) (Fin 6) GF8 :=
  mPi * decode (wordCode suW[k.val]!) * mP

@[expose] def suOK : Prop :=
  mP * mPi = 1 ∧ mPi * mP = 1 ∧ mPi * decode tzc * mP = rbM ∧
    (∀ k : Fin 7, (aMat k)ᵀ * jbM * aMat k = jbM ∧ detBlk (aMat k) = 1) ∧
    Matrix.trace (decode (wordCode suW[5]!)) = GF8.ofNat' 6

instance instDecidableSuOK : Decidable suOK := by
  unfold suOK
  infer_instance

end CFSG.AGLEmbedding.KFactProofs.G28.SU
