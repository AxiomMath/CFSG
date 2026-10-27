module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Fix11Native
public import Certificates.Certificate12602

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Sporadic.J4Schreier Matrix
open scoped Classical

set_option maxRecDepth 100000

theorem rowsMatrix_pairRows (P : Array ℕ × Array ℕ) :
    rowsMatrix (pairRows P) = CFSG.Sporadic.SmallF2.rowsMatrix 112 P.1 := by
  ext i j
  rw [rowsMatrix_apply, CFSG.Sporadic.SmallF2.rowsMatrix_apply]
  unfold pairRows
  rw [Array.getElem?_map]
  cases h : P.1[i.val]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [V2.toVec_zero, CFSG.Sporadic.SmallF2.toVecD_zero]
  | some n =>
    simp only [Option.map_some, Option.getD_some]
    rw [natV2, V2.toVec_ofFn, CFSG.Sporadic.SmallF2.toVecD_apply]

theorem card_centralizer_qx :
    ∃ h ∈ Hj, orderOf h = 11 ∧ Nat.card (Subgroup.centralizer ({qx} : Set J)) =
      11 * Nat.card ↥(Subgroup.centralizer ({h} : Set J) ⊓ Hj) :=
  Certificates.certificate12602

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
