module

public import CFSG.Quasithin.Recognition.CertF8

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28.SU

open CFSG.Quasithin

@[expose] def Rm : Matrix (Fin 2) (Fin 2) GF8 := !![0, 1; 1, 1]

@[expose] def Km : Matrix (Fin 2) (Fin 2) GF8 := !![0, 1; 1, 0]

@[expose] def sIdx (i : Fin 3) (r : Fin 2) : Fin 6 := ⟨2 * i.val + r.val, by omega⟩

@[expose] def sEquiv : Fin 3 × Fin 2 ≃ Fin 6 where
  toFun p := sIdx p.1 p.2
  invFun a := (⟨a.val / 2, by omega⟩, ⟨a.val % 2, by omega⟩)
  left_inv := by decide
  right_inv := by decide

theorem sEquiv_apply (i : Fin 3) (r : Fin 2) : sEquiv (i, r) = sIdx i r := rfl

@[expose] def blockEquiv : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) GF8) ≃+*
    Matrix (Fin 6) (Fin 6) GF8 :=
  (Matrix.compRingEquiv (Fin 3) (Fin 2) GF8).trans (Matrix.reindexRingEquiv GF8 sEquiv)

theorem blockEquiv_apply (B : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) GF8))
    (i j : Fin 3) (r s : Fin 2) : blockEquiv B (sIdx i r) (sIdx j s) = B i j r s := by
  simp [blockEquiv, Matrix.reindexRingEquiv, ← sEquiv_apply]

@[expose] def rbM : Matrix (Fin 6) (Fin 6) GF8 := blockEquiv (Matrix.diagonal fun _ => Rm)

@[expose] def jbM : Matrix (Fin 6) (Fin 6) GF8 := blockEquiv (Matrix.diagonal fun _ => Km)

@[expose] def blk (A : Matrix (Fin 6) (Fin 6) GF8) (i j : Fin 3) : Matrix (Fin 2) (Fin 2) GF8 :=
  Matrix.of fun r s => A (sIdx i r) (sIdx j s)

@[expose] def detBlk (A : Matrix (Fin 6) (Fin 6) GF8) : Matrix (Fin 2) (Fin 2) GF8 :=
  blk A 0 0 * blk A 1 1 * blk A 2 2 + blk A 0 1 * blk A 1 2 * blk A 2 0 +
    blk A 0 2 * blk A 1 0 * blk A 2 1 + blk A 0 2 * blk A 1 1 * blk A 2 0 +
    blk A 0 1 * blk A 1 0 * blk A 2 2 + blk A 0 0 * blk A 1 2 * blk A 2 1

end CFSG.AGLEmbedding.KFactProofs.G28.SU
