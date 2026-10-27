module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicIso4
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74
open scoped MatrixGroups

@[expose] noncomputable def slCongr4 {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') :
    Matrix.SpecialLinearGroup (Fin 4) K ≃* Matrix.SpecialLinearGroup (Fin 4) K' where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _

theorem genLoc4_of_zmod3 {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3)
    (h : GenLoc4 (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3))) :
    GenLoc4 (Matrix.SpecialLinearGroup (Fin 4) F) := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 3 := by rw [Fintype.card_eq_nat_card]; exact hF3
  exact GenLoc4.of_mulEquiv (slCongr4 (ZMod.ringEquivOfPrime F Nat.prime_three hF')) h

end CFSG.GH74.Generic.BProg.B2
