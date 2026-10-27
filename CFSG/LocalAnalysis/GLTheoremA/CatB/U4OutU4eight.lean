module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09U48

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

theorem u4Out_index_u4eight {P : Type} [Group P] [Finite P] (h : catalogIs P S9.isU4eight) :
    (innerAut P).index = 6 := by
  haveI : Finite (MulAut P) :=
    Finite.of_injective (fun α : MulAut P => (α : P → P)) DFunLike.coe_injective
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.bridge_u4eight h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 (GaloisField 2 (2 * 3)) :=
    ⟨Nat.prime_two, by norm_num, GaloisField.card 2 (2 * 3) (by norm_num)⟩
  obtain ⟨-, -, -, -, hout, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hU
      (n := 4) (by norm_num) (by norm_num)
  have e2 : P ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 4 :=
    e1.trans ((CFSG.PGLModel.projSUEquivStatedProj 4 2 3).trans
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm)
  have hO : Nat.card (MulAut P ⧸ innerAut P) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 4)) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e2).toEquiv
  change Nat.card (MulAut P ⧸ innerAut P) = 6
  rw [hO, hout]
  norm_num

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
