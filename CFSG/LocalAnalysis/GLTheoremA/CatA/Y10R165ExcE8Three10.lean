module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three5

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open scoped Matrix MatrixGroups

section Order


private theorem pow_eq_one_of_zetaPow {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) (v : ℕ) : (ζ ^ v) ^ p = 1 := by
  rw [← pow_mul, Nat.mul_comm v p, pow_mul, hζ.pow_eq_one, one_pow]

theorem orderOf_rootDiagUnit_e8T3XColumn_zetaPow {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) {ε : ℤ} {q : ZMod p} :
    orderOf (rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε q i).val)) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.ComponentClassification.CatFC.DS81.Ex.orderOf_rootDiagUnit_eq_prime_of_pow
    (τ := Tag.E8) (K := L) _ ?_ 3 ?_
  · intro i
    exact pow_eq_one_of_zetaPow hζ _
  · show ζ ^ (e8T3XColumn ε q 3).val ≠ 1
    rw [e8T3XColumn_apply_three, ZMod.val_one'' hp.ne_one, pow_one]
    exact hζ.ne_one hp.one_lt

theorem orderOf_rootDiagUnit_e8T3ZColumn_zetaPow {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) {ε : ℤ} {q : ZMod p} :
    orderOf (rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val)) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.ComponentClassification.CatFC.DS81.Ex.orderOf_rootDiagUnit_eq_prime_of_pow
    (τ := Tag.E8) (K := L) _ ?_ 2 ?_
  · intro i
    exact pow_eq_one_of_zetaPow hζ _
  · show ζ ^ (e8T3ZColumn ε q 2).val ≠ 1
    rw [e8T3ZColumn_apply_two, ZMod.val_one'' hp.ne_one, pow_one]
    exact hζ.ne_one hp.one_lt

end Order

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
