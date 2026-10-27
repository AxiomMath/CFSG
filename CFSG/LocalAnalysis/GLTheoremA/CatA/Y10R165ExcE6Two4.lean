module

public import CFSG.RankThree.PartTwo.Census.Exceptional.E6Two
public import CFSG.HardMathSupport.Seitz.Proving.SL2PrimeOrder
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.OmegaMinusTorus
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Census.Exceptional
open CFSG.LieType.Steinberg.Minuscule
open CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

section FData

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def e6TwoOrtho3 : Fin 3 → Fin (Tag.rank .E6) → ℤ :=
  fun i => e6OrthoRoots (Fin.castLE (by omega : 3 ≤ 4) i)

theorem e6TwoOrtho3_check :
    (∀ i, CFSG.LieType.Chevalley.RootOps.isRootB .E6 (e6TwoOrtho3 i) = true) ∧
      ∀ i j, i ≠ j → e6TwoOrtho3 i + e6TwoOrtho3 j ≠ 0 ∧
        e6TwoOrtho3 i - e6TwoOrtho3 j ≠ 0 ∧
        CFSG.LieType.Chevalley.RootOps.isRootB .E6 (e6TwoOrtho3 i + e6TwoOrtho3 j) = false ∧
        CFSG.LieType.Chevalley.RootOps.isRootB .E6 (e6TwoOrtho3 i - e6TwoOrtho3 j) = false := by
  obtain ⟨hr, -, hso, -⟩ := e6Two_check
  refine ⟨fun i => hr _, fun i j hij => ?_⟩
  have hcast : Fin.castLE (by omega : 3 ≤ 4) i ≠ Fin.castLE (by omega : 3 ≤ 4) j := by
    intro h
    exact hij (Fin.castLE_injective (by omega : 3 ≤ 4) h)
  exact hso _ _ hcast

theorem exists_orderOf_eq_of_dvd_card_sl2 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdiv : q ∣ Nat.card F - 1 ∨ Nat.card F = 2 ∧ q = 3) :
    ∃ c : SL(2, F), orderOf c = q := by
  refine CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hq ?_
  rcases hdiv with h | ⟨hcard, rfl⟩
  · rw [← Nat.one_pow 2, Nat.sq_sub_sq]
    exact h.mul_left _
  · rw [hcard]
    norm_num

end FData

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two
