module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Assembly
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem modelHyperGen_of_seitzHyperGamma_eq_top {M : Type*} [Group M] {p : ℕ}
    {B : Subgroup (MulAut M)} (h : CFSG.LieType.Seitz.seitzHyperGamma p B = ⊤) :
    ModelHyperGen p B := by
  unfold ModelHyperGen
  rw [eq_top_iff, ← h]
  unfold CFSG.LieType.Seitz.seitzHyperGamma
  refine iSup₂_le fun H hH => fun x hx => Subgroup.subset_closure ?_
  exact ⟨H, hH.1, hH.2, fun b hb => (CFSG.LieType.Seitz.mem_fixedPoints.1 hx) b hb⟩

theorem a2ThreeSixtyFour_holds : A2ThreeSixtyFour := by
  intro F _ _ hF B hB hBc
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 6) := Fintype.ofFinite (GaloisField 2 6)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card F = Fintype.card (GaloisField 2 6) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 6 (by norm_num)]
    norm_num
  let e : F ≃+* GaloisField 2 6 := FiniteField.ringEquivOfCardEq hcard
  let φ : projectiveSL 3 F ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 6) :=
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr e).trans
      (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 6)).symm
  have h27 : Nat.card B = 27 := by rw [hBc]; norm_num
  exact modelHyperGen_of_seitzHyperGamma_eq_top
    (CFSG.RankThree.PartTwo.Sec4.seitzL3SixtyFour_holds (projectiveSL 3 F) ⟨φ⟩ B hB h27)

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
