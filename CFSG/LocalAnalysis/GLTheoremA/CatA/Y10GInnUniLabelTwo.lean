module

public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.Open.StatedDefs
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.Assembly.GL83StatedBridge
import CFSG.Assembly.OpenBridges
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem exists_quot_heldSU_two_equiv_psl {E : Type} [Field E] [Finite E] {m : ℕ}
    (τ' : E ≃+* E) (hτ' : ∀ x, τ' (τ' x) = x) (hτ'm : ∀ x, τ' x = x ^ (2 ^ m))
    (hE : Nat.card E = (2 ^ m) ^ 2) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ m ∧
      Nonempty (heldSU 2 E τ' hτ' ⧸ Subgroup.center (heldSU 2 E τ' hτ') ≃*
        StatedProj (StatedSL 2 k)) := by
  have h2 : (2 : E) = 0 := two_eq_zero_of_card hE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
  let k : Type := ↥(CFSG.LieType.Steinberg.fixedSubfield E 2 m)
  have hk : Nat.card k = 2 ^ m :=
    CFSG.LieType.Steinberg.card_fixedSubfield (F := E) (p := 2) (f := m) hE
  obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
    (K := E) (r := 2) (f := m) hE
  have hheld : heldSU 2 E τ' hτ' = StatedSU 2 (2 ^ m) E :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU
      (a := 2) (Q := 2 ^ m) hτ'm
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  rw [hheld]
  exact ⟨(QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)).trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 k)⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end
