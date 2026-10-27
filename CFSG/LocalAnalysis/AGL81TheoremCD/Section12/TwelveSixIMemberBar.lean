module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransfer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem center_barM_eq_bot_and_psl {M L : Subgroup G} (hL : IsTwoPrimeComponent M L) {n : ℕ}
    (hL3 : IsL3TwoPow n (modTwoCore L)) :
    Subgroup.center ↥(barM M L) = ⊥ ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* PSL(3, GaloisField 2 n)) := by
  obtain ⟨eB⟩ := CFSG.RankThree.PartTwo.Sec19.Item194Proof.nonempty_barM_mulEquiv
    hL.le hL.inf_twoCore
  obtain ⟨e3⟩ := hL3
  have hL3bar : IsL3TwoPow n (barM M L) := ⟨eB.symm.trans e3⟩
  haveI : IsSimpleGroup ↥(barM M L) := hL3bar.isSimpleGroup
  haveI : Group.IsPerfect ↥(barM M L) := ⟨hL.component.2.2.1⟩
  have hZ : Subgroup.center ↥(barM M L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(barM M L)) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h)
        (Group.IsPerfect.not_isMulCommutative (G := ↥(barM M L)))
  exact ⟨hZ, ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot.trans (eB.symm.trans e3))⟩⟩

noncomputable def yHom {M L X : Subgroup G} (hXL : X ≤ L) (hL : L ≤ M) :
    ↥X →* ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) :=
  (QuotientGroup.mk' _).comp
    ((CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.barHom M L hL).comp (inclusion hXL))

theorem range_yHom {M L X : Subgroup G} (hXL : X ≤ L) (hL : L ≤ M) : (yHom hXL hL).range =
    ((barM M X).subgroupOf (barM M L)).map (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) := by
  rw [yHom, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range,
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.map_barHom_subgroupOf hXL hL]

theorem isPGroup_ker_yHom {M L X : Subgroup G} (hXL : X ≤ L) (hL : L ≤ M)
    (hZ : Subgroup.center ↥(barM M L) = ⊥) : IsPGroup 2 (yHom hXL hL).ker := by
  have h : (yHom hXL hL).ker =
      (CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.barHom M L hL).ker.comap
        (inclusion hXL) := by
    rw [yHom, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ, MonoidHom.comap_bot,
      ← MonoidHom.comap_ker]
  rw [h]
  have hP := CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.isPGroup_ker_barHom M L hL
  exact hP.comap_of_injective _ (Subgroup.inclusion_injective hXL)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
