module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp6
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AP2Lin
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.PLayer.Bootstrap
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks2
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import Certificates.Certificate41501

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine
open CFSG.RankThree.SubgroupLists (spForm spForm_isAlt spForm_nondegenerate)
open CFSG.RankThree.Classical (spEnd spEnd_apply)
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

local notation "V₆" => Fin 3 ⊕ Fin 3 → ZMod 2

private noncomputable def sp6Act : StatedSp 3 (ZMod 2) →* (V₆ ≃ₗ[ZMod 2] V₆) :=
  (linIsometryGroup (spForm 3 (ZMod 2))).subtype.comp
    (statedSpEquivLinIsometryGroup 3 (ZMod 2)).toMonoidHom

private theorem sp6Act_apply (s : StatedSp 3 (ZMod 2)) (v : V₆) : sp6Act s v = spEnd s v := by
  rw [spEnd_apply]
  exact statedSpEquivLinIsometryGroup_apply 3 (ZMod 2) s v

private theorem sp6Act_injective : Function.Injective sp6Act :=
  (linIsometryGroup (spForm 3 (ZMod 2))).subtype_injective.comp
    (statedSpEquivLinIsometryGroup 3 (ZMod 2)).injective

private theorem sp6Act_isometry (s : StatedSp 3 (ZMod 2)) (u v : V₆) :
    spForm 3 (ZMod 2) (sp6Act s u) (sp6Act s v) = spForm 3 (ZMod 2) u v :=
  mem_linIsometryGroup.mp (statedSpEquivLinIsometryGroup 3 (ZMod 2) s).2 u v

private theorem fixedByEnd_sp6Act (s : StatedSp 3 (ZMod 2)) :
    fixedByEnd (sp6Act s) = LinearMap.ker (spEnd s - 1) := by
  ext v
  rw [mem_fixedByEnd, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    sp6Act_apply]

theorem sp6_eq_bot_of_normalized_two_subgroup {Ab T : Subgroup (StatedSp 3 (ZMod 2))}
    (hAb : IsElemAbelian 3 Ab) (h9 : Nat.card Ab = 9)
    (hfix : ∀ s ∈ Ab, s ≠ 1 → Module.finrank (ZMod 2) (LinearMap.ker (spEnd s - 1)) ≤ 2)
    (hT : IsPGroup 2 T) (hAT : Ab ≤ Subgroup.normalizer (T : Set (StatedSp 3 (ZMod 2)))) :
    T = ⊥ := by
  haveI : Finite (V₆ ≃ₗ[ZMod 2] V₆) :=
    Finite.of_injective (fun e : V₆ ≃ₗ[ZMod 2] V₆ => (e : V₆ → V₆))
      fun e e' h => LinearEquiv.ext (congrFun h)
  haveI : Fintype ↥(Ab.map sp6Act) := Fintype.ofFinite _
  have hA9 : Nat.card ↥(Ab.map sp6Act) = 9 := by
    rw [Subgroup.card_map_of_injective sp6Act_injective, h9]
  have hB : InvariantBilin (Ab.map sp6Act) (spForm 3 (ZMod 2)) := fun a u v => by
    obtain ⟨s, -, hs⟩ := Subgroup.mem_map.mp a.2
    rw [← hs]
    exact sp6Act_isometry s u v
  have hfixA : ∀ a : ↥(Ab.map sp6Act), a ≠ 1 →
      Module.finrank (ZMod 2) (fixedByEnd (a : V₆ ≃ₗ[ZMod 2] V₆)) ≤ 2 := fun a ha1 => by
    obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.mp a.2
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact ha1 (Subtype.ext (hsa.symm.trans (map_one sp6Act)))
    rw [← hsa, fixedByEnd_sp6Act]
    exact hfix s hs hs1
  have hA := CFSG.SectionRank.isElemAbelian_map hAb sp6Act
  have hpF : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide
  have hF : ∀ x : ZMod 2, x ^ 3 = 1 → x = 1 := by decide
  have hT' := eq_bot_of_normalized_two_subgroup (Ab.map sp6Act) hF spForm_isAlt hB
    spForm_nondegenerate hA
    (fixedSpaceOf_eq_bot_of_card_nine (Ab.map sp6Act) hpF spForm_isAlt hB spForm_nondegenerate hA
      hA9 hfixA)
    (finrank_blockSpace_le_two_of_card_nine (Ab.map sp6Act) hA9 hfixA) (T := T.map sp6Act)
    (hT.map sp6Act) (fun t ht u v => by
      obtain ⟨s, -, hs⟩ := Subgroup.mem_map.mp ht
      rw [← hs]
      exact sp6Act_isometry s u v)
    ((Subgroup.map_mono hAT).trans (Subgroup.le_normalizer_map sp6Act))
  exact (Subgroup.map_eq_bot_iff_of_injective T sp6Act_injective).mp hT'

end CFSG.LocalAnalysis.GLTheoremA.S265A
