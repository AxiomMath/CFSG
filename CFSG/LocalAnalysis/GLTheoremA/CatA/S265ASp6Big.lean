module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ABlk
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp6Lay
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASpAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp6
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.Assembly.OpenBridges
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.GroupTheory.PLayer.Bootstrap
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Glue
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks2
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnAPI
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot
import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
import CFSG.Milestones.ASVolI.A2OddAut
import CFSG.Milestones.ASVolI.F48.Core
import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec4.Item426A6
import CFSG.RankThree.PartTwo.Sec4.Statements423
import Certificates.Certificate41501

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open Module CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine
open CFSG.RankThree.SubgroupLists (spForm spForm_isAlt spForm_nondegenerate)
open CFSG.RankThree.Classical (spEnd spEnd_apply)

variable {Ω : Type} [Group Ω] [Finite Ω]

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

theorem false_of_sp6_big {X J B D : Subgroup Ω} (hN : NLAct 3 X J B D) (hB : IsElemAbelian 3 B)
    (hcat : catalogIs (PSimple 3 J) S9.isSp6two) (h27 : 27 * Nat.card D ≤ Nat.card B) :
    False := by
  obtain ⟨e⟩ := CatB.bridge_sp6two hcat
  obtain ⟨Ab, hAb, hcard, hL⟩ := exists_spImage (by norm_num) e hN hB
  have hle : 27 ≤ Nat.card Ab :=
    Nat.le_of_mul_le_mul_right (by rw [hcard]; exact h27) Nat.card_pos
  obtain ⟨A₀, hA₀A, hA₀c⟩ : ∃ A₀ ≤ Ab, Nat.card A₀ = 27 := by
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 3) Nat.prime_three
      hAb.isPGroup (by norm_num; exact hle)
    refine ⟨K.map Ab.subtype, Subgroup.map_subtype_le K, ?_⟩
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective K _ Ab.subtype_injective).toEquiv, hK]
    norm_num
  have hA₀ : IsElemAbelian 3 A₀ := hAb.mono hA₀A
  haveI : Finite (V₆ ≃ₗ[ZMod 2] V₆) :=
    Finite.of_injective (fun e : V₆ ≃ₗ[ZMod 2] V₆ => (e : V₆ → V₆))
      fun e e' h => LinearEquiv.ext (congrFun h)
  letI : Fintype ↥(A₀.map sp6Act) := Fintype.ofFinite _
  have hAe : IsElemAbelian 3 (A₀.map sp6Act) := hA₀.map sp6Act
  have hpF : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide
  have hBi : InvariantBilin (A₀.map sp6Act) (spForm 3 (ZMod 2)) := fun a u v => by
    obtain ⟨s, -, hs⟩ := Subgroup.mem_map.mp a.2
    rw [← hs]
    exact sp6Act_isometry s u v
  have hcardA : Fintype.card ↥(A₀.map sp6Act) = 27 := by
    rw [← Nat.card_eq_fintype_card, Subgroup.card_map_of_injective sp6Act_injective, hA₀c]
  have hV : finrank (ZMod 2) V₆ = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hev : ∀ D : Hyperplane (A₀.map sp6Act) 3,
      Even (finrank (ZMod 2) ↥(blockSpace (A₀.map sp6Act) D.1)) := fun D => by
    have halt : (LinearMap.BilinForm.restrict (spForm 3 (ZMod 2))
        (blockSpace (A₀.map sp6Act) D.1)).IsAlt := fun w => by
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
      exact spForm_isAlt _
    exact halt.even_finrank (blockSpace_nondegenerate (A₀.map sp6Act) Nat.prime_three hpF hAe
      spForm_isAlt hBi spForm_nondegenerate D)
  have hsplit : ∀ a, nOut (fun D : Hyperplane (A₀.map sp6Act) 3 => D.1)
      (fun D => finrank (ZMod 2) ↥(blockSpace (A₀.map sp6Act) D.1)) a =
      2 * nOut (fun D : Hyperplane (A₀.map sp6Act) 3 => D.1)
        (fun D => finrank (ZMod 2) ↥(blockSpace (A₀.map sp6Act) D.1) / 2) a := by
    intro a
    unfold nOut
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun D _ => ?_
    split_ifs
    · rfl
    · obtain ⟨k, hk⟩ := hev D
      dsimp only
      omega
  have hM : ∑ D : Hyperplane (A₀.map sp6Act) 3,
      finrank (ZMod 2) ↥(blockSpace (A₀.map sp6Act) D.1) / 2 ≤ 4 := by
    have h1 := sum_finrank_blockSpace_le_finrank (A₀.map sp6Act) Nat.prime_three hpF hAe
    have h2 : ∑ D : Hyperplane (A₀.map sp6Act) 3,
        finrank (ZMod 2) ↥(blockSpace (A₀.map sp6Act) D.1) =
        2 * ∑ D : Hyperplane (A₀.map sp6Act) 3,
          finrank (ZMod 2) ↥(blockSpace (A₀.map sp6Act) D.1) / 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun D _ => ?_
      obtain ⟨k, hk⟩ := hev D
      omega
    omega
  refine false_of_nOut_two_three (fun D : Hyperplane (A₀.map sp6Act) 3 => D.1)
    (fun D => finrank (ZMod 2) ↥(blockSpace (A₀.map sp6Act) D.1) / 2) (fun D => D.2)
    (fun D => ⟨fun n hn g => ?_⟩) Subtype.val_injective (fun a ha1 => ?_) hM (Or.inl hcardA)
  · have := hAe.1
    rwa [mul_comm' g n, mul_inv_cancel_right]
  · obtain ⟨s, hsA₀, hsa⟩ := Subgroup.mem_map.mp a.2
    have hs1 : s ≠ 1 := fun h1 => ha1 (Subtype.ext (by rw [← hsa, h1, map_one]; rfl))
    have hfix := finrank_ker_le_two_of_layer_eq_bot_sp6 (hA₀.2 s hsA₀) hs1 (hL s (hA₀A hsA₀) hs1)
    have hfs : fixedByEnd (a : V₆ ≃ₗ[ZMod 2] V₆) = LinearMap.ker (spEnd s - 1) := by
      rw [← hsa]
      exact fixedByEnd_sp6Act s
    have hbr := finrank_eq_fixedByEnd_add_nOut (A₀.map sp6Act) Nat.prime_three hpF hAe a
    rw [hsplit, hV, hfs] at hbr
    omega

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
