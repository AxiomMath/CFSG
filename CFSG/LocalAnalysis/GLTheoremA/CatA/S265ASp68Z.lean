module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.Open.StatedDefs
import CFSG.GH74.Generic.GKFCover
import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Generic.Certificates
import CFSG.GH74.Statements
import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

variable {Ω : Type} [Group Ω] [Finite Ω] {X S : Subgroup Ω} {K : Type} [Field K] [Finite K]

theorem center_pQuot_eq_bot_of_sp68 (hS : GLAPComponent 3 X S) (hK : Nat.card K = 8)
    (e : PSimple 3 S ≃* StatedProj (StatedSp 3 K)) : Subgroup.center (PQuot 3 S) = ⊥ := by
  have hperf : Group.IsPerfect (PQuot 3 S) :=
    Group.isPerfect_def.mpr (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hS).1
  let q : PQuot 3 S →* StatedProj (StatedSp 3 K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (PQuot 3 S)))
  have hker : q.ker = Subgroup.center (PQuot 3 S) := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le
  obtain ⟨-, ⟨m⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_hopfMultiplier (K := K)
    (n := 3) (by norm_num) (by omega)
  have h1 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedSp 3 K))) = 1 := by
    rw [← Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv, Nat.card_congr m.toEquiv,
      hK]
    simp
  rw [h1, Nat.dvd_one, hker] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

theorem nonempty_mulEquiv_of_sp68 (hS : GLAPComponent 3 X S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hK : Nat.card K = 8) (e : PSimple 3 S ≃* StatedProj (StatedSp 3 K)) :
    Nonempty (↥S ≃* StatedProj (StatedSp 3 K)) :=
  ⟨((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcore.symm)).trans
    ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
      (center_pQuot_eq_bot_of_sp68 hS hK e).symm)).trans e))⟩

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
