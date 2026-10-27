module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1K6
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Out
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Layer
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section One

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}

theorem szh1b_pCore_le (hY : Sz32Case2Data Pb a c y) : CFSG.pCore 5 Y ≤ Pb := by
  obtain ⟨S, hS⟩ := hY.sylow
  rw [← hS]
  haveI : (CFSG.pCore 5 Y).Normal := CFSG.pCore_normal
  exact CFSG.pCore_isPGroup.le_sylow_of_normal S

theorem szh1b_Z_le_pCore (hY : Sz32Case2Data Pb a c y) (hne : CFSG.pCore 5 Y ≠ ⊥) :
    sz32Z a c ≤ CFSG.pCore 5 Y := by
  haveI hRn : (CFSG.pCore 5 Y).Normal := CFSG.pCore_normal
  have hnz : CFSG.pCore 5 Y ⊓ sz32Z a c ≠ ⊥ :=
    szh1_inf_Z_ne_bot hY (szh1b_pCore_le hY) (fun q _ n hn => hRn.conj_mem n hn q) hne
  have hirr := hY.irr (CFSG.pCore 5 Y ⊓ sz32Z a c) inf_le_right (by
    intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro h
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hRn.conj_mem h h1 g, (hg h).mp h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, (hg h).mpr h2⟩
      have := hRn.conj_mem _ h1 g⁻¹
      rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this)
  rcases hirr with h | h
  · exact absurd h hnz
  · exact inf_eq_right.mp h

theorem szh1b_comp_le_centralizer_pCore {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    L ≤ Subgroup.centralizer (CFSG.pCore 5 Y : Set Y) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI hRn : (CFSG.pCore 5 Y).Normal := CFSG.pCore_normal
  haveI : Group.IsNilpotent (CFSG.pCore 5 Y) := (CFSG.pCore_isPGroup (p := 5)).isNilpotent
  haveI : Group.IsSolvable (CFSG.pCore 5 Y) := inferInstance
  have hsub : IsSubnormal (CFSG.pCore 5 Y) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hRn.isSubnormal
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal L
      (CFSG.pCore 5 Y) hL hsub)

theorem szh1_pCore_bot (hY : Sz32Case2Data Pb a c y) (hI6103 : KFactI6103Five)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : CFSG.pCore 5 Y = ⊥ := by
  clear hI6103
  by_contra hne
  obtain ⟨S, hS⟩ := hY.sylow
  have hc5 : c ^ 5 ∈ CFSG.pCore 5 Y := szh1b_Z_le_pCore hY hne (szh1_c5_mem_Z a c)
  have hLW : L ≤ Subgroup.centralizer ({c ^ 5} : Set Y) :=
    (szh1b_comp_le_centralizer_pCore hL).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hc5))
  obtain ⟨N, hN⟩ := hY.series
  rw [← hS] at hN
  exact szh1_not_le_of_centSeries hY.core S hN hL hLW

theorem szh1b_mem_normalizer_zpowers {g h : Y} {n : ℤ} (hgh : g * h * g⁻¹ = h ^ n) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers h : Set Y) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, hgh, ← zpow_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers h) _

theorem szh1b_normal_of_unique {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hall : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L) : L.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hc : IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  have h := hall _ hc
  have hmem : g * x * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rw [h] at hmem
  exact hmem

theorem szh1b_centralizer_eq_bot (hcore : primeComplementCore (G := Y) 5 = ⊥)
    (hbot : CFSG.pCore 5 Y = ⊥) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hall : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L) :
    Subgroup.centralizer (L : Set Y) = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hlayer : CFSG.layer Y = L := by
    rw [CFSG.layer.eq_sSup]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      exact (hall K ((CFSG.isComponent_iff_open K).mp hK)).le
    · exact le_sSup ((CFSG.isComponent_iff_open L).mpr hL)
  have h := CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.centralizer_layer_inf_centralizer_pCore_le
    (Y := Y) (p := 5) hcore
  rw [hbot, hlayer] at h
  rw [eq_bot_iff]
  intro g hg
  have h2 : g ∈ Subgroup.centralizer ((⊥ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have : x = 1 := by simpa using hx
    rw [this]; simp
  exact h ⟨hg, h2⟩

theorem szh1_one_comp_false (hY : Sz32Case2Data Pb a c y) (hI6103 : KFactI6103Five)
    (hI122 : KFactI122Five) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hall : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L) : False := by
  have hbot := szh1_pCore_bot hY hI6103 hL
  have hLn := szh1b_normal_of_unique hL hall
  have hC := szh1b_centralizer_eq_bot hY.core hbot hL hall
  obtain ⟨S, rfl⟩ := hY.sylow
  have hOm : ∀ g ∈ (S : Subgroup Y), ∀ h ∈ (S : Subgroup Y), g ^ 5 = 1 → h ^ 5 = 1 →
      g * h = h * g := fun g hg h hh g5 h5 => szh1_Om_comm hY hg hh g5 h5
  have hz := szh1_center_bot hI6103 hY.catalog hY.core hY.rank S hOm hL
  obtain ⟨hsimple, hnonab, hcat⟩ := szh1_simple_data hY.catalog hL hz
  obtain ⟨n, hn, -⟩ := hY.pres.ya
  obtain ⟨ν, hν, -⟩ := hY.pres.yc
  obtain ⟨N, hNn, ⟨k, hk⟩, hNtop⟩ := hI122 Y L hLn hsimple hnonab hcat hC S
    (Subgroup.zpowers a) (Subgroup.zpowers c) y hY.facts.card
    (Subgroup.zpowers_le.mpr hY.pres.a_mem) (Subgroup.zpowers_le.mpr hY.pres.c_mem)
    inferInstance inferInstance
    (by rw [Nat.card_zpowers, hY.pres.ord_a]; norm_num)
    (by rw [Nat.card_zpowers, hY.facts.ord_c]; norm_num)
    hY.pres.inf
    (fun u hu v hv => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.zpow_zpow hY.pres.ac i j).eq)
    hY.pres.y_mem (szh1_y_order hY) hY.pres.y_not hY.pres.gen.symm
    (szh1b_mem_normalizer_zpowers hn) (szh1b_mem_normalizer_zpowers hν)
    (fun z hz => szh1_center_iff hY hz)
  exact hNtop (hY.perf N hNn ⟨k, hk⟩)

end One

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
