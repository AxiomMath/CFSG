module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKerQuot
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenTrans
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFieldAut
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenOmega
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenSigma
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenClauses
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenCompGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenKerQuotGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenSigmaGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenTransGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenOrbitGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenThreeGen
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateLinear
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16005
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8052

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

namespace NineSettingGen

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G}

section Certified

theorem isPSLType_oPPrimeHull_quotKer_of_three_components (h714 : SevenOneFourField)
    (h72 : KFactOmegaNotCentral) (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (hp : 3 ∉ sigmaM G M) (hU : NineNineOne M 3) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q H)
    {C : Subgroup (StarGroup 3 H)} {q : StarGroup 3 H}
    (hcomp : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔
      ∃ i : Fin 3, D = C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom)
    (hinj : Function.Injective (fun i : Fin 3 => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom))
    (hrank : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D → CFSG.Open.pRank 3 D = 1)
    (hY : centralizer (CFSG.layer (StarGroup 3 H) : Set (StarGroup 3 H)) = ⊥)
    (hLM : pLayerIn 3 H ≤ M) (hE : ¬ starImg 3 H E ≤ compNormalizer (StarGroup 3 H)) :
    IsPSLType 2 (ZMod 3) ↥(oPPrimeHull 3 (⊤ : Subgroup (QuotKer M H))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Cf : Fin 3 → Subgroup (StarGroup 3 H) :=
    fun i => C.map (MulAut.conj (q ^ (i : ℕ))).toMonoidHom
  have hCf : ∀ i : Fin 3, CFSG.IsComponent (Cf i) :=
    fun i => (hcomp (Cf i)).mpr ⟨i, rfl⟩
  have hcompCf : ∀ D : Subgroup (StarGroup 3 H), CFSG.IsComponent D ↔
      ∃ i : Fin 3, D = Cf i :=
    hcomp
  have hE_layer : CFSG.layer (StarGroup 3 H) = ⨆ i, Cf i :=
    layer_eq_iSup_of_components Cf hcompCf
  haveI hlayerC : (CFSG.layer (StarGroup 3 H)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  haveI hlayerN : (CFSG.layer (StarGroup 3 H)).Normal := inferInstance
  haveI hsupN : (⨆ i, Cf i).Normal := hE_layer ▸ hlayerN
  have hcomm : ∀ i j : Fin 3, i ≠ j →
      Cf i ≤ centralizer (Cf j : Set (StarGroup 3 H)) := by
    intro i j hij
    rcases CFSG.LocalCores.distinct_components_commute (hCf i) (hCf j) with h | h
    · exact absurd (hinj h) hij
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hrankCf : ∀ i : Fin 3, CFSG.Open.pRank 3 (Cf i) = 1 :=
    fun i => hrank (Cf i) (hCf i)
  have hZ : ∀ i : Fin 3, ¬ 3 ∣ Nat.card (center ↥(Cf i)) :=
    fun i => not_dvd_card_center_of_pRank_eq_one h72 h.isKGroup_star (hCf i)
      Nat.prime_three (by norm_num) (hrankCf i)
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) ≤ 3 :=
    h.pRank_star_le_three hH2 hp
  let T : Subgroup (StarGroup 3 H) := starImg 3 H Q ⊓ ⨆ i, Cf i
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 T (⨆ i, Cf i) :=
    (h.isSylowOf_starImg_top hQ).inf_of_le_normalizer le_top
      (le_of_eq (Subgroup.normalizer_eq_top (H := ⨆ i, Cf i)).symm)
  let V : Subgroup (StarGroup 3 H) := omegaOnePSub 3 T
  obtain ⟨hVc, hV3, hV27, hVi, hVle⟩ :=
    omegaOnePSub_structure (p := 3) Nat.prime_three (by norm_num) Cf hcomm hrankCf hZ hrk hT
  obtain ⟨y, hyE, hy1, hyN⟩ := h.exists_ne_one_mem_compNormalizer hcomp hinj hE
  obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp hyE
  have huE : (u : G) ∈ E := Subgroup.mem_subgroupOf.mp hu
  have hy3 : y ^ 3 = 1 := by
    have hu3 : (u : G) ^ 3 = 1 := h.stdE.2.2.1.2 (u : G) huE
    have hu3' : u ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [← huy, ← map_pow, hu3', map_one]
  have hyLayer : y ∈ CFSG.layer (StarGroup 3 H) :=
    mem_layer_of_mem_compNormalizer h714 h72 h.isKGroup_star hrk hcomp hinj hrank hY hyN hy3
  have hySup : y ∈ ⨆ i, Cf i := by
    rw [← hE_layer]
    exact hyLayer
  have hyQ : y ∈ starImg 3 H Q := starImg_mono h.stdE.2.1 hyE
  have hyV : y ∈ V := Subgroup.subset_closure ⟨⟨hyQ, hySup⟩, hy3⟩
  have hCV : centralizer (V : Set (StarGroup 3 H)) ≤ starImg 3 H M :=
    h.centralizer_le_of_mem_starImg hyE hy1 hyV
  have hVc' : ∀ a b : ↥V, a * b = b * a :=
    fun a b => Subtype.ext (by simpa using hVc a a.2 b b.2)
  have hV3' : ∀ v : ↥V, v ^ 3 = 1 :=
    fun v => Subtype.ext (by simpa using hV3 v v.2)
  have hVcard : Nat.card ↥V = 27 := by
    change Nat.card V = 27
    rw [hV27]
    norm_num
  let D : Fin 3 → Subgroup ↥V := fun i => (Cf i).subgroupOf V
  have hD : ∀ i : Fin 3, Nat.card (D i) = 3 := by
    intro i
    have h1 : (Cf i).subgroupOf V = (V ⊓ Cf i).subgroupOf V :=
      (Subgroup.inf_subgroupOf_left (Cf i) V).symm
    have h2 : Nat.card ((V ⊓ Cf i).subgroupOf V) = Nat.card ↥(V ⊓ Cf i) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := V ⊓ Cf i) (K := V) inf_le_left).toEquiv
    change Nat.card ((Cf i).subgroupOf V) = 3
    rw [h1, h2]
    exact hVi i
  have hDV : (⨆ i, D i) = ⊤ := by
    rw [eq_top_iff]
    refine (Subgroup.map_le_map_iff_of_injective V.subtype_injective).mp ?_
    have htop : (⊤ : Subgroup ↥V).map V.subtype = V := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hDmap : ∀ i : Fin 3, (D i).map V.subtype = V ⊓ Cf i := by
      intro i
      change ((Cf i).subgroupOf V).map V.subtype = V ⊓ Cf i
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_comm _ _
    rw [htop, Subgroup.map_iSup]
    calc V ≤ ⨆ i, V ⊓ Cf i := hVle
      _ = ⨆ i, (D i).map V.subtype := iSup_congr (fun i => (hDmap i).symm)
  let ρ : ↥(normalizer (V : Set (StarGroup 3 H))) →* MulAut ↥V := V.normalizerMonoidHom
  have hρ : ∀ x i, ∃ j, (D i).map (ρ x).toMonoidHom = D j := by
    intro x i
    have hcomp' : CFSG.IsComponent ((Cf i).map
        (MulAut.conj (x : StarGroup 3 H)).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (x : StarGroup 3 H)) (hCf i)
    obtain ⟨j, hj⟩ := (hcomp _).mp hcomp'
    refine ⟨j, ?_⟩
    rw [map_normalizerMonoidHom_subgroupOf V (Cf i) x, hj]
  obtain ⟨φ, hφs, hφk⟩ := h.exists_hom_quotKer
  have hLMlayer : CFSG.layer (StarGroup 3 H) ≤ starImg 3 H M := h.pLayerIn_le_iff.mp hLM
  have hLM' : (⨆ i, Cf i) ≤ starImg 3 H M := by
    rw [← hE_layer]
    exact hLMlayer
  have hLφ : (⨆ i, Cf i) ≤ φ.ker := by
    intro l hl
    rw [← hE_layer] at hl
    rw [MonoidHom.mem_ker]
    exact hφk l (fun g => hLMlayer (hlayerN.conj_mem l hl g))
  have hNV : normalizer (T : Set (StarGroup 3 H)) ≤ normalizer (V : Set (StarGroup 3 H)) :=
    normalizer_le_normalizer_omegaOnePSub 3 T
  have htop : (⊤ : Subgroup (StarGroup 3 H)) ≤ (⨆ i, Cf i) ⊔ normalizer T := by
    have h1 := h.top_le_layer_sup_normalizer hQ
    rw [hE_layer] at h1
    exact h1
  let π : ↥(normalizer (V : Set (StarGroup 3 H))) →* QuotKer M H :=
    φ.comp (normalizer (V : Set (StarGroup 3 H))).subtype
  have hπ : Function.Surjective π :=
    surjective_comp_subtype_of_top_le (A := ⨆ i, Cf i) hφs
      (htop.trans (sup_le_sup_left hNV (⨆ i, Cf i))) hLφ
  have hρπ : ρ.ker ≤ π.ker := by
    intro x hx
    have hxker : x ∈ V.normalizerMonoidHom.ker := hx
    rw [Subgroup.normalizerMonoidHom_ker] at hxker
    have hxcent : (x : StarGroup 3 H) ∈ centralizer (V : Set (StarGroup 3 H)) :=
      Subgroup.mem_subgroupOf.mp hxker
    show φ (x : StarGroup 3 H) = 1
    exact hφk (x : StarGroup 3 H) (fun h0 =>
      conj_mem_of_mem_centralizer (L := ⨆ i, Cf i) (N := normalizer T) (W := V)
        (M := starImg 3 H M) htop hNV hLM' hCV hxcent h0)
  exact h.isPSLType_oPPrimeHull_quotKer_of_lines hp hU hVc' hV3' hVcard D hD hDV ρ hρ π hπ hρπ

theorem nineTenTwo_of_not_le_compNormalizer (h62 : NineSixTwoComp) (h713 : SevenOneThree)
    (hI : NineTenInputs) (h714 : SevenOneFourField) (h72 : KFactOmegaNotCentral)
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hU : NineNineOne M p) (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hQN : ¬ starImg p H Q ≤ compNormalizer (StarGroup p H)) :
    pLayerIn p H ≠ ⊥ ∧ pLayerIn p H ≤ M ∧ NineTenTwo p M H E := by
  obtain ⟨rfl, C, q, hq, hC, hcomp, hinj, hrank, hR⟩ :=
    h.three_components h72 hH2 hp hQN
  have hY : centralizer (CFSG.layer (StarGroup 3 H) : Set (StarGroup 3 H)) = ⊥ :=
    centralizer_layer_eq_bot Nat.prime_three H hR
  have hLM : pLayerIn 3 H ≤ M :=
    h.pLayerIn_le_of_three_components h62 hH2 hp hq hcomp hinj
  have hE : ¬ starImg 3 H E ≤ compNormalizer (StarGroup 3 H) :=
    h.not_starImg_le_compNormalizer h713 hI hH2 hp hU hQ hLM hY
  refine ⟨?_, hLM, ?_⟩
  · intro hbot
    have hlayer : CFSG.layer (StarGroup 3 H) = ⊥ :=
      (pLayerIn_eq_bot_iff Nat.prime_three H).mp hbot
    have hCle : C ≤ CFSG.layer (StarGroup 3 H) := CFSG.LocalCores.component_le_layer hC
    rw [hlayer] at hCle
    have hCbot : C = ⊥ := le_bot_iff.mp hCle
    have hnt : Nontrivial ↥C := CFSG.LocalCores.isQuasisimple_nontrivial hC.1
    exact (Subgroup.nontrivial_iff_ne_bot C).mp hnt hCbot
  · refine Or.inl ⟨rfl, h.nineTenTwo_list hcomp hinj hrank hE, hR, ?_⟩
    exact h.isPSLType_oPPrimeHull_quotKer_of_three_components h714 h72 hH2 hp hU hQ
      hcomp hinj hrank hY hLM hE

end Certified

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
