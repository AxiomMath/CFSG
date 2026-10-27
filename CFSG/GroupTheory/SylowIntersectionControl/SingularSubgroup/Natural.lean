module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Generation
import CFSG.GroupTheory.PermSylowTwo.StabilizerSup
import CFSG.Quasithin.MS93.S38ESecMod
import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Head
import CFSG.GroupTheory.SpecialLinearTwoCommutator
import CFSG.GroupTheory.SylowIntersectionControl.RegularGeneration
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
import CFSG.Walter.PSL2Facts.Even
import CFSG.Quasithin.Background.C126A5ExtractAux
import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionTwoExtension
import CFSG.Quasithin.Background.A4Aut
import CFSG.Quasithin.Background.B6Basic
import CFSG.Quasithin.Background.C1GNNotation
import TauCeti.Algebra.Group.Subgroup.ModularLaw
import CFSG.GroupTheory.SubgroupTransport
import CFSG.Quasithin.EmptyFaithful.SzN15Nat
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.GroupTheory.ConjTransport
import CFSG.Quasithin.Background.B2Factorization
import CFSG.Quasithin.Background.G2SL2
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CoprimeInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoProductOddCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalSylowIntersection
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.B6Offenders
import CFSG.Quasithin.Background.C126A5Perm
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E2Three
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.Walter.Defs

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

private theorem autOn_le_of_forall_conj_mem_g45ja (h : GomiThm45Counterexample c G S)
    {P : Subgroup (MulAut ↥(gomiV G))} (hi : G ≤ conjClosure (baum S) G)
    (hP : ∀ y ∈ autOn G (gomiV G), ∀ k ∈ autOn (baum S) (gomiV G),
      y * k * y⁻¹ ∈ P) :
    autOn G (gomiV G) ≤ P := by
  have hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  set α : G →* MulAut ↥(gomiV G) := A4.actionOn (gomiV G) G hG
  have hαmem : ∀ g : G, α g ∈ autOn G (gomiV G) := fun g =>
    (A4.mem_autOn_iff hG).mpr ⟨g, rfl⟩
  have hbaumN : baum S ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    (CFSG.Quasithin.C1GN.baum_le S).trans (h.isSylowTwoOf.1.trans hG)
  have hGle : ∀ g : ↥G, α g ∈ P := by
    have hcl : G ≤ (P.comap α).map G.subtype := by
      refine hi.trans (conjClosure_le ?_)
      intro g hg z hz
      have hzG : z ∈ G := h.isSylowTwoOf.1 ((CFSG.Quasithin.C1GN.baum_le S) hz)
      have hzB : α ⟨z, hzG⟩ ∈ autOn (baum S) (gomiV G) :=
        (A4.mem_autOn_iff hbaumN).mpr ⟨⟨z, hz⟩, rfl⟩
      have hmem := hP (α ⟨g, hg⟩) (hαmem ⟨g, hg⟩) (α ⟨z, hzG⟩) hzB
      refine Subgroup.mem_map.mpr ⟨⟨g * z * g⁻¹,
        G.mul_mem (G.mul_mem hg hzG) (G.inv_mem hg)⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have harg : (⟨g, hg⟩ * ⟨z, hzG⟩ * ⟨g, hg⟩⁻¹ : ↥G) =
          ⟨g * z * g⁻¹, G.mul_mem (G.mul_mem hg hzG) (G.inv_mem hg)⟩ := rfl
      rw [← harg, map_mul, map_mul, map_inv]
      exact hmem
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (hcl g.2)
    have hxP : α x ∈ P := hx
    have hxg' : x = g := Subtype.ext hxg
    rwa [hxg'] at hxP
  intro y hy
  obtain ⟨g, rfl⟩ := (A4.mem_autOn_iff hG).mp hy
  exact hGle g

private theorem autOn_thompsonJ_le_ffJ_g45ja (h : GomiThm45Counterexample c G S) :
    autOn (thompsonJ S) (gomiV G) ≤ ffJ (autOn S (gomiV G)) := by
  have hVea : IsElemAbelian 2 (gomiV G) := (gomiV_moduleSetting G).1
  have hGN : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hVS : gomiV G ≤ S :=
    (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self (pCoreOf 2 G)).trans
      (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf)
  have hSN : S ≤ Subgroup.normalizer (gomiV G : Set Ω) := h.isSylowTwoOf.1.trans hGN
  have hdist : autOn (thompsonJ S) (gomiV G) =
      ⨆ (A : Subgroup Ω) (_ : IsMaxElemAbelian S A), autOn A (gomiV G) :=
    CFSG.Quasithin.autI_iSup₂ (hV := hVea) (fun A hA => fun x hx => hSN (hA.1 hx))
  rw [hdist]
  refine iSup_le fun A => iSup_le fun hA => ?_
  by_cases hAC : A ≤ Subgroup.centralizer (gomiV G : Set Ω)
  · rw [CFSG.Quasithin.AutOn.autOn_eq_bot_of_le_centralizer hAC]
    exact bot_le
  · have hFF := CFSG.Quasithin.offenderImages_isFFStarOffender (hV := hVea)
      (H := S) hVS hSN (B := CFSG.Quasithin.autI hVea A) ⟨A, ⟨hA, hAC⟩, rfl⟩
    rw [CFSG.Quasithin.autI_eq_autOn, CFSG.Quasithin.autI_eq_autOn] at hFF
    exact le_iSup₂_of_le (f := fun (B : Subgroup (MulAut ↥(gomiV G)))
      (_ : IsFFStarOffender (autOn S (gomiV G)) B) => B) (autOn A (gomiV G)) hFF le_rfl

private theorem mem_omegaOneCenterOf_thompsonJ_g45ja (h : GomiThm45Counterexample c G S)
    {w : ↥(gomiV G)} (hwJ : w ∈ fixV (autOn (thompsonJ S) (gomiV G))) :
    (w : Ω) ∈ omegaOneCenterOf (thompsonJ S) := by
  have hVea : IsElemAbelian 2 (gomiV G) := (gomiV_moduleSetting G).1
  have hGN : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hVS : gomiV G ≤ S :=
    (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self (pCoreOf 2 G)).trans
      (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf)
  have hcommJ : ∀ j ∈ thompsonJ S, (j : Ω) * (w : Ω) = (w : Ω) * (j : Ω) := by
    intro j hj
    have hjN : j ∈ Subgroup.normalizer (gomiV G : Set Ω) :=
      hGN (h.isSylowTwoOf.1 ((CFSG.Quasithin.C1GN.thompsonJ_le S) hj))
    have hmem : CFSG.Quasithin.conjAct (gomiV G) ⟨j, hjN⟩ ∈
        autOn (thompsonJ S) (gomiV G) :=
      CFSG.Quasithin.AutOn.conjAct_mem_autOn ⟨j, hjN⟩ hj
    have hcoe := congrArg Subtype.val (mem_fixV.mp hwJ _ hmem)
    rw [CFSG.Quasithin.AutOn.coe_conjAct_apply] at hcoe
    calc (j : Ω) * (w : Ω) = (j : Ω) * (w : Ω) * (j : Ω)⁻¹ * (j : Ω) := by group
      _ = (w : Ω) * (j : Ω) := by rw [hcoe]
  obtain ⟨A, hA⟩ := CFSG.Quasithin.exists_isMaxElemAbelian S
  have hwA : (w : Ω) ∈ A :=
    CFSG.Quasithin.inf_centralizer_le_of_isMaxElemAbelian hVea hVS hA
      ⟨w.2, Subgroup.mem_centralizer_iff.mpr (fun a ha =>
        hcommJ a ((le_iSup₂_of_le (f := fun (B : Subgroup Ω)
          (_ : IsMaxElemAbelian S B) => B) A hA le_rfl) ha))⟩
  have hwJmem : (w : Ω) ∈ thompsonJ S :=
    le_iSup₂_of_le (f := fun (B : Subgroup Ω) (_ : IsMaxElemAbelian S B) => B) A hA le_rfl hwA
  have hwCenter : (w : Ω) ∈ CFSG.Quasithin.centerOf (thompsonJ S) :=
    Subgroup.mem_inf.mpr ⟨hwJmem, Subgroup.mem_centralizer_iff.mpr hcommJ⟩
  have hw2 : (w : Ω) ^ 2 = 1 := hVea.2 (w : Ω) w.2
  exact Subgroup.subset_closure ⟨hwCenter, hw2⟩

private theorem autOn_baum_le_gomiCSP_g45j (h : GomiThm45Counterexample c G S)
    (L : Subgroup (MulAut ↥(gomiV G))) :
    autOn (baum S) (gomiV G) ≤ gomiCSP (autOn S (gomiV G)) L := by
  have hJle := autOn_thompsonJ_le_ffJ_g45ja h
  rw [gomiCSP]
  refine le_inf (CFSG.Quasithin.AutOn.autOn_mono (CFSG.Quasithin.C1GN.baum_le S)) ?_
  intro k hk
  rw [mem_fixingSubgroup_iff]
  intro w hw
  have hwff : w ∈ fixV (ffJ (autOn S (gomiV G))) := (Subgroup.mem_inf.mp hw).2
  have hwJ : w ∈ fixV (autOn (thompsonJ S) (gomiV G)) := by
    rw [mem_fixV] at hwff ⊢
    exact fun x hx => hwff x (hJle hx)
  have hwOmega := mem_omegaOneCenterOf_thompsonJ_g45ja h hwJ
  obtain ⟨n, hnB, hnk⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp hk
  have hcent := Subgroup.mem_centralizer_iff.mp hnB.2 (w : Ω) hwOmega
  rw [← hnk]
  apply Subtype.ext
  rw [MulAut.smul_def, CFSG.Quasithin.AutOn.coe_conjAct_apply, ← hcent]
  group

private theorem le_normalizer_of_autOn_baum_le_g45j (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hi : G ≤ conjClosure (baum S) G)
    (hK : autOn (baum S) (gomiV G) ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G)))) :
    autOn G (gomiV G) ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) := by
  have hG : G ≤ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2
  have hSN : S ≤ Subgroup.normalizer (gomiV G : Set Ω) := h.isSylowTwoOf.1.trans hG
  have hSNbaum : S ≤ Subgroup.normalizer (baum S : Set Ω) :=
    (Subgroup.le_normalizer : S ≤ Subgroup.normalizer (S : Set Ω)).trans
      (CFSG.Quasithin.normalizer_le_normalizer_baum S)
  have hnormK : autOn S (gomiV G) ≤
      Subgroup.normalizer (autOn (baum S) (gomiV G) : Set (MulAut ↥(gomiV G))) :=
    CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hSNbaum
  have hN : (⨆ y ∈ autOn G (gomiV G), Lb.map (MulAut.conj y).toMonoidHom) ≤
      Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) :=
    iSup_map_conj_le_normalizer hL.commute
  refine autOn_le_of_forall_conj_mem_g45ja h hi ?_
  intro y hy k hk
  have hy' : y⁻¹ ∈ autOn G (gomiV G) := (autOn G (gomiV G)).inv_mem hy
  obtain ⟨s, hs, hEq⟩ :=
    exists_mem_map_conj_eq (S := autOn S (gomiV G)) (L := Lb) (isSylowIn_autOn h).le hN
      hL.sup_eq hy'
  have hks : s⁻¹ * k * s ∈ autOn (baum S) (gomiV G) := by
    have hsinv : s⁻¹ ∈ autOn S (gomiV G) := (autOn S (gomiV G)).inv_mem hs
    have hmem := (Subgroup.mem_normalizer_iff.mp (hnormK hsinv) k).mp hk
    simpa using hmem
  have hkn : s⁻¹ * k * s ∈ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) := hK hks
  have hknmap : Lb.map (MulAut.conj (s⁻¹ * k * s)).toMonoidHom = Lb :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hkn
  have hksmap : Lb.map (MulAut.conj (k * s)).toMonoidHom =
      Lb.map (MulAut.conj s).toMonoidHom := by
    conv_lhs => rw [show k * s = s * (s⁻¹ * k * s) by group]
    rw [← map_conj_map_conj s (s⁻¹ * k * s) Lb, hknmap]
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  calc Lb.map (MulAut.conj (y * k * y⁻¹)).toMonoidHom
      = ((Lb.map (MulAut.conj y⁻¹).toMonoidHom).map
          (MulAut.conj k).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
        rw [map_conj_map_conj k y⁻¹ Lb, map_conj_map_conj y (k * y⁻¹) Lb,
          show y * (k * y⁻¹) = y * k * y⁻¹ by group]
    _ = ((Lb.map (MulAut.conj s).toMonoidHom).map
          (MulAut.conj k).toMonoidHom).map (MulAut.conj y).toMonoidHom := by rw [hEq]
    _ = (Lb.map (MulAut.conj (k * s)).toMonoidHom).map
          (MulAut.conj y).toMonoidHom := by rw [map_conj_map_conj k s Lb]
    _ = (Lb.map (MulAut.conj s).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
        rw [hksmap]
    _ = Lb := by
        rw [← hEq]
        simpa using map_conj_map_conj_inv y⁻¹ Lb

private theorem center_statedSL_two_eq_bot_g45ja {K : Type} [Field K] [CharP K 2] :
    Subgroup.center ↥(StatedSL 2 K) = ⊥ := by
  have hmap := Subgroup.map_center_eq
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
  rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.map_bot] at hmap
  exact hmap.symm

private theorem center_eq_bot_of_isSLn_two_g45ja {X : Type} [Group X] {m : ℕ}
    (h : IsSLn X 2 m) : Subgroup.center X = ⊥ := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hK2 : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) (by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard)
  have hmap := Subgroup.map_center_eq e
  rw [@center_statedSL_two_eq_bot_g45ja K _ hK2] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

private theorem center_eq_bot_of_isAlt_g45ja {X : Type} [Group X] {n : ℕ}
    (h : IsAlt X n) (hn : 4 ≤ n) : Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  have hZ : Subgroup.center (alternatingGroup (Fin n)) = ⊥ := by
    apply alternatingGroup.center_eq_bot
    simpa using hn
  have hmap := Subgroup.map_center_eq e
  rw [hZ] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

omit [Finite Ω] in
private theorem center_eq_bot_of_isGomiStepG_g45ja {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hg : IsGomiStepG Lb) : Subgroup.center ↥Lb = ⊥ := by
  rcases hg with ⟨m, -, hSLn, -⟩ | ⟨m, hm2, hAlt, -⟩
  · exact center_eq_bot_of_isSLn_two_g45ja hSLn
  · refine center_eq_bot_of_isAlt_g45ja hAlt ?_
    have h22 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega

private theorem inf_inf_centralizer_eq_bot_g45ja {Γ : Type*} [Group Γ] {Y L : Subgroup Γ}
    (hZ : Subgroup.center ↥L = ⊥) :
    (Y ⊓ Subgroup.centralizer (L : Set Γ)) ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxC, hxL⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨-, hxC⟩ := Subgroup.mem_inf.mp hxC
  have hxcenter : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (y : Γ) y.2)
  rw [hZ, Subgroup.mem_bot] at hxcenter
  exact congrArg Subtype.val hxcenter

private theorem centralizer_subgroupOf_eq_inf_g45ja {Γ : Type*} [Group Γ] {Y L : Subgroup Γ}
    (hLY : L ≤ Y) :
    (Y ⊓ Subgroup.centralizer (L : Set Γ)).subgroupOf Y =
      Subgroup.centralizer (L.subgroupOf Y : Set ↥Y) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨-, hxcent⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : Γ) ∈ L := hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcent (y : Γ) hy')
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hy : (⟨l, hLY hl⟩ : ↥Y) ∈ L.subgroupOf Y := hl
    have hc := (Subgroup.mem_centralizer_iff.mp hx) ⟨l, hLY hl⟩ hy
    exact congrArg Subtype.val hc

private theorem sup_eq_of_iSup_map_conj_eq_g45ja {Γ : Type*} [Group Γ] {Y S L : Subgroup Γ}
    (hN : Y ≤ Subgroup.normalizer (L : Set Γ))
    (hsup : (⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom) ⊔ S = Y) :
    L ⊔ S = Y := by
  have hconst : (⨆ y ∈ Y, L.map (MulAut.conj y).toMonoidHom) = L := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun y => iSup_le fun hy => ?_
      exact le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN hy))
    · refine le_iSup₂_of_le (f := fun y (_ : y ∈ Y) => L.map (MulAut.conj y).toMonoidHom)
        1 Y.one_mem (le_of_eq ?_)
      rw [show (MulAut.conj (1 : Γ)).toMonoidHom = MonoidHom.id _ from by ext x; simp,
        Subgroup.map_id]
  rw [← hsup, hconst]

private theorem isPGroup_quotient_g45ja {W : Type*} [CommGroup W]
    {Y Lb Sb : Subgroup (MulAut W)}
    (hLbY : Lb ≤ Y) (hSbY : Sb ≤ Y)
    (hSbN : Sb ≤ Subgroup.normalizer (Lb : Set (MulAut W)))
    (hSb2 : IsPGroup 2 Sb) (hYeq : Lb ⊔ Sb = Y) (hN : (Lb.subgroupOf Y).Normal) :
    IsPGroup 2 (↥Y ⧸ (Lb.subgroupOf Y)) := by
  let Q := ↥Y ⧸ (Lb.subgroupOf Y)
  let ψ : ↥Sb →* Q := (QuotientGroup.mk' (Lb.subgroupOf Y)).comp (Subgroup.inclusion hSbY)
  have hψsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxmul : (x : MulAut W) ∈ (Lb ⊔ Sb : Subgroup (MulAut W)) := by
      rw [hYeq]
      exact x.2
    change (x : MulAut W) ∈ (↑(Lb ⊔ Sb) : Set (MulAut W)) at hxmul
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Lb Sb hSbN] at hxmul
    obtain ⟨l, hl, s, hs, hls⟩ := Set.mem_mul.mp hxmul
    refine ⟨⟨s, hs⟩, ?_⟩
    show (QuotientGroup.mk' (Lb.subgroupOf Y)) ⟨s, hSbY hs⟩ =
      (QuotientGroup.mk' (Lb.subgroupOf Y)) x
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨⟨s⁻¹ * l * s, hLbY ((Subgroup.mem_normalizer_iff''.mp (hSbN hs) l).mp hl)⟩,
      (Subgroup.mem_normalizer_iff''.mp (hSbN hs) l).mp hl, ?_⟩
    apply Subtype.ext
    show s * (s⁻¹ * l * s) = (x : MulAut W)
    rw [← hls]
    group
  exact IsPGroup.of_surjective hSb2 ψ hψsurj

private theorem isPGroup_of_inf_eq_bot_g45ja {W : Type*} [CommGroup W]
    {Y Lb C : Subgroup (MulAut W)}
    (hCY : C ≤ Y) (hCL : C ⊓ Lb = ⊥) (hN : (Lb.subgroupOf Y).Normal)
    (hQ2 : IsPGroup 2 (↥Y ⧸ (Lb.subgroupOf Y))) : IsPGroup 2 C := by
  let κ : ↥C →* (↥Y ⧸ (Lb.subgroupOf Y)) :=
    (QuotientGroup.mk' (Lb.subgroupOf Y)).comp (Subgroup.inclusion hCY)
  have hκinj : Function.Injective κ := by
    intro a b hab
    have hmem : ((a : MulAut W) * (b : MulAut W)⁻¹) ∈ Lb := by
      have h := QuotientGroup.eq_iff_div_mem.mp hab
      rw [Subgroup.mem_subgroupOf] at h
      simpa [div_eq_mul_inv] using h
    have hmemC : ((a : MulAut W) * (b : MulAut W)⁻¹) ∈ C :=
      C.mul_mem a.2 (C.inv_mem b.2)
    have hbot : ((a : MulAut W) * (b : MulAut W)⁻¹) ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hCL]
      exact ⟨hmemC, hmem⟩
    rw [Subgroup.mem_bot] at hbot
    exact Subtype.ext (mul_inv_eq_one.mp hbot)
  exact IsPGroup.of_injective hQ2 κ hκinj

private theorem inf_centralizer_eq_bot_g45j (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hn : autOn G (gomiV G) ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))))
    (hg : IsGomiStepG Lb) :
    autOn G (gomiV G) ⊓ Subgroup.centralizer (Lb : Set (MulAut ↥(gomiV G))) = ⊥ := by
  have hLbY : Lb ≤ autOn G (gomiV G) := hL.le
  have hSbY : autOn S (gomiV G) ≤ autOn G (gomiV G) :=
    CFSG.Quasithin.AutOn.autOn_mono h.isSylowTwoOf.1
  have hSbN : autOn S (gomiV G) ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) :=
    hSbY.trans hn
  have hLbNormal : (Lb.subgroupOf (autOn G (gomiV G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbY).mpr hn
  have hYeq : Lb ⊔ autOn S (gomiV G) = autOn G (gomiV G) :=
    sup_eq_of_iSup_map_conj_eq_g45ja hn hL.sup_eq
  let C : Subgroup (MulAut ↥(gomiV G)) :=
    autOn G (gomiV G) ⊓ Subgroup.centralizer (Lb : Set (MulAut ↥(gomiV G)))
  have hCL : C ⊓ Lb = ⊥ :=
    inf_inf_centralizer_eq_bot_g45ja (center_eq_bot_of_isGomiStepG_g45ja hg)
  have hSb2 : IsPGroup 2 (autOn S (gomiV G)) :=
    CFSG.Quasithin.AutOn.isPGroup_autOn h.isSylowTwoOf.2.1
  have hQ2 : IsPGroup 2 (↥(autOn G (gomiV G)) ⧸
      (Lb.subgroupOf (autOn G (gomiV G)))) :=
    isPGroup_quotient_g45ja (W := ↥(gomiV G)) hLbY hSbY hSbN hSb2 hYeq hLbNormal
  have hC2 : IsPGroup 2 C :=
    isPGroup_of_inf_eq_bot_g45ja (W := ↥(gomiV G)) inf_le_left hCL hLbNormal hQ2
  have hCnorm : (C.subgroupOf (autOn G (gomiV G))).Normal := by
    change ((autOn G (gomiV G) ⊓ Subgroup.centralizer
      (Lb : Set (MulAut ↥(gomiV G)))).subgroupOf (autOn G (gomiV G))).Normal
    rw [centralizer_subgroupOf_eq_inf_g45ja hLbY]
    exact @Subgroup.normal_centralizer ↥(autOn G (gomiV G)) _
      (Lb.subgroupOf (autOn G (gomiV G))) hLbNormal
  exact (o2Trivial_autOn h) C inf_le_left hCnorm hC2

private theorem eq_autOn_of_isSLn_g45j (h : GomiThm45Counterexample c G S)
    (h37 : GomiFact37Three) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hi : G ≤ conjClosure (baum S) G)
    (hn : autOn G (gomiV G) ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))))
    (hC : autOn G (gomiV G) ⊓ Subgroup.centralizer (Lb : Set (MulAut ↥(gomiV G))) = ⊥)
    {m : ℕ} (hm : 1 ≤ m) (hSLn : IsSLn ↥Lb 2 m)
    (hnat : BinaryNaturalSL Lb (commV Lb) (gomiWXKer Lb) 2 m) :
    Lb = autOn G (gomiV G) := by
  have hV2 : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)
  have hsub : (Lb.subgroupOf (autOn G (gomiV G))).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mpr hn).isSubnormal
  have hCSP : gomiCSP (autOn S (gomiV G)) Lb =
      autOn S (gomiV G) ⊓ Lb :=
    h37 ↥(gomiV G) hV2 (autOn G (gomiV G)) (autOn S (gomiV G)) Lb m hm
      (pset_nonempty h) (isSylowIn_autOn h) hL.le hsub hSLn hC hnat
  have hKle : autOn (baum S) (gomiV G) ≤ Lb := by
    have h1 := autOn_baum_le_gomiCSP_g45j h Lb
    rw [hCSP] at h1
    exact h1.trans inf_le_right
  refine le_antisymm hL.le ?_
  refine autOn_le_of_forall_conj_mem_g45ja h hi ?_
  intro y hy k hk
  exact (Subgroup.mem_normalizer_iff.mp (hn hy) k).mp (hKle hk)

private theorem isPGroup_quotient_of_le_g45jb {E : Type*} [Group E]
    {N P : Subgroup E} [N.Normal] [P.Normal] (hNP : N ≤ P)
    (h : IsPGroup 2 (E ⧸ N)) : IsPGroup 2 (E ⧸ P) := by
  have hle : N ≤ Subgroup.comap (MonoidHom.id E) P := by simpa using hNP
  let f : (E ⧸ N) →* (E ⧸ P) := QuotientGroup.map N P (MonoidHom.id E) hle
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P q
    refine ⟨QuotientGroup.mk' N y, ?_⟩
    change QuotientGroup.map N P (MonoidHom.id E) hle (QuotientGroup.mk' N y) =
      QuotientGroup.mk' P y
    rw [QuotientGroup.map_mk']
    rfl
  exact IsPGroup.of_surjective h f hf

private theorem isPGroup_quotient_pPrimeCore_of_le_g45jb {E : Type*} [Group E] [Finite E]
    {N : Subgroup E} [N.Normal] (hN : N ≤ CFSG.GH74.GLS.pPrimePCore 2 E)
    (h : IsPGroup 2 (E ⧸ N)) : IsPGroup 2 (E ⧸ CFSG.pPrimeCore 2 E) := by
  let O : Subgroup E := CFSG.pPrimeCore 2 E
  let P : Subgroup E := CFSG.GH74.GLS.pPrimePCore 2 E
  let Q : Subgroup (E ⧸ O) := P.map (QuotientGroup.mk' O)
  have hOP : O ≤ P :=
    CFSG.GH74.GLS.Stage2.Final.Thm6.I414.pPrimeCore_le_pPrimePCore 2 E
  have hPO : Q = CFSG.pCore 2 (E ⧸ O) := by
    change (Subgroup.comap (QuotientGroup.mk' O) (CFSG.pCore 2 (E ⧸ O))).map
      (QuotientGroup.mk' O) = CFSG.pCore 2 (E ⧸ O)
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) _
  have hQn : Q.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  have hQ2 : IsPGroup 2 Q := by
    rw [hPO]
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hq3 : IsPGroup 2 ((E ⧸ O) ⧸ Q) := by
    have hP2 : IsPGroup 2 (E ⧸ P) := isPGroup_quotient_of_le_g45jb hN h
    have e := QuotientGroup.quotientQuotientEquivQuotient O P hOP
    exact IsPGroup.of_injective hP2 e.toMonoidHom e.injective
  exact CFSG.BenderSuzuki.External.hkt_isPGroup_of_normal_quotient (p := 2)
    (N := Q) hQ2 hq3

private theorem pPrimePCore_eq_top_of_isPGroup_quotient_g45jb {E : Type*} [Group E] [Finite E]
    (h : IsPGroup 2 (E ⧸ CFSG.pPrimeCore 2 E)) :
    CFSG.GH74.GLS.pPrimePCore 2 E = ⊤ := by
  have hcore : CFSG.pCore 2 (E ⧸ CFSG.pPrimeCore 2 E) = ⊤ := by
    refine top_le_iff.mp ?_
    exact CFSG.LieType.BorelTits.le_pCore 2 (N := ⊤) inferInstance
      (h.of_equiv Subgroup.topEquiv.symm)
  change (CFSG.pCore 2 (E ⧸ CFSG.pPrimeCore 2 E)).comap
    (QuotientGroup.mk' (CFSG.pPrimeCore 2 E)) = ⊤
  rw [hcore, Subgroup.comap_top]

private theorem sSup_gomiNSet_le_normalizer_g45jb {W : Type} [CommGroup W]
    {Y Lb : Subgroup (MulAut W)} (hN : Lb ∈ gomiNSet Y)
    (hPair : (gomiNSet Y).Pairwise fun N N' => ∀ x ∈ N, ∀ y ∈ N', x * y = y * x) :
    sSup (gomiNSet Y) ≤ Subgroup.normalizer (Lb : Set (MulAut W)) := by
  refine sSup_le fun N hNm => ?_
  by_cases hNL : N = Lb
  · rw [hNL]
    exact Subgroup.le_normalizer
  · rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    have hcomm : b * a = a * b := hPair hNm hN hNL b hb a ha
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact ha

private theorem sup_gstar_eq_of_iSup_map_conj_g45jb {W : Type} [CommGroup W]
    {Y Sb Lb : Subgroup (MulAut W)} (hN : Lb ∈ gomiNSet Y)
    (hSSup : sSup (gomiNSet Y) = gomiGstar0 Y)
    (hsup : (⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom) ⊔ Sb = Y) :
    gomiGstar0 Y ⊔ Sb = Y := by
  have hSbY : Sb ≤ Y := by rw [← hsup]; exact le_sup_right
  refine le_antisymm (sup_le (gomiGstar0_le Y) hSbY) ?_
  calc Y = (⨆ y ∈ Y, Lb.map (MulAut.conj y).toMonoidHom) ⊔ Sb := hsup.symm
    _ ≤ gomiGstar0 Y ⊔ Sb := by
      refine sup_le_sup_right ?_ Sb
      refine iSup₂_le fun y hy => ?_
      have hmem : Lb.map (MulAut.conj y).toMonoidHom ∈ gomiNSet Y :=
        map_conj_mem_gomiNSet hN hy
      exact (le_sSup hmem).trans (le_of_eq hSSup)

private theorem gstar_le_inSubgroup_pPrimePCore_g45jb {W : Type} [CommGroup W]
    (Y : Subgroup (MulAut W)) :
    gomiGstar0 Y ≤ CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y := by
  refine sSup_le fun A hA => hA.2

private theorem subgroupOf_gstar_le_pPrimePCore_g45jb {W : Type} [CommGroup W]
    (Y : Subgroup (MulAut W)) :
    (gomiGstar0 Y).subgroupOf Y ≤ CFSG.GH74.GLS.pPrimePCore 2 ↥Y := by
  intro x hx
  have hmem : (x : MulAut W) ∈ CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y := by
    apply gstar_le_inSubgroup_pPrimePCore_g45jb Y
    rwa [Subgroup.mem_subgroupOf] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

private theorem commV_ne_bot_of_isSLn_two_one_g45jb {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} (h : IsSLn ↥L 2 1) : commV L ≠ ⊥ := by
  have hL_ne : L ≠ ⊥ := by
    obtain ⟨K, hKf, hKfin, hKcard, ⟨eL⟩⟩ := h
    have hcard : Nat.card ↥L = 6 := by
      rw [Nat.card_congr eL.toEquiv,
        @CFSG.Open.StatedAPI.card_statedSL_two K hKf hKfin, hKcard]
      norm_num
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  exact fun hbot => hL_ne (CFSG.Quasithin.FixVLat.eq_bot_of_commV_eq_bot hbot)

private theorem inf_commV_fixV_ne_bot_g45jb {W : Type} [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) {L P : Subgroup (MulAut W)}
    (hcomm : commV L ≠ ⊥) (hLP : P ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hP2 : IsPGroup 2 ↥P) : commV L ⊓ fixV P ≠ ⊥ := by
  have hStab : P ≤ stabSub (commV L) := by
    intro g hg
    exact CFSG.Quasithin.FixVLat.mem_stabSub_commV_of_mem_normalizer (hLP hg)
  have hAut2 : IsPGroup 2 ↥(autSub P (commV L)) := by
    have hsub : IsPGroup 2 ↥(P.subgroupOf (stabSub (commV L))) :=
      hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hStab).symm
    change IsPGroup 2 ↥(Subgroup.map (CFSG.Quasithin.resHom (commV L))
      (P.subgroupOf (stabSub (commV L))))
    exact hsub.map (CFSG.Quasithin.resHom (commV L))
  have hFixAut_ne : fixV (autSub P (commV L)) ≠ ⊥ := by
    have hcommV2 : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (hW2 (v : W))
    have hNontriv : Nontrivial ↥(commV L) :=
      (Subgroup.nontrivial_iff_ne_bot (commV L)).mpr hcomm
    exact CFSG.Quasithin.MS93.S38E.fixV_ne_bot_of_isPGroup hcommV2 hAut2
  intro hbot
  have hmap := CFSG.Quasithin.map_subtype_fixV_autSub (A := P) (U := commV L) hStab
  have hzero : (fixV (autSub P (commV L))).map (commV L).subtype = ⊥ := by
    rw [hmap, hbot]
  exact hFixAut_ne ((Subgroup.map_eq_bot_iff_of_injective _
    (Subgroup.subtype_injective _)).mp hzero)

private theorem gomiCSP_le_normalizer_of_ne_bot_g45jb {W : Type} [CommGroup W]
    {Y Sb Lb : Subgroup (MulAut W)} (hN : Lb ∈ gomiNSet Y) (hSbY : Sb ≤ Y)
    (hIndep : iSupIndep fun N : ↥(gomiNSet Y) => commV (N : Subgroup (MulAut W)))
    (hF_ne : commV Lb ⊓ fixV (ffJ Sb) ≠ ⊥) :
    gomiCSP Sb Lb ≤ Subgroup.normalizer (Lb : Set (MulAut W)) := by
  intro s hs
  have hs' : s ∈ Sb ⊓ fixingSubgroup (MulAut W)
      ((commV Lb ⊓ fixV (ffJ Sb) : Subgroup W) : Set W) := hs
  obtain ⟨hsS, hsF⟩ := Subgroup.mem_inf.mp hs'
  rw [mem_fixingSubgroup_iff] at hsF
  have hsY : s ∈ Y := hSbY hsS
  have hNs : Lb.map (MulAut.conj s).toMonoidHom ∈ gomiNSet Y :=
    map_conj_mem_gomiNSet hN hsY
  have hsv : ∀ v ∈ commV Lb ⊓ fixV (ffJ Sb), (s : MulAut W) v = v := by
    intro v hv
    simpa using hsF v hv
  by_cases hEq : Lb.map (MulAut.conj s).toMonoidHom = Lb
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq
  · exfalso
    have hle : commV Lb ⊓ fixV (ffJ Sb) ≤
        commV Lb ⊓ commV (Lb.map (MulAut.conj s).toMonoidHom) := by
      refine le_inf inf_le_left ?_
      rw [CFSG.Quasithin.commV_map_conj_eq Lb s]
      intro v hv
      have hv1 : v ∈ commV Lb := (Subgroup.mem_inf.mp hv).1
      have hsvv : (s : MulAut W) v = v := hsv v hv
      have hinv : (s : MulAut W)⁻¹ v = v := by
        calc (s : MulAut W)⁻¹ v = (s : MulAut W)⁻¹ ((s : MulAut W) v) := by rw [hsvv]
          _ = v := by simp
      refine Subgroup.mem_map.mpr ⟨(s : MulAut W)⁻¹ v, ?_, ?_⟩
      · rwa [hinv]
      · simp
    let i : ↥(gomiNSet Y) := ⟨Lb, hN⟩
    let j : ↥(gomiNSet Y) := ⟨Lb.map (MulAut.conj s).toMonoidHom, hNs⟩
    have hne : i ≠ j := by
      intro hij
      apply hEq
      have hval := congrArg Subtype.val hij
      simpa [i, j] using hval.symm
    have hdisj : Disjoint (commV (i : Subgroup (MulAut W)))
        (commV (j : Subgroup (MulAut W))) := hIndep.pairwiseDisjoint hne
    have hbot : commV (i : Subgroup (MulAut W)) ⊓
        commV (j : Subgroup (MulAut W)) = ⊥ := disjoint_iff.mp hdisj
    exact hF_ne (le_bot_iff.mp (hle.trans (le_of_eq hbot)))

private theorem pPrimePCore_eq_self_of_setup_g45jb (h : GomiThm45Counterexample c G S)
    (h31 : GomiFact31) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hP0 : (gomiPstar0Set (autOn G (gomiV G))).Nonempty)
    (hN : Lb ∈ gomiNSet (autOn G (gomiV G))) :
    CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) (autOn G (gomiV G)) =
      autOn G (gomiV G) := by
  set Y : Subgroup (MulAut ↥(gomiV G)) := autOn G (gomiV G)
  set Sb : Subgroup (MulAut ↥(gomiV G)) := autOn S (gomiV G)
  let Nsub : Subgroup ↥Y := (gomiGstar0 Y).subgroupOf Y
  let P : Subgroup ↥Y := CFSG.GH74.GLS.pPrimePCore 2 ↥Y
  have hW2 : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)
  have hO2 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O2Trivial
      (gomiGstar0 Y) :=
    o2Trivial_of_normal (o2Trivial_autOn h) (gomiGstar0_le Y)
      (gomiGstar0_subgroupOf_normal Y)
  obtain ⟨⟨-, -, -, hSSup⟩, -, -, -⟩ := h31 ↥(gomiV G) hW2 Y hP0 hO2
  have hSbY : Sb ≤ Y := (isSylowIn_autOn h).le
  have hYsup : gomiGstar0 Y ⊔ Sb = Y :=
    sup_gstar_eq_of_iSup_map_conj_g45jb hN hSSup hL.sup_eq
  have hGstar_le_P : Nsub ≤ P := subgroupOf_gstar_le_pPrimePCore_g45jb Y
  have hNsub_normal : Nsub.Normal := gomiGstar0_subgroupOf_normal Y
  have hAB : Nsub ⊔ Sb.subgroupOf Y = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (gomiGstar0_le Y) hSbY, hYsup,
      Subgroup.subgroupOf_self]
  have hB2 : IsPGroup 2 ↥(Sb.subgroupOf Y) :=
    (isSylowIn_autOn h).isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSbY).symm
  have hq1 : IsPGroup 2 (↥Y ⧸ Nsub) :=
    CFSG.ComponentClassification.AschbacherComponentInvolution.normal_two_extension_quotient
      _ _ hAB hB2
  have hYO : IsPGroup 2 (↥Y ⧸ CFSG.pPrimeCore 2 ↥Y) :=
    isPGroup_quotient_pPrimeCore_of_le_g45jb hGstar_le_P hq1
  have hPtop : P = ⊤ := pPrimePCore_eq_top_of_isPGroup_quotient_g45jb hYO
  have hPmap : P.map Y.subtype = Y := by
    rw [hPtop, Subgroup.map_top, Subgroup.range_subtype]
  change P.map Y.subtype = Y
  exact hPmap

private theorem ffJ_le_gstar_of_setup_g45jb (h : GomiThm45Counterexample c G S)
    (h31 : GomiFact31) (h32 : GomiFact32)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hP0 : (gomiPstar0Set (autOn G (gomiV G))).Nonempty)
    (hN : Lb ∈ gomiNSet (autOn G (gomiV G))) :
    ffJ (autOn S (gomiV G)) ≤ gomiGstar0 (autOn G (gomiV G)) := by
  set Y : Subgroup (MulAut ↥(gomiV G)) := autOn G (gomiV G)
  set Sb : Subgroup (MulAut ↥(gomiV G)) := autOn S (gomiV G)
  have hSbY : Sb ≤ Y := (isSylowIn_autOn h).le
  have hPtop_in := pPrimePCore_eq_self_of_setup_g45jb h h31 hL hP0 hN
  have hW2 : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)
  have hO2 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O2Trivial
      (gomiGstar0 Y) :=
    o2Trivial_of_normal (o2Trivial_autOn h) (gomiGstar0_le Y)
      (gomiGstar0_subgroupOf_normal Y)
  have hg0 : gomiG0 Y = gomiGstar0 Y := h32 ↥(gomiV G) hW2 Y hO2
  have hle : ffJ Sb ≤ gomiG0 Y := by
    refine iSup₂_le fun A hA => ?_
    have hAY : A ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Pset Y :=
      ((mem_pset_iff_of_le hSbY).mp hA).1
    have hAP : A ≤ CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y := by
      rw [hPtop_in]
      exact hA.1.trans hSbY
    exact le_sSup (⟨hAY, hAP⟩ : A ∈ gomiP0Set Y)
  exact hle.trans (le_of_eq hg0)

private theorem gomiCSP_le_normalizer_of_mem_gomiNSet_g45j (h : GomiThm45Counterexample c G S)
    (h31 : GomiFact31) (h32 : GomiFact32) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hP0 : (gomiPstar0Set (autOn G (gomiV G))).Nonempty)
    (hN : Lb ∈ gomiNSet (autOn G (gomiV G))) :
    gomiCSP (autOn S (gomiV G)) Lb ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) := by
  classical
  set Y : Subgroup (MulAut ↥(gomiV G)) := autOn G (gomiV G)
  set Sb : Subgroup (MulAut ↥(gomiV G)) := autOn S (gomiV G)
  have hSbY : Sb ≤ Y := (isSylowIn_autOn h).le
  have hW2 : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)
  have hO2 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O2Trivial
      (gomiGstar0 Y) :=
    o2Trivial_of_normal (o2Trivial_autOn h) (gomiGstar0_le Y)
      (gomiGstar0_subgroupOf_normal Y)
  obtain ⟨⟨hSLn, -, hPair, hSSup⟩, ⟨-, hIndep, -⟩, -, -⟩ :=
    h31 ↥(gomiV G) hW2 Y hP0 hO2
  have hGstar_norm : gomiGstar0 Y ≤
      Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) := by
    rw [← hSSup]
    exact sSup_gomiNSet_le_normalizer_g45jb hN hPair
  have hffJ_le_Gstar : ffJ Sb ≤ gomiGstar0 Y :=
    ffJ_le_gstar_of_setup_g45jb h h31 h32 hL hP0 hN
  have hffJ_le_norm : ffJ Sb ≤
      Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) :=
    hffJ_le_Gstar.trans hGstar_norm
  have hffJ_le_Sb : ffJ Sb ≤ Sb := by
    refine iSup₂_le fun A hA => hA.1
  have hffJ2 : IsPGroup 2 ↥(ffJ Sb) :=
    (isSylowIn_autOn h).isPGroup.to_le hffJ_le_Sb
  have hcomm_ne : commV Lb ≠ ⊥ :=
    commV_ne_bot_of_isSLn_two_one_g45jb (hSLn Lb hN)
  have hF_ne : commV Lb ⊓ fixV (ffJ Sb) ≠ ⊥ :=
    inf_commV_fixV_ne_bot_g45jb hW2 hcomm_ne hffJ_le_norm hffJ2
  exact gomiCSP_le_normalizer_of_ne_bot_g45jb hN hSbY hIndep hF_ne

private theorem relIndex_map_comap_g45jd1 {A B : Type*} [Group A] [Group B]
    {H : Subgroup A} (φ : H →* B) (hφ : Function.Surjective φ) (K : Subgroup B) :
    ((K.comap φ).map H.subtype).relIndex H = K.index := by
  have hri := Subgroup.relIndex_map_map_of_injective (f := H.subtype)
    (K.comap φ) ⊤ H.subtype_injective
  rw [Subgroup.map_top, Subgroup.subtype_range, Subgroup.relIndex_top_right] at hri
  rw [hri, Subgroup.index_comap_of_surjective K hφ]

private theorem map_codRestrict_eq_g45jd1 {A B : Type*} [Group A] [Group B]
    {L : Subgroup B} (f : A →* B) (hf : ∀ g, f g ∈ L) {S : Subgroup A} {X : Subgroup B}
    (hX : X ≤ L) (hSX : S.map f = X) :
    S.map (f.codRestrict L hf) = X.subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hX]
  exact hSX

omit [Finite Ω] in
private theorem actionOn_map_subgroupOf_g45jd1 {G S : Subgroup Ω} (hSG : S ≤ G) :
    (S.subgroupOf G).map (A4.actionOn (gomiV G) G (gomiV_moduleSetting G).2) =
      autOn S (gomiV G) := by
  have key : ∀ {H : Subgroup Ω} (hH : H ≤ Subgroup.normalizer (gomiV G : Set Ω)) (x : ↥H),
      A4.actionOn (gomiV G) H hH x =
        conjAct (gomiV G) ⟨x.1, hH x.2⟩ := by
    intro H hH x
    ext v
    rw [A4.actionOn_apply_coe, AutOn.coe_conjAct_apply]
  ext a
  rw [AutOn.mem_autOn_iff_exists]
  constructor
  · rintro ⟨s, hs, hsa⟩
    refine ⟨s.1, (gomiV_moduleSetting G).2 s.2, Subgroup.mem_subgroupOf.mp hs, ?_⟩
    rw [← hsa, key]
  · rintro ⟨x, hx, hxS, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hSG hxS⟩, Subgroup.mem_subgroupOf.mpr hxS, ?_⟩
    rw [key]

private theorem preimage_ne_top_and_le_g45jd1 {A B : Type*} [Group A] [Group B]
    {H : Subgroup A} (φ : H →* B) (hφ : Function.Surjective φ)
    {X : Subgroup B} (hX : X ≠ ⊤) {C : Subgroup A}
    (hCH : C ≤ H) (hker : ∀ c : H, (c : A) ∈ C → φ c = 1) :
    (X.comap φ).map H.subtype ≠ H ∧ C ≤ (X.comap φ).map H.subtype := by
  constructor
  · intro hEq
    have hrel := relIndex_map_comap_g45jd1 φ hφ X
    have h1 : ((X.comap φ).map H.subtype).relIndex H = 1 := by
      rw [hEq, Subgroup.relIndex_self]
    rw [hrel] at h1
    exact hX (Subgroup.index_eq_one.mp h1)
  · intro c hc
    refine Subgroup.mem_map.mpr ⟨⟨c, hCH hc⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [hker ⟨c, hCH hc⟩ hc]
    exact X.one_mem

private theorem isSylowOf_inf_comap_g45jd1 {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] {p : ℕ} [Fact p.Prime] {φ : A →* B}
    (hφ : Function.Surjective φ) {S : Subgroup A} (hS : IsSylowOf p S ⊤)
    {X : Subgroup B} (hX : IsSylowOf p (S.map φ ⊓ X) X) :
    IsSylowOf p (S ⊓ X.comap φ) (X.comap φ) := by
  rw [isSylowOf_iff] at hX ⊢
  obtain ⟨-, -, hBidx⟩ := hX
  refine ⟨inf_le_right, hS.isPGroup.to_inf_left, ?_⟩
  set C : Subgroup A := X.comap φ with hCdef
  set B' : Subgroup B := S.map φ ⊓ X with hBdef
  set D : Subgroup A := S ⊓ C with hDdef
  set E : Subgroup A := (S ⊔ φ.ker) ⊓ C with hEdef
  have hOC : φ.ker ≤ C := by
    intro x hx
    rw [hCdef, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact X.one_mem
  have hcomap : B'.comap φ = E := by
    rw [hBdef, Subgroup.comap_inf, Subgroup.comap_map_eq, hEdef]
  have hmapC : C.map φ = X := Subgroup.map_comap_eq_self_of_surjective hφ X
  have hErel : E.relIndex C = B'.relIndex X := by
    have h := Subgroup.relIndex_comap (f := φ) (H := B') C
    rw [hcomap, hmapC] at h
    exact h
  have hEeq : E = D ⊔ φ.ker := by
    have hmod := Subgroup.inf_sup_assoc_of_le (H := S) (K := C) (N := φ.ker)
      Subgroup.le_normalizer_of_normal hOC
    rw [inf_comm C S] at hmod
    rw [hEdef, hDdef, inf_comm (S ⊔ φ.ker) C]
    exact hmod.symm
  have hDX : D ≤ E := by
    rw [hDdef, hEdef]
    exact le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hEC : E ≤ C := by rw [hEdef]; exact inf_le_right
  have hDC : D.relIndex C = D.relIndex E * E.relIndex C :=
    (Subgroup.relIndex_mul_relIndex (H := D) (K := E) (L := C) hDX hEC).symm
  have hprime1 : ¬ p ∣ D.relIndex E := by
    have h1 : D.relIndex E = D.relIndex φ.ker := by
      rw [hEeq, sup_comm]
      exact relIndex_sup_eq_relIndex_of_normal φ.ker D
    have h2 : D.relIndex φ.ker = (S ⊓ φ.ker).relIndex φ.ker := by
      rw [← Subgroup.inf_relIndex_right (H := D) (K := φ.ker)]
      congr 1
      rw [hDdef, inf_assoc, inf_comm C φ.ker, inf_eq_left.mpr hOC]
    have hSO : IsSylowOf p (S ⊓ φ.ker) φ.ker :=
      hS.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
    rw [h1, h2]
    exact (isSylowOf_iff.mp hSO).2.2
  have hprime2 : ¬ p ∣ E.relIndex C := by rw [hErel]; exact hBidx
  rw [hDC]
  exact Nat.Prime.not_dvd_mul Fact.out hprime1 hprime2

private theorem baum_le_map_comap_g45jd1 (h : GomiThm45Counterexample c G S)
    {ψ : ↥G →* ↥(autOn G (gomiV G))}
    (hbaum : ∀ (b : Ω) (hb : b ∈ baum S),
      ψ ⟨b, h.isSylowTwoOf.1 (C1GN.baum_le S hb)⟩ ∈
        (autOn (baum S) (gomiV G)).subgroupOf (autOn G (gomiV G)))
    {X : Subgroup ↥(autOn G (gomiV G))}
    (hKX : (autOn (baum S) (gomiV G)).subgroupOf (autOn G (gomiV G)) ≤ X) :
    baum S ≤ (X.comap ψ).map G.subtype := by
  intro b hb
  have hbG : b ∈ G := h.isSylowTwoOf.1 (C1GN.baum_le S hb)
  have hmemX : ψ ⟨b, hbG⟩ ∈ X := hKX (hbaum b hb)
  exact Subgroup.mem_map.mpr ⟨⟨b, hbG⟩, Subgroup.mem_comap.mpr hmemX, rfl⟩

private theorem isSylowOf_inf_map_comap_g45jd1 (h : GomiThm45Counterexample c G S)
    {ψ : ↥G →* ↥(autOn G (gomiV G))} (hψ : Function.Surjective ψ)
    (hSmap : (S.subgroupOf G).map ψ =
      (autOn S (gomiV G)).subgroupOf (autOn G (gomiV G)))
    {X : Subgroup ↥(autOn G (gomiV G))}
    (hSX : IsSylowOf 2 ((autOn S (gomiV G)).subgroupOf (autOn G (gomiV G)) ⊓ X) X) :
    IsSylowOf 2 (S ⊓ (X.comap ψ).map G.subtype) ((X.comap ψ).map G.subtype) := by
  have hSG : IsSylowOf 2 S G := isSylowOf_iff.mpr h.isSylowTwoOf
  have hS_top : IsSylowOf 2 (S.subgroupOf G) ⊤ := by
    refine (isSylowOf_map_subtype_iff (p := 2) G
      (A := S.subgroupOf G) (B := ⊤)).mp ?_
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.isSylowTwoOf.1,
      Subgroup.map_top, Subgroup.subtype_range] using hSG
  have hSX' : IsSylowOf 2 ((S.subgroupOf G).map ψ ⊓ X) X := by rwa [hSmap]
  have hD := isSylowOf_inf_comap_g45jd1 (p := 2) hψ hS_top hSX'
  have hD' : IsSylowOf 2 (((S.subgroupOf G) ⊓ X.comap ψ).map G.subtype)
      ((X.comap ψ).map G.subtype) :=
    (isSylowOf_map_subtype_iff (p := 2) G).mpr hD
  have hmapinf : ((S.subgroupOf G) ⊓ X.comap ψ).map G.subtype =
      S ⊓ (X.comap ψ).map G.subtype := by
    rw [Subgroup.map_inf _ _ _ G.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr h.isSylowTwoOf.1]
  simpa [hmapinf] using hD'

private theorem preimage_le_iSup_sylowMembers_g45jd1
    (h : GomiThm45Counterexample c G S)
    {ψ : ↥G →* ↥(autOn G (gomiV G))} (hψ : Function.Surjective ψ)
    (hSmap : (S.subgroupOf G).map ψ =
      (autOn S (gomiV G)).subgroupOf (autOn G (gomiV G)))
    (hker : ∀ x : ↥G, (x : Ω) ∈
      G ⊓ Subgroup.centralizer (gomiV G : Set Ω) → ψ x = 1)
    (hbaum : ∀ (b : Ω) (hb : b ∈ baum S),
      ψ ⟨b, h.isSylowTwoOf.1 (C1GN.baum_le S hb)⟩ ∈
        (autOn (baum S) (gomiV G)).subgroupOf (autOn G (gomiV G)))
    {X : Subgroup ↥(autOn G (gomiV G))} (hX : X ≠ ⊤)
    (hSX : IsSylowOf 2 ((autOn S (gomiV G)).subgroupOf (autOn G (gomiV G)) ⊓ X) X)
    (hKX : (autOn (baum S) (gomiV G)).subgroupOf (autOn G (gomiV G)) ≤ X) :
    (X.comap ψ).map G.subtype ≤
      ⨆ X' ∈ sylowMembers 2 (c.selection.family G) S, X' := by
  let Y : Subgroup Ω := (X.comap ψ).map G.subtype
  have hYG : Y ≤ G := Subgroup.map_subtype_le _
  obtain ⟨hYne, hC_le⟩ :=
    preimage_ne_top_and_le_g45jd1 ψ hψ hX inf_le_left hker
  have hQ_le : pCoreOf 2 G ≤ Y := by
    refine (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 G) ?_).trans hC_le
    exact Subgroup.le_centralizer_iff.mpr
      ((C1GN.omegaOneCenterOf_le_centerOf (pCoreOf 2 G)).trans inf_le_right)
  have hbaum_le : baum S ≤ Y := baum_le_map_comap_g45jd1 h hbaum hKX
  have hpCore_ne : pCoreOf 2 Y ≠ ⊥ := by
    have hQY : pCoreOf 2 G ≤ pCoreOf 2 Y :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQ_le
        (hYG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G)
    intro hbot
    exact GomiHyp43.pCoreOf_ne_bot h.hyp43
      (le_bot_iff.mp (hQY.trans (le_of_eq hbot)))
  have hIso : ¬ IsPIsolatedOver 2 Y ⊥ := by
    intro hiso
    have hle : pCoreOf 2 Y ≤ ⊥ :=
      IsPIsolatedOver.le_of_normal hiso (p := 2) IsPGroup.of_bot bot_le
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    exact hpCore_ne (le_bot_iff.mp hle)
  exact le_iSup_sylowMembers_of_isRegular h hYG
    (h.isRegular_of_lt (lt_of_le_of_ne hYG hYne)
      (sup_le (B6.thompsonJ_le_baum S |>.trans hbaum_le) hQ_le))
    hbaum_le hIso (isSylowOf_inf_map_comap_g45jd1 h hψ hSmap hSX)

private theorem exists_actionOn_setup_g45jd1 (h : GomiThm45Counterexample c G S) :
    ∃ ψ : ↥G →* ↥(autOn G (gomiV G)),
      Function.Surjective ψ ∧
      (S.subgroupOf G).map ψ = (autOn S (gomiV G)).subgroupOf (autOn G (gomiV G)) ∧
      (∀ x : ↥G, (x : Ω) ∈ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) → ψ x = 1) ∧
      (∀ (b : Ω) (hb : b ∈ baum S),
        ψ ⟨b, h.isSylowTwoOf.1 (C1GN.baum_le S hb)⟩ ∈
          (autOn (baum S) (gomiV G)).subgroupOf (autOn G (gomiV G))) := by
  let V : Subgroup Ω := gomiV G
  let Gbar : Subgroup (MulAut ↥V) := autOn G V
  let hG : G ≤ Subgroup.normalizer (V : Set Ω) := (gomiV_moduleSetting G).2
  let ψ : ↥G →* ↥Gbar :=
    (A4.actionOn V G hG).codRestrict Gbar (fun g => (A4.mem_autOn_iff hG).2 ⟨g, rfl⟩)
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨g, hg⟩ := (A4.mem_autOn_iff hG).1 a.2
    exact ⟨g, Subtype.ext hg⟩
  · exact map_codRestrict_eq_g45jd1 (L := Gbar) (A4.actionOn V G hG)
      (fun g => (A4.mem_autOn_iff hG).2 ⟨g, rfl⟩)
      (A4.autOn_mono h.isSylowTwoOf.1)
      (actionOn_map_subgroupOf_g45jd1 h.isSylowTwoOf.1)
  · rintro ⟨c, hcG⟩ ⟨-, hcC⟩
    apply Subtype.ext
    change A4.actionOn V G hG ⟨c, hcG⟩ = 1
    exact (A4.actionOn_eq_one_iff hG ⟨c, hcG⟩).2 hcC
  · intro b hb
    rw [Subgroup.mem_subgroupOf]
    refine (AutOn.mem_autOn_iff_exists (X := baum S) (V := V)).mpr
      ⟨b, hG (h.isSylowTwoOf.1 (C1GN.baum_le S hb)), hb, ?_⟩
    rfl

private theorem false_of_sup_eq_top_g45j (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb)
    {X₁ X₂ : Subgroup ↥(autOn G (gomiV G))} (hX₁ : X₁ ≠ ⊤) (hX₂ : X₂ ≠ ⊤)
    (hsup : X₁ ⊔ X₂ = ⊤)
    (hS₁ : IsSylowOf 2 ((autOn S (gomiV G)).subgroupOf (autOn G (gomiV G)) ⊓ X₁) X₁)
    (hS₂ : IsSylowOf 2 ((autOn S (gomiV G)).subgroupOf (autOn G (gomiV G)) ⊓ X₂) X₂)
    (hK : (autOn (baum S) (gomiV G)).subgroupOf (autOn G (gomiV G)) ≤ X₁ ⊓ X₂) : False := by
  obtain ⟨ψ, hψ, hSmap, hker, hbaum⟩ := h.exists_actionOn_setup_g45jd1
  have hcomap : X₁.comap ψ ⊔ X₂.comap ψ = ⊤ := by
    rw [Subgroup.comap_sup_eq ψ X₁ X₂ hψ, hsup, Subgroup.comap_top]
  let Y₁ : Subgroup Ω := (X₁.comap ψ).map G.subtype
  let Y₂ : Subgroup Ω := (X₂.comap ψ).map G.subtype
  have hsupY : Y₁ ⊔ Y₂ = G := by
    change (X₁.comap ψ).map G.subtype ⊔ (X₂.comap ψ).map G.subtype = G
    rw [← Subgroup.map_sup, hcomap, Subgroup.map_top, Subgroup.subtype_range]
  have hY₁le : Y₁ ≤ ⨆ X ∈ sylowMembers 2 (c.selection.family G) S, X :=
    preimage_le_iSup_sylowMembers_g45jd1 h hψ hSmap hker hbaum hX₁ hS₁
      (hK.trans inf_le_left)
  have hY₂le : Y₂ ≤ ⨆ X ∈ sylowMembers 2 (c.selection.family G) S, X :=
    preimage_le_iSup_sylowMembers_g45jd1 h hψ hSmap hker hbaum hX₂ hS₂
      (hK.trans inf_le_right)
  have hGle : G ≤ ⨆ X ∈ sylowMembers 2 (c.selection.family G) S, X := by
    have h := sup_le hY₁le hY₂le
    rwa [hsupY] at h
  have hiSup_le_G : (⨆ X ∈ sylowMembers 2 (c.selection.family G) S, X) ≤ G := by
    refine iSup_le fun X => iSup_le fun hXmem => ?_
    obtain ⟨P, hP, F, hF, rfl⟩ := hXmem.1
    exact inf_le_left
  exact h.iSup_sylowMembers_ne hL hg (le_antisymm hiSup_le_G hGle)

private theorem isSylowOf_inf_comap_mulEquiv_g45jd2 {Q Q' : Type*} [Group Q] [Group Q']
    [Finite Q] [Finite Q'] (π : Q ≃* Q') {p : ℕ} [Fact p.Prime] {B : Subgroup Q}
    {A : Subgroup Q'} (h : IsSylowOf p (B.map π.toMonoidHom ⊓ A) A) :
    IsSylowOf p (B ⊓ A.comap π.toMonoidHom) (A.comap π.toMonoidHom) := by
  refine (isSylowOf_map_mulEquiv π).mp ?_
  rwa [Subgroup.map_inf_eq _ _ _ π.injective,
    Subgroup.map_comap_eq_self_of_surjective π.surjective]

private theorem comap_sup_eq_top_and_ne_top_g45jd2 {Q Q' : Type*} [Group Q] [Group Q']
    (π : Q ≃* Q') {A₁ A₂ : Subgroup Q'} (h₁ : A₁ ≠ ⊤) (h₂ : A₂ ≠ ⊤)
    (hsup : A₁ ⊔ A₂ = ⊤) :
    A₁.comap π.toMonoidHom ⊔ A₂.comap π.toMonoidHom = ⊤ ∧
      A₁.comap π.toMonoidHom ≠ ⊤ ∧ A₂.comap π.toMonoidHom ≠ ⊤ := by
  have hne : ∀ A : Subgroup Q', A ≠ ⊤ → A.comap π.toMonoidHom ≠ ⊤ := by
    intro A hA h
    apply hA
    have h' := congrArg (Subgroup.map π.toMonoidHom) h
    rwa [Subgroup.map_comap_eq_self_of_surjective π.surjective, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr π.surjective] at h'
  have hle : ∀ A : Subgroup Q', A ≤ π.toMonoidHom.range := by
    intro A
    rw [MonoidHom.range_eq_top.mpr π.surjective]
    exact le_top
  refine ⟨?_, hne A₁ h₁, hne A₂ h₂⟩
  rw [Subgroup.comap_sup_eq_of_le_range (f := π.toMonoidHom) (hle A₁) (hle A₂), hsup,
    Subgroup.comap_top]

private theorem two_pow_add_one_g45jd2 {m : ℕ} (hm : 2 ≤ m) :
    2 * (2 ^ (m - 1) + 1) - 1 = 2 ^ m + 1 ∧ Odd (2 * (2 ^ (m - 1) + 1) - 1) ∧
      5 ≤ 2 * (2 ^ (m - 1) + 1) - 1 ∧ 3 ≤ 2 ^ (m - 1) + 1 := by
  have hpow : 2 * 2 ^ (m - 1) = 2 ^ m := by
    rw [mul_comm, ← pow_succ, show m - 1 + 1 = m by omega]
  have h3 : 3 ≤ 2 ^ (m - 1) + 1 := by
    have h2 : 2 ≤ 2 ^ (m - 1) := by
      have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 1 ≤ m - 1)
      simpa using h
    omega
  have hdim : 2 * (2 ^ (m - 1) + 1) - 1 = 2 ^ m + 1 := by
    rw [Nat.mul_add, Nat.mul_one, hpow]
    omega
  refine ⟨hdim, ?_, ?_, h3⟩
  · rw [hdim]
    exact ⟨2 ^ (m - 1), by rw [← hpow]⟩
  · rw [hdim]
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    norm_num at h4 ⊢
    omega

private theorem exists_perm_of_isAlt_g45jd2 (h : GomiThm45Counterexample c G S)
    (h37 : GomiFact37Four) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hn : autOn G (gomiV G) ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))))
    (hC : autOn G (gomiV G) ⊓ Subgroup.centralizer (Lb : Set (MulAut ↥(gomiV G))) = ⊥)
    {m : ℕ} (hm : 2 ≤ m) (hAlt : IsAlt ↥Lb (2 ^ m + 1))
    (hmod : (FFModel.altDn (2 ^ m + 1)).Realizes Lb (commV Lb) (gomiWXKer Lb)) :
    ∃ φ : ↥(autOn G (gomiV G)) ≃* Equiv.Perm (Fin (2 * (2 ^ (m - 1) + 1) - 1)),
      gomiCSP (autOn S (gomiV G)) Lb =
        Subgroup.closure {s | ∃ hs : s ∈ autOn G (gomiV G), s ∈ autOn S (gomiV G) ∧
          (φ ⟨s, hs⟩).IsSwap} ∧
      IsSylowOf 2 (((autOn S (gomiV G)).subgroupOf (autOn G (gomiV G))).map
        φ.toMonoidHom) ⊤ := by
  obtain ⟨hdim, -, -, h3⟩ := two_pow_add_one_g45jd2 hm
  have hV2 : ∀ w : ↥(gomiV G), w ^ 2 = 1 := fun w =>
    Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)
  have hsub : (Lb.subgroupOf (autOn G (gomiV G))).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mpr hn).isSubnormal
  have hAlt' : IsAlt ↥Lb (2 * (2 ^ (m - 1) + 1) - 1) := by
    rw [hdim]
    exact hAlt
  have hmod' : (FFModel.altDn (2 * (2 ^ (m - 1) + 1) - 1)).Realizes Lb (commV Lb)
      (gomiWXKer Lb) := by
    rw [hdim]
    exact hmod
  obtain ⟨φ, hφ⟩ := h37 ↥(gomiV G) hV2 (autOn G (gomiV G)) (autOn S (gomiV G)) Lb
    (2 ^ (m - 1) + 1) h3 (pset_nonempty h) (isSylowIn_autOn h) hL.le hsub hAlt' hC hmod'
  refine ⟨φ, hφ, ?_⟩
  have hSbTop : IsSylowOf 2
      ((autOn S (gomiV G)).subgroupOf (autOn G (gomiV G))) ⊤ := by
    refine (isSylowOf_map_subtype_iff (autOn G (gomiV G))).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (isSylowIn_autOn h).le,
      Subgroup.map_top, Subgroup.range_subtype]
    exact isSylowOf_iff.mpr (isSylowIn_autOn h)
  have hP := (isSylowOf_map_mulEquiv φ).mpr hSbTop
  rwa [Subgroup.map_top, MonoidHom.range_eq_top.mpr φ.surjective] at hP

omit [Finite Ω] in
private theorem gomiCSP_le_map_inf_g45jd2 {Lb : Subgroup (MulAut ↥(gomiV G))}
    {n : ℕ} {φ : ↥(autOn G (gomiV G)) ≃* Equiv.Perm (Fin n)}
    (hφ : gomiCSP (autOn S (gomiV G)) Lb =
      Subgroup.closure {s | ∃ hs : s ∈ autOn G (gomiV G), s ∈ autOn S (gomiV G) ∧
        (φ ⟨s, hs⟩).IsSwap})
    {X₁ X₂ : Subgroup (Equiv.Perm (Fin n))}
    (hswap : ∀ τ ∈ ((autOn S (gomiV G)).subgroupOf (autOn G (gomiV G))).map
      φ.toMonoidHom, τ.IsSwap → τ ∈ X₁ ⊓ X₂) :
    gomiCSP (autOn S (gomiV G)) Lb ≤
      (X₁.comap φ.toMonoidHom ⊓ X₂.comap φ.toMonoidHom).map
        (autOn G (gomiV G)).subtype := by
  rw [hφ, Subgroup.closure_le]
  rintro s ⟨hsY, hsSb, hsw⟩
  have hmemP : φ ⟨s, hsY⟩ ∈
      ((autOn S (gomiV G)).subgroupOf (autOn G (gomiV G))).map φ.toMonoidHom :=
    Subgroup.mem_map_of_mem φ.toMonoidHom (Subgroup.mem_subgroupOf.mpr hsSb)
  have hmemX : φ ⟨s, hsY⟩ ∈ X₁ ⊓ X₂ := hswap _ hmemP hsw
  have hmemZ : (⟨s, hsY⟩ : ↥(autOn G (gomiV G))) ∈
      X₁.comap φ.toMonoidHom ⊓ X₂.comap φ.toMonoidHom :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mpr hmemX.1, Subgroup.mem_comap.mpr hmemX.2⟩
  exact Subgroup.mem_map_of_mem (autOn G (gomiV G)).subtype hmemZ

private theorem subgroupOf_le_inf_g45jd2 (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    {Z₁ Z₂ : Subgroup ↥(autOn G (gomiV G))}
    (hZ : gomiCSP (autOn S (gomiV G)) Lb ≤
      (Z₁ ⊓ Z₂).map (autOn G (gomiV G)).subtype) :
    (autOn (baum S) (gomiV G)).subgroupOf (autOn G (gomiV G)) ≤ Z₁ ⊓ Z₂ := by
  have hKY : autOn (baum S) (gomiV G) ≤ autOn G (gomiV G) :=
    (autOn_baum_le_gomiCSP_g45j h Lb).trans (inf_le_left.trans (isSylowIn_autOn h).le)
  rw [← Subgroup.map_subtype_le_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hKY]
  exact (autOn_baum_le_gomiCSP_g45j h Lb).trans hZ

private theorem false_of_isAlt_g45j (h : GomiThm45Counterexample c G S) (h37 : GomiFact37Four)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hn : autOn G (gomiV G) ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))))
    (hC : autOn G (gomiV G) ⊓ Subgroup.centralizer (Lb : Set (MulAut ↥(gomiV G))) = ⊥)
    {m : ℕ} (hm : 2 ≤ m) (hAlt : IsAlt ↥Lb (2 ^ m + 1))
    (hmod : (FFModel.altDn (2 ^ m + 1)).Realizes Lb (commV Lb) (gomiWXKer Lb)) : False := by
  obtain ⟨-, hodd, h5, -⟩ := two_pow_add_one_g45jd2 hm
  obtain ⟨φ, hφ, hP⟩ := exists_perm_of_isAlt_g45jd2 h h37 hL hn hC hm hAlt hmod
  obtain ⟨X₁, X₂, hX₁, hX₂, hsup, hS₁, hS₂, hswap⟩ :=
    CFSG.GroupTheory.PermSylowTwo.exists_sup_eq_top_of_isSylowOf
      (n := 2 * (2 ^ (m - 1) + 1) - 1) hodd h5 hP
  obtain ⟨hsup', hZ₁, hZ₂⟩ := comap_sup_eq_top_and_ne_top_g45jd2 φ hX₁ hX₂ hsup
  exact false_of_sup_eq_top_g45j h hL (Or.inr ⟨m, hm, hAlt, hmod⟩) hZ₁ hZ₂ hsup'
    (isSylowOf_inf_comap_mulEquiv_g45jd2 φ hS₁)
    (isSylowOf_inf_comap_mulEquiv_g45jd2 φ hS₂)
    (subgroupOf_le_inf_g45jd2 h (gomiCSP_le_map_inf_g45jd2 hφ hswap))

private theorem eq_one_of_natAct_eq_g45je {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {γ : ↥Γ}
    (h : ∀ x : Multiplicative (ι → K), natAct Γ γ x = x) : γ = 1 := by
  have hmat : (((γ : ↥Γ) : GL ι K) : Matrix ι ι K) = 1 := by
    apply Matrix.ext_of_mulVec_single (N := (1 : Matrix ι ι K))
    intro i
    have h' : ((((γ : ↥Γ) : GL ι K) : Matrix ι ι K)).mulVec (Pi.single i 1) =
        Pi.single i 1 := by
      simpa only [natAct, toAdd_ofAdd] using
        congrArg Multiplicative.toAdd (h (Multiplicative.ofAdd (Pi.single i 1)))
    have hcol : (Matrix.col (1 : Matrix ι ι K) i) = Pi.single i 1 := by
      funext j
      simp [Matrix.col_apply, Matrix.one_apply, Pi.single_apply]
    simpa [Matrix.one_mulVec, hcol] using h'
  refine Subtype.ext ?_
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simpa using congrFun (congrFun hmat i) j

private theorem natAct_eq_of_realizesVia_g45je {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : ↥Γ →* ↥H}
    (hπ : (FFModel.nat Γ).RealizesVia H U Z π) {γ : ↥Γ} (hγ : π γ = 1) :
    ∀ x : Multiplicative (ι → K), natAct Γ γ x = x := by
  let R : CFSG.Quasithin.SzN15.NatReal H U Z Γ π :=
    CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβs, -, hβe⟩ := R.exists_β
  intro x
  obtain ⟨u, hu⟩ := hβs x
  have hmem : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := R.U_inv (π γ) u u.2
  have h1 : β ⟨((π γ : ↥H) : MulAut V) (u : V), hmem⟩ = natAct Γ γ (β u) :=
    hβe γ u hmem
  have hsubu : (⟨((π γ : ↥H) : MulAut V) (u : V), hmem⟩ : ↥U) = u := by
    apply Subtype.ext
    have hone : ((π γ : ↥H) : MulAut V) = 1 := by rw [hγ]; rfl
    simp [hone]
  rw [hsubu] at h1
  have h2 : β u = natAct Γ γ (β u) := by simpa using h1
  rw [hu] at h2
  exact h2.symm

private theorem natReal_injective_g45je {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : ↥Γ →* ↥H}
    (hπ : (FFModel.nat Γ).RealizesVia H U Z π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  exact eq_one_of_natAct_eq_g45je (natAct_eq_of_realizesVia_g45je hπ hγ)

private theorem exists_commEquiv_g45je {X : Type} [Group X] {V G : Subgroup X}
    [hVcomm : IsMulCommutative ↥V]
    (hVG : G ≤ Subgroup.normalizer (V : Set X)) :
    ∃ θ : ↥(commV (autOn G V)) ≃* ↥(⁅V, G⁆ : Subgroup X),
      (∀ u, ((θ u : ↥(⁅V, G⁆ : Subgroup X)) : X) = ((u : ↥V) : X)) ∧
      (∀ x, (((θ.symm x : ↥(commV (autOn G V))) : ↥V) : X) = (x : X)) := by
  have hWV : ⁅V, G⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hVG
  let θ : ↥(commV (autOn G V)) ≃* ↥(⁅V, G⁆ : Subgroup X) :=
    (MulEquiv.subgroupCongr (CFSG.Quasithin.AutOn.commV_autOn_eq hVG)).trans
      (Subgroup.subgroupOfEquivOfLe hWV)
  have hcoe : ∀ u, ((θ u : ↥(⁅V, G⁆ : Subgroup X)) : X) = ((u : ↥V) : X) := fun _ => rfl
  refine ⟨θ, hcoe, ?_⟩
  intro x
  have h := hcoe (θ.symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

private theorem transfer_ker_g45je {X : Type} [Group X] {V G : Subgroup X}
    (hVG : G ≤ Subgroup.normalizer (V : Set X)) [hVcomm : IsMulCommutative ↥V]
    {K : Type} [Field K]
    {β₀ : ↥(commV (autOn G V)) →* Multiplicative (Fin 2 → K)}
    (hβ₀ker : ∀ u, β₀ u = 1 ↔ (u : ↥V) ∈ gomiWXKer (autOn G V))
    {θ : ↥(commV (autOn G V)) ≃* ↥(⁅V, G⁆ : Subgroup X)}
    (hθsymm : ∀ x, (((θ.symm x : ↥(commV (autOn G V))) : ↥V) : X) = (x : X))
    {β : ↥(⁅V, G⁆ : Subgroup X) →* Multiplicative (Fin 2 → K)}
    (hβ : ∀ x, β x = β₀ (θ.symm x)) :
    β.ker = ((⁅V, G⁆ : Subgroup X) ⊓ Subgroup.centralizer (G : Set X)).subgroupOf
      (⁅V, G⁆ : Subgroup X) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hx
    have hxZ : (((θ.symm x : ↥(commV (autOn G V))) : ↥V)) ∈ gomiWXKer (autOn G V) :=
      (hβ₀ker (θ.symm x)).1 (by rw [← hβ x]; exact hx)
    have hxfix : (((θ.symm x : ↥(commV (autOn G V))) : ↥V)) ∈ fixV (autOn G V) :=
      (Subgroup.mem_inf.1 hxZ).2
    have hxfix' : (((θ.symm x : ↥(commV (autOn G V))) : ↥V)) ∈
        (Subgroup.centralizer (G : Set X)).subgroupOf V := by
      rwa [CFSG.Quasithin.AutOn.fixV_autOn_eq hVG] at hxfix
    have hxc : ((((θ.symm x : ↥(commV (autOn G V))) : ↥V)) : X) ∈
        Subgroup.centralizer (G : Set X) := (Subgroup.mem_subgroupOf).1 hxfix'
    exact ⟨x.2, by simpa [hθsymm x] using hxc⟩
  · rintro ⟨-, hxc⟩
    rw [hβ x]
    apply (hβ₀ker (θ.symm x)).2
    refine Subgroup.mem_inf.2 ⟨(θ.symm x).2, ?_⟩
    rw [CFSG.Quasithin.AutOn.fixV_autOn_eq hVG, Subgroup.mem_subgroupOf]
    simpa [hθsymm x] using hxc

private theorem transfer_act_g45je {X : Type} [Group X] {V G : Subgroup X}
    (hVG : G ≤ Subgroup.normalizer (V : Set X)) [hVcomm : IsMulCommutative ↥V]
    {K : Type} [Field K]
    {π : ↥(StatedSL 2 K) →* ↥(autOn G V)}
    (hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia (autOn G V) (commV (autOn G V))
      (gomiWXKer (autOn G V)) π)
    {β₀ : ↥(commV (autOn G V)) →* Multiplicative (Fin 2 → K)}
    (hβ₀act : ∀ (γ : ↥(StatedSL 2 K)) (u : ↥(commV (autOn G V)))
      (hu : ((π γ : ↥(autOn G V)) : MulAut ↥V) (u : ↥V) ∈ commV (autOn G V)),
      β₀ ⟨((π γ : ↥(autOn G V)) : MulAut ↥V) (u : ↥V), hu⟩ =
        natAct (StatedSL 2 K) γ (β₀ u))
    {θ : ↥(commV (autOn G V)) ≃* ↥(⁅V, G⁆ : Subgroup X)}
    (hθsymm : ∀ x, (((θ.symm x : ↥(commV (autOn G V))) : ↥V) : X) = (x : X))
    {β : ↥(⁅V, G⁆ : Subgroup X) →* Multiplicative (Fin 2 → K)}
    (hβ : ∀ x, β x = β₀ (θ.symm x))
    {ε : G →* ↥(StatedSL 2 K)}
    (hε : ∀ g, ((π (ε g) : ↥(autOn G V)) : MulAut ↥V) = A4.actionOn V G hVG g) :
    ∀ (g : G) (u v : ↥(⁅V, G⁆ : Subgroup X)), (v : X) = g * u * g⁻¹ →
      Multiplicative.toAdd (β v) =
        ((((ε g : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).mulVec
          (Multiplicative.toAdd (β u)) := by
  intro g u v huv
  let R : CFSG.Quasithin.SzN15.NatReal (autOn G V) (commV (autOn G V))
      (gomiWXKer (autOn G V)) (StatedSL 2 K) π :=
    CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  have hmem : ((π (ε g) : ↥(autOn G V)) : MulAut ↥V)
      (((θ.symm u : ↥(commV (autOn G V))) : ↥V)) ∈ commV (autOn G V) :=
    R.U_inv (π (ε g)) (θ.symm u) (θ.symm u).2
  have h1 : β₀ ⟨((π (ε g) : ↥(autOn G V)) : MulAut ↥V)
        (((θ.symm u : ↥(commV (autOn G V))) : ↥V)), hmem⟩ =
      natAct (StatedSL 2 K) (ε g) (β₀ (θ.symm u)) := hβ₀act (ε g) (θ.symm u) hmem
  have hsub : (⟨((π (ε g) : ↥(autOn G V)) : MulAut ↥V)
        (((θ.symm u : ↥(commV (autOn G V))) : ↥V)), hmem⟩ :
      ↥(commV (autOn G V))) = θ.symm v := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp only
    rw [hε, A4.actionOn_apply_coe, hθsymm u, hθsymm v]
    exact huv.symm
  rw [hsub] at h1
  rw [hβ v, hβ u, h1]
  simp [natAct]

private theorem alpha_of_action_g45je {X : Type} [Group X] {V G : Subgroup X}
    (hVG : G ≤ Subgroup.normalizer (V : Set X))
    {K : Type} [Field K] {π : ↥(StatedSL 2 K) →* ↥(autOn G V)}
    (hπinj : Function.Injective π)
    {ε : G →* ↥(StatedSL 2 K)}
    (hε : ∀ g, ((π (ε g) : ↥(autOn G V)) : MulAut ↥V) = A4.actionOn V G hVG g) :
    ∃ α : G →* Matrix.SpecialLinearGroup (Fin 2) K, Function.Surjective α ∧
      α.ker = (Subgroup.centralizer (V : Set X)).subgroupOf G ∧
      ∀ g, ((α g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (((ε g : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  let e₂ : ↥(StatedSL 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  let α : G →* Matrix.SpecialLinearGroup (Fin 2) K := e₂.toMonoidHom.comp ε
  have hεsurj : Function.Surjective ε := by
    intro γ
    obtain ⟨g, hg⟩ := (A4.mem_autOn_iff hVG).1 (π γ).2
    refine ⟨g, hπinj ?_⟩
    apply Subtype.ext
    rw [hε]
    exact hg
  have hαsurj : Function.Surjective α := by
    intro y
    obtain ⟨x, hx⟩ := e₂.surjective y
    obtain ⟨g, hg⟩ := hεsurj x
    exact ⟨g, by rw [show α g = e₂ (ε g) from rfl, hg, hx]⟩
  refine ⟨α, hαsurj, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ e₂.toMonoidHom e₂.injective]
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hiff : ε g = 1 ↔ (A4.actionOn V G hVG) g = 1 := by
      constructor
      · intro h
        rw [← hε, h, map_one π]
        simp
      · intro h
        apply hπinj
        rw [map_one]
        exact Subtype.ext (by rw [hε, h]; rfl)
    rw [hiff]
    exact A4.actionOn_eq_one_iff hVG g
  · intro g
    have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 2 K (e₂ (ε g))
    rw [show CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K (e₂ (ε g)) = ε g from
      MulEquiv.symm_apply_apply e₂ (ε g)] at h
    exact h.symm

private theorem beta_of_action_g45je {X : Type} [Group X] {V G : Subgroup X}
    (hVG : G ≤ Subgroup.normalizer (V : Set X)) [hVcomm : IsMulCommutative ↥V]
    {K : Type} [Field K]
    {π : ↥(StatedSL 2 K) →* ↥(autOn G V)}
    (hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia (autOn G V) (commV (autOn G V))
      (gomiWXKer (autOn G V)) π)
    {ε : G →* ↥(StatedSL 2 K)}
    (hε : ∀ g, ((π (ε g) : ↥(autOn G V)) : MulAut ↥V) = A4.actionOn V G hVG g) :
    ∃ β : ↥(⁅V, G⁆ : Subgroup X) →* Multiplicative (Fin 2 → K), Function.Surjective β ∧
      β.ker = ((⁅V, G⁆ : Subgroup X) ⊓ Subgroup.centralizer (G : Set X)).subgroupOf
        (⁅V, G⁆ : Subgroup X) ∧
      ∀ (g : G) (u v : ↥(⁅V, G⁆ : Subgroup X)), (v : X) = g * u * g⁻¹ →
        Multiplicative.toAdd (β v) =
          ((((ε g : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).mulVec
            (Multiplicative.toAdd (β u)) := by
  let U : Subgroup ↥V := commV (autOn G V)
  let W : Subgroup X := ⁅V, G⁆
  let R : CFSG.Quasithin.SzN15.NatReal (autOn G V) U (gomiWXKer (autOn G V))
      (StatedSL 2 K) π := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β₀, hβ₀surj, hβ₀ker, hβ₀act⟩ := R.exists_β
  obtain ⟨θ, -, hθsymm⟩ := exists_commEquiv_g45je (V := V) (G := G) hVG
  let β : ↥W →* Multiplicative (Fin 2 → K) := β₀.comp θ.symm.toMonoidHom
  have hβ : ∀ x, β x = β₀ (θ.symm x) := fun _ => rfl
  have hβsurj : Function.Surjective β := hβ₀surj.comp θ.symm.surjective
  have hβker : β.ker = (W ⊓ Subgroup.centralizer (G : Set X)).subgroupOf W :=
    transfer_ker_g45je hVG hβ₀ker hθsymm hβ
  have hβe := transfer_act_g45je hVG hπ hβ₀act hθsymm hβ hε
  exact ⟨β, hβsurj, hβker, hβe⟩

private theorem natural_core_g45je {X : Type} [Group X] {G V : Subgroup X}
    (hVG : G ≤ Subgroup.normalizer (V : Set X)) [hVcomm : IsMulCommutative ↥V]
    {K : Type} [field : Field K] [finite : Finite K] {m : ℕ}
    (hKcard : Nat.card K = 2 ^ m)
    {π : ↥(StatedSL 2 K) →* ↥(autOn G V)}
    (hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia (autOn G V) (commV (autOn G V))
      (gomiWXKer (autOn G V)) π) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ m ∧
      ∃ α : G →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective α ∧
        α.ker = (Subgroup.centralizer (V : Set X)).subgroupOf G ∧
      ∃ β : ↥(⁅V, G⁆ : Subgroup X) →* Multiplicative (Fin 2 → F), Function.Surjective β ∧
        β.ker = ((⁅V, G⁆ : Subgroup X) ⊓ Subgroup.centralizer (G : Set X)).subgroupOf
          (⁅V, G⁆ : Subgroup X) ∧
        ∀ (g : G) (u v : ↥(⁅V, G⁆ : Subgroup X)), (v : X) = g * u * g⁻¹ →
          Multiplicative.toAdd (β v) =
            (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)) := by
  have hπinj : Function.Injective π := natReal_injective_g45je hπ
  let eπ : ↥(StatedSL 2 K) ≃* ↥(autOn G V) := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  let ψ₀ : G →* MulAut ↥V := A4.actionOn V G hVG
  have hψ₀mem : ∀ g : G, ψ₀ g ∈ autOn G V := fun g => (A4.mem_autOn_iff hVG).2 ⟨g, rfl⟩
  let ψ : G →* ↥(autOn G V) := ψ₀.codRestrict (autOn G V) hψ₀mem
  let ε : G →* ↥(StatedSL 2 K) := eπ.symm.toMonoidHom.comp ψ
  have hε : ∀ g, ((π (ε g) : ↥(autOn G V)) : MulAut ↥V) = A4.actionOn V G hVG g := by
    intro g
    exact congrArg (fun x : ↥(autOn G V) => (x : MulAut ↥V)) (eπ.apply_symm_apply (ψ g))
  obtain ⟨α, hαsurj, hαker, hαmat⟩ := alpha_of_action_g45je hVG hπinj hε
  obtain ⟨β, hβsurj, hβker, hβe⟩ := beta_of_action_g45je hVG hπ hε
  have hβeα : ∀ (g : G) (u v : ↥(⁅V, G⁆ : Subgroup X)), (v : X) = g * u * g⁻¹ →
      Multiplicative.toAdd (β v) =
        (α g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u)) := by
    intro g u v huv
    rw [hβe g u v huv, hαmat g]
  have hcard : @Fintype.card K (Fintype.ofFinite K) = 2 ^ m := by
    rw [← @Nat.card_eq_fintype_card K (Fintype.ofFinite K)]
    exact hKcard
  exact ⟨K, field, Fintype.ofFinite K, hcard, α, hαsurj, hαker, β, hβsurj, hβker, hβeα⟩

omit [Finite Ω] in
private theorem natural_of_autOn_g45j {m : ℕ}
    (hnat : BinaryNaturalSL (autOn G (gomiV G)) (commV (autOn G (gomiV G)))
      (gomiWXKer (autOn G (gomiV G))) 2 m) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ m ∧
      ∃ α : G →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective α ∧
        α.ker = (Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf G ∧
      ∃ β : ↥(⁅gomiV G, G⁆ : Subgroup Ω) →* Multiplicative (Fin 2 → F), Function.Surjective β ∧
        β.ker = (⁅gomiV G, G⁆ ⊓ Subgroup.centralizer (G : Set Ω)).subgroupOf ⁅gomiV G, G⁆ ∧
        ∀ (g : G) (u v : ↥(⁅gomiV G, G⁆ : Subgroup Ω)), (v : Ω) = g * u * g⁻¹ →
          Multiplicative.toAdd (β v) =
            (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)) := by
  obtain ⟨K, hKfield, hKfinite, hKcard, π, hπ⟩ := hnat
  let π' : ↥(StatedSL 2 K) →* ↥(autOn G (gomiV G)) := π
  have hπ' : (FFModel.nat (StatedSL 2 K)).RealizesVia (autOn G (gomiV G))
      (commV (autOn G (gomiV G))) (gomiWXKer (autOn G (gomiV G))) π' := hπ
  exact natural_core_g45je (V := gomiV G) (hVG := (gomiV_moduleSetting G).2)
    (hVcomm := (gomiV_moduleSetting G).1.1) (field := hKfield) (finite := hKfinite)
    hKcard hπ'

private theorem gomiCSP_le_normalizer_of_component_g45j (h : GomiThm45Counterexample c G S)
    (h37 : GomiFact37OneCSP) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb)
    (hLle1 : Lb ≤ gomiGstar1 (autOn G (gomiV G)))
    (hcomp : CFSG.IsComponent (Lb.subgroupOf (gomiGstar1 (autOn G (gomiV G)))))
    (hg : IsGomiStepG Lb) :
    gomiCSP (autOn S (gomiV G)) Lb ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) := by
  obtain ⟨hHyp, hne, hnat⟩ := h.gomiFact37Hyp_of_isGomiStepG hL hLle1 hcomp hg
  exact h37 ↥(gomiV G) (fun w => Subtype.ext ((gomiV_moduleSetting G).1.2 w w.2)) _ _ _
    hHyp hne hnat

theorem natural_autOn (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    (h32 : GomiFact32) (h37 : GomiFact37OneCSP) (h373 : GomiFact37Three)
    (h374 : GomiFact37Four) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb)
    (hi : G ≤ conjClosure (baum S) G) :
    ∃ m : ℕ, 1 ≤ m ∧ IsSLn ↥(autOn G (gomiV G)) 2 m ∧
      BinaryNaturalSL (autOn G (gomiV G)) (commV (autOn G (gomiV G)))
        (gomiWXKer (autOn G (gomiV G))) 2 m := by
  have hK : autOn (baum S) (gomiV G) ≤ Subgroup.normalizer (Lb : Set (MulAut ↥(gomiV G))) := by
    refine (autOn_baum_le_gomiCSP_g45j h Lb).trans ?_
    rcases hL.mem_or with ⟨hP0, hN⟩ | ⟨-, hLle1, hcomp⟩
    · exact gomiCSP_le_normalizer_of_mem_gomiNSet_g45j h h31 h32 hL hP0 hN
    · exact gomiCSP_le_normalizer_of_component_g45j h h37 hL hLle1 hcomp hg
  have hn := le_normalizer_of_autOn_baum_le_g45j h hL hi hK
  have hC := inf_centralizer_eq_bot_g45j h hL hn hg
  rcases hg with ⟨m, hm, hSLn, hnat⟩ | ⟨m, hm, hAlt, hmod⟩
  · obtain rfl := eq_autOn_of_isSLn_g45j h h373 hL hi hn hC hm hSLn hnat
    exact ⟨m, hm, hSLn, hnat⟩
  · exact (false_of_isAlt_g45j h h374 hL hn hC hm hAlt hmod).elim

theorem natural (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    (h32 : GomiFact32) (h37 : GomiFact37OneCSP) (h373 : GomiFact37Three)
    (h374 : GomiFact37Four) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb)
    (hi : G ≤ conjClosure (baum S) G) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ m ∧
      ∃ α : G →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective α ∧
        α.ker = (Subgroup.centralizer (gomiV G : Set Ω)).subgroupOf G ∧
      ∃ β : ↥(⁅gomiV G, G⁆ : Subgroup Ω) →* Multiplicative (Fin 2 → F), Function.Surjective β ∧
        β.ker = (⁅gomiV G, G⁆ ⊓ Subgroup.centralizer (G : Set Ω)).subgroupOf ⁅gomiV G, G⁆ ∧
        ∀ (g : G) (u v : ↥(⁅gomiV G, G⁆ : Subgroup Ω)), (v : Ω) = g * u * g⁻¹ →
          Multiplicative.toAdd (β v) =
            (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)) := by
  obtain ⟨m, -, -, hnat⟩ := h.natural_autOn h31 h32 h37 h373 h374 hL hg hi
  exact ⟨m, natural_of_autOn_g45j hnat⟩

private theorem exists_minimal_g45k {F : Type} [Field F] {D : Type} [Group D] [Finite D]
    {G J : Subgroup D} {α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hαs : Function.Surjective α) :
    ∃ X : Subgroup ↥G, J.subgroupOf G ≤ Subgroup.normalizer (X : Set ↥G) ∧
      X.map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F) ∧
      ∀ Y : Subgroup ↥G, J.subgroupOf G ≤ Subgroup.normalizer (Y : Set ↥G) →
        Y.map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F) → Y ≤ X → X ≤ Y := by
  have hKnormal : (commutator (Matrix.SpecialLinearGroup (Fin 2) F)).Normal :=
    Subgroup.commutator_normal ⊤ ⊤
  have hKmem : ((commutator (Matrix.SpecialLinearGroup (Fin 2) F)).comap α) ∈
      {Y : Subgroup ↥G | J.subgroupOf G ≤ Subgroup.normalizer (Y : Set ↥G) ∧
        Y.map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F)} := by
    refine ⟨?_, ?_⟩
    · intro j _
      have hN : ((commutator (Matrix.SpecialLinearGroup (Fin 2) F)).comap α).Normal :=
        hKnormal.comap α
      rw [Subgroup.normalizer_eq_top (h := hN)]
      exact Subgroup.mem_top j
    · rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hαs]
      exact top_inf_eq _
  obtain ⟨X, hXmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun Y : Subgroup ↥G => J.subgroupOf G ≤ Subgroup.normalizer (Y : Set ↥G) ∧
      Y.map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F))
    (fun Y => Nat.card Y) ⟨_, hKmem⟩
  refine ⟨X, hXmin.prop.1, hXmin.prop.2, fun Y hY1 hY2 hYX => ?_⟩
  by_contra hnot
  have hlt : Y < X := lt_of_le_of_ne hYX fun heq => hnot heq.ge
  exact hXmin.not_lt ⟨hY1, hY2⟩ (Set.Finite.card_lt_card (Set.toFinite (X : Set ↥G)) hlt)

private theorem minimal_props_g45k {F : Type} [Field F] [Fintype F] {D : Type} [Group D]
    [Finite D] {G J : Subgroup D} {α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F}
    {X : Subgroup ↥G} {m : ℕ} (hcard : Fintype.card F = 2 ^ m)
    (hXJ : J.subgroupOf G ≤ Subgroup.normalizer (X : Set ↥G))
    (hXK : X.map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F))
    (hmin : ∀ Y : Subgroup ↥G, J.subgroupOf G ≤ Subgroup.normalizer (Y : Set ↥G) →
      Y.map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F) → Y ≤ X → X ≤ Y)
    (hJp : IsPGroup 2 ((J.subgroupOf G).map α)) (hJne : (J.subgroupOf G).map α ≠ ⊥) :
    X = ⁅X, J.subgroupOf G⁆ ∧ twoResidual X = X := by
  let Y : Subgroup ↥G := ⁅X, J.subgroupOf G⁆
  have hcomm : J.subgroupOf G ≤ Subgroup.normalizer (Y : Set ↥G) :=
    Subgroup.normalizer_commutator_ge_right X (J.subgroupOf G)
  have hmap : Y.map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.map_commutator, hXK]
    exact SL2CharTwo.commutator_commutator_eq_of_isPGroup hcard hJp hJne
  have hle : Y ≤ X := (Subgroup.le_normalizer_iff_commutator_le_left).mp hXJ
  have h1 : X = Y := le_antisymm (hmin _ hcomm hmap hle) hle
  have h2map : (twoResidual X).map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [E1.map_twoResidual α X, hXK]
    exact SL2CharTwo.twoResidual_commutator_eq hcard
  have h2 : twoResidual X = X := le_antisymm (twoResidual_le X)
    (hmin _ (hXJ.trans (CFSG.Quasithin.C126.A5.normalizer_le_normalizer_twoResidual X)) h2map
      (twoResidual_le X))
  exact ⟨h1, h2⟩

private theorem map_subtype_props_g45k {D : Type} [Group D] [Finite D]
    {G J : Subgroup D} {X : Subgroup ↥G} (hJG : J ≤ G)
    (hXcomm : X = ⁅X, J.subgroupOf G⁆) (hXtwo : twoResidual X = X) :
    ∃ XΩ : Subgroup D, XΩ ≤ G ∧ XΩ.subgroupOf G = X ∧ XΩ = ⁅XΩ, J⁆ ∧ twoResidual XΩ = XΩ := by
  refine ⟨X.map G.subtype, Subgroup.map_subtype_le X, ?_, ?_, ?_⟩
  · exact Subgroup.comap_map_eq_self_of_injective G.subtype_injective X
  · conv_lhs => rw [hXcomm]
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJG]
  · show twoResidual (X.map G.subtype) = X.map G.subtype
    rw [← E1.map_twoResidual G.subtype X, hXtwo]

private theorem map_thompsonJ_ne_bot_g45k {F : Type} [Field F] {D : Type} [Group D]
    {G J V : Subgroup D} {α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hJG : J ≤ G) (hJc : ¬ J ≤ Subgroup.centralizer (V : Set D))
    (hαk : α.ker = (Subgroup.centralizer (V : Set D)).subgroupOf G) :
    (J.subgroupOf G).map α ≠ ⊥ := by
  intro hbot
  apply hJc
  intro j hj
  have hmem : α ⟨j, hJG hj⟩ ∈ (J.subgroupOf G).map α :=
    Subgroup.mem_map_of_mem α (Subgroup.mem_subgroupOf.mpr hj)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_subgroupOf.mp (hαk ▸ MonoidHom.mem_ker.mpr hmem)

private theorem restrict_alpha_g45k {F : Type} [Field F] {D : Type} [Group D]
    {C G X : Subgroup D} {α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F} (hXG : X ≤ G)
    (hαk : α.ker = C.subgroupOf G)
    (hαX : (X.subgroupOf G).map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F)) :
    (α.comp (Subgroup.inclusion hXG)).ker = C.subgroupOf X ∧
      (α.comp (Subgroup.inclusion hXG)).range =
        commutator (Matrix.SpecialLinearGroup (Fin 2) F) := by
  refine ⟨?_, ?_⟩
  · ext x
    show α (Subgroup.inclusion hXG x) = 1 ↔ (x : D) ∈ C
    rw [← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  · rw [MonoidHom.range_comp, Subgroup.inclusion_range, hαX]

private theorem map_commutator_invariant_g45k {F : Type} [Field F] {D : Type} [Group D]
    {G V X : Subgroup D} {α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F}
    {β : ↥⁅V, G⁆ →* Multiplicative (Fin 2 → F)}
    (hβe : ∀ (g : G) (u v : ↥⁅V, G⁆), (v : D) = g * u * g⁻¹ →
      Multiplicative.toAdd (β v) =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hXG : X ≤ G) (hW : ⁅V, X⁆ ≤ ⁅V, G⁆)
    (hαX : (X.subgroupOf G).map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∀ A ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) F),
      ∀ y ∈ (⁅V, X⁆.subgroupOf ⁅V, G⁆).map β,
        SL2Model.natAct A y ∈ (⁅V, X⁆.subgroupOf ⁅V, G⁆).map β := by
  intro A hA y hy
  obtain ⟨u, hu, hxu⟩ := Subgroup.mem_map.mp hy
  rw [← hxu]
  have hAre : A ∈ (α.comp (Subgroup.inclusion hXG)).range := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, hαX]
    exact hA
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hAre
  have hk' : α (Subgroup.inclusion hXG k) = A := hk
  have hconj : (k : D) * (u : D) * (k : D)⁻¹ ∈ ⁅V, X⁆ := by
    have h1 := Subgroup.mem_normalizer_iff.mp
      (Subgroup.normalizer_commutator_ge_right V X k.2) (u : D)
    exact h1.mp (Subgroup.mem_subgroupOf.mp hu)
  have hnat : SL2Model.natAct A (β u) = β ⟨(k : D) * (u : D) * (k : D)⁻¹, hW hconj⟩ := by
    have h1 := hβe (Subgroup.inclusion hXG k) u ⟨_, hW hconj⟩
      (by simp only [Subgroup.coe_inclusion, Subgroup.coe_inv])
    rw [hk'] at h1
    rw [SL2Model.natAct_apply, SL2Model.smul_eq_mulVec', ← h1, ofAdd_toAdd]
  rw [hnat]
  exact Subgroup.mem_map.mpr ⟨⟨_, hW hconj⟩, Subgroup.mem_subgroupOf.mpr hconj, rfl⟩

private theorem commutator_sl2_ne_bot_g45k {F : Type} [Field F] [Fintype F] {m : ℕ}
    (hF : Fintype.card F = 2 ^ m) :
    commutator (Matrix.SpecialLinearGroup (Fin 2) F) ≠ ⊥ := by
  intro hbot
  have hv : ∀ g ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) F),
      (g : Matrix (Fin 2) (Fin 2) F).mulVec (![1, 0] : Fin 2 → F) = ![1, 0] := by
    intro g hg
    rw [hbot, Subgroup.mem_bot] at hg
    subst hg
    simp
  have h0 := SL2CharTwo.eq_zero_of_forall_mulVec_eq hF hv
  have h1 : (![1, 0] : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  exact h1 h0

private theorem not_map_commutator_eq_bot_g45k {F : Type} [Field F] [Fintype F] {m : ℕ}
    (hcard : Fintype.card F = 2 ^ m) {D : Type} [Group D] [Finite D]
    {G V X : Subgroup D} {α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F}
    {β : ↥⁅V, G⁆ →* Multiplicative (Fin 2 → F)}
    (hαk : α.ker = (Subgroup.centralizer (V : Set D)).subgroupOf G)
    (hβk : β.ker = (⁅V, G⁆ ⊓ Subgroup.centralizer (G : Set D)).subgroupOf ⁅V, G⁆)
    (hVp : IsPGroup 2 V) (hXV : X ≤ Subgroup.normalizer (V : Set D))
    (hXtwo : twoResidual X = X) (hXG : X ≤ G) (hW : ⁅V, X⁆ ≤ ⁅V, G⁆)
    (hαX : (X.subgroupOf G).map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F))
    (hbot : (⁅V, X⁆.subgroupOf ⁅V, G⁆).map β = ⊥) : False := by
  have hW₁C : ⁅V, X⁆ ≤ Subgroup.centralizer (G : Set D) := by
    intro w hw
    have h1 : β ⟨w, hW hw⟩ = 1 := by
      have h2 : β ⟨w, hW hw⟩ ∈ (⁅V, X⁆.subgroupOf ⁅V, G⁆).map β :=
        Subgroup.mem_map_of_mem β (Subgroup.mem_subgroupOf.mpr hw)
      rw [hbot, Subgroup.mem_bot] at h2
      exact h2
    have h3 : (⟨w, hW hw⟩ : ↥⁅V, G⁆) ∈ β.ker := MonoidHom.mem_ker.mpr h1
    rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h3
    exact h3.2
  have hzero : ⁅⁅V, X⁆, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hW₁C.trans (Subgroup.centralizer_le fun x hx => hXG hx)
  have hsims : ⁅⁅V, X⁆, X⁆ = ⁅V, X⁆ :=
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
      (eq_top_of_isPGroup_quotient_of_twoResidual_eq hXtwo) hVp hXV
  have hWbot : ⁅V, X⁆ = ⊥ := hsims ▸ hzero
  have hXC : X ≤ Subgroup.centralizer (V : Set D) :=
    Subgroup.le_centralizer_iff.mpr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWbot)
  have hKbot : (X.subgroupOf G).map α = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [hαk, Subgroup.mem_subgroupOf]
    exact hXC (Subgroup.mem_subgroupOf.mp hx)
  rw [hαX] at hKbot
  exact commutator_sl2_ne_bot_g45k hcard hKbot

private theorem map_commutator_eq_top_g45k {F : Type} [Field F] [Fintype F] [CharP F 2]
    {D : Type} [Group D] {G V X : Subgroup D} {β : ↥⁅V, G⁆ →* Multiplicative (Fin 2 → F)}
    (hinv : ∀ A ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) F),
      ∀ y ∈ (⁅V, X⁆.subgroupOf ⁅V, G⁆).map β,
        SL2Model.natAct A y ∈ (⁅V, X⁆.subgroupOf ⁅V, G⁆).map β)
    (hne : (⁅V, X⁆.subgroupOf ⁅V, G⁆).map β ≠ ⊥) :
    (⁅V, X⁆.subgroupOf ⁅V, G⁆).map β = ⊤ := by
  rcases SL2Model.natAct_irreducible_comm _ hinv with h | h
  · exact absurd h hne
  · exact h

private theorem restrict_ker_g45k {F : Type} [Field F] [Fintype F] {m : ℕ}
    (hcard : Fintype.card F = 2 ^ m) {D : Type} [Group D]
    {G V X : Subgroup D} {α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F}
    {β : ↥⁅V, G⁆ →* Multiplicative (Fin 2 → F)}
    (hβe : ∀ (g : G) (u v : ↥⁅V, G⁆), (v : D) = g * u * g⁻¹ →
      Multiplicative.toAdd (β v) =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hβk : β.ker = (⁅V, G⁆ ⊓ Subgroup.centralizer (G : Set D)).subgroupOf ⁅V, G⁆)
    (hXG : X ≤ G) (hW : ⁅V, X⁆ ≤ ⁅V, G⁆)
    (hαX : (X.subgroupOf G).map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F)) :
    (β.comp (Subgroup.inclusion hW)).ker =
      (⁅V, X⁆ ⊓ Subgroup.centralizer (X : Set D)).subgroupOf ⁅V, X⁆ := by
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h1
    refine ⟨u.2, ?_⟩
    have h3 : (Subgroup.inclusion hW u : ↥⁅V, G⁆) ∈ β.ker := MonoidHom.mem_ker.mpr h1
    rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h3
    exact Subgroup.centralizer_le (fun x hx => hXG hx) h3.2
  · rintro ⟨-, hc⟩
    have hfix : ∀ A ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) F),
        (A : Matrix (Fin 2) (Fin 2) F).mulVec
            (Multiplicative.toAdd (β (Subgroup.inclusion hW u))) =
          Multiplicative.toAdd (β (Subgroup.inclusion hW u)) := by
      intro A hA
      have hAre : A ∈ (α.comp (Subgroup.inclusion hXG)).range := by
        rw [MonoidHom.range_comp, Subgroup.inclusion_range, hαX]
        exact hA
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hAre
      have hcomm : (k : D) * (u : D) = (u : D) * (k : D) :=
        Subgroup.mem_centralizer_iff.mp hc (k : D) k.2
      have hconj : ((Subgroup.inclusion hW u : ↥⁅V, G⁆) : D) =
          (Subgroup.inclusion hXG k : ↥G) * (Subgroup.inclusion hW u : D) *
            (Subgroup.inclusion hXG k : ↥G)⁻¹ := by
        show ((u : D)) = ((k : D)) * ((u : D)) * ((k : D))⁻¹
        rw [hcomm]
        group
      have h2 := hβe (Subgroup.inclusion hXG k) (Subgroup.inclusion hW u)
        (Subgroup.inclusion hW u) hconj
      have hk' : α (Subgroup.inclusion hXG k) = A := hk
      rw [hk'] at h2
      exact h2.symm
    have h0 := SL2CharTwo.eq_zero_of_forall_mulVec_eq hcard hfix
    rw [← ofAdd_toAdd (β (Subgroup.inclusion hW u)), h0, ofAdd_zero]

private theorem restrict_intertwines_g45k {F : Type} [Field F] {D : Type} [Group D]
    {G V X : Subgroup D} {α : ↥G →* Matrix.SpecialLinearGroup (Fin 2) F}
    {β : ↥⁅V, G⁆ →* Multiplicative (Fin 2 → F)}
    (hβe : ∀ (g : G) (u v : ↥⁅V, G⁆), (v : D) = g * u * g⁻¹ →
      Multiplicative.toAdd (β v) =
        (α g : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hXG : X ≤ G) (hW : ⁅V, X⁆ ≤ ⁅V, G⁆) :
    ∀ (k : X) (u v : ↥⁅V, X⁆), (v : D) = k * u * k⁻¹ →
      Multiplicative.toAdd ((β.comp (Subgroup.inclusion hW)) v) =
        ((α.comp (Subgroup.inclusion hXG)) k : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd ((β.comp (Subgroup.inclusion hW)) u)) := by
  intro k u v huv
  exact hβe (Subgroup.inclusion hXG k) (Subgroup.inclusion hW u) (Subgroup.inclusion hW v) (by
    show ((v : D)) = ((k : D)) * ((u : D)) * ((k : D))⁻¹
    exact huv)

theorem not_commutator_le_gomiV (h : GomiThm45Counterexample c G S)
    (h31 : GomiFact31) (h32 : GomiFact32) (h37 : GomiFact37OneCSP) (h373 : GomiFact37Three)
    (h374 : GomiFact37Four) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb)
    (hi : G ≤ conjClosure (baum S) G) :
    ¬ ⁅pCoreOf 2 G, twoResidual G⁆ ≤ gomiV G := by
  intro hQV
  obtain ⟨m, F, hFld, hFint, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ :=
    h.natural h31 h32 h37 h373 h374 hL hg hi
  have hCharP : CharP F 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; exact charP_of_card_eq_prime_pow hcard
  have hm : 1 ≤ m := by
    have h2 : 1 < 2 ^ m := by rw [← hcard]; exact Fintype.one_lt_card
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, pow_zero] at h2; omega
  have hJS : thompsonJ S ≤ S := iSup₂_le fun _ hA => hA.1
  have hJG : thompsonJ S ≤ G := hJS.trans h.isSylowTwoOf.1
  have hVp : IsPGroup 2 (gomiV G) := isPGroup_iff_pow_pow_eq_one.mpr fun g =>
    ⟨1, Subtype.ext (by simpa using (gomiV_moduleSetting G).1.2 g g.2)⟩
  have hJmapP : IsPGroup 2 (((thompsonJ S).subgroupOf G).map α) :=
    (IsPGroup.of_equiv (h.isSylowTwoOf.2.1.to_le hJS)
      (Subgroup.subgroupOfEquivOfLe hJG).symm).map α
  have hJne : ((thompsonJ S).subgroupOf G).map α ≠ ⊥ :=
    map_thompsonJ_ne_bot_g45k hJG h.not_thompsonJ_le_centralizer hαk
  obtain ⟨X, hXJ, hXK, hmin⟩ := exists_minimal_g45k hαs
  obtain ⟨hXcomm, hXtwo⟩ := minimal_props_g45k hcard hXJ hXK hmin hJmapP hJne
  obtain ⟨XΩ, hXΩG, hXΩsub, hXΩcomm, hXΩtwo⟩ := map_subtype_props_g45k hJG hXcomm hXtwo
  have hXΩK : (XΩ.subgroupOf G).map α = commutator (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [hXΩsub]; exact hXK
  obtain ⟨hker, hrange⟩ := restrict_alpha_g45k hXΩG hαk hXΩK
  have hWle : ⁅gomiV G, XΩ⁆ ≤ ⁅gomiV G, G⁆ := Subgroup.commutator_mono le_rfl hXΩG
  have hinv := map_commutator_invariant_g45k hβe hXΩG hWle hXΩK
  have hMne : (⁅gomiV G, XΩ⁆.subgroupOf ⁅gomiV G, G⁆).map β ≠ ⊥ := fun hbot =>
    not_map_commutator_eq_bot_g45k hcard hαk hβk hVp
      (hXΩG.trans (gomiV_moduleSetting G).2) hXΩtwo hXΩG hWle hXΩK hbot
  have hMtop : (⁅gomiV G, XΩ⁆.subgroupOf ⁅gomiV G, G⁆).map β = ⊤ :=
    map_commutator_eq_top_g45k hinv hMne
  have hβΩs : Function.Surjective (β.comp (Subgroup.inclusion hWle)) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hMtop
  have hβΩk := restrict_ker_g45k hcard hβe hβk hXΩG hWle hXΩK
  have hβΩe := restrict_intertwines_g45k hβe hXΩG hWle
  refine h.not_isGomiSingularSubgroup XΩ ⟨hXΩG, hXΩcomm, hXΩtwo, ?_, ?_⟩
  · calc ⁅pCoreOf 2 G, XΩ⁆ ≤ ⁅pCoreOf 2 G, twoResidual G⁆ :=
        Subgroup.commutator_mono le_rfl (hXΩtwo ▸ F6.twoResidual_mono hXΩG)
    _ ≤ gomiV G := hQV
  · exact ⟨Subgroup.centralizer (gomiV G : Set Ω), m, hm, F, hFld, hFint, hcard,
      α.comp (Subgroup.inclusion hXΩG), hker, hrange,
      β.comp (Subgroup.inclusion hWle), hβΩs, hβΩk, hβΩe⟩

end CFSG.GroupTheory.GomiThm45Counterexample
