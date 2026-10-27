module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.Quasithin.Background.D2Basic
import CFSG.Quasithin.Background.G64NatTop
import CFSG.Quasithin.Background.ConjTransport
import CFSG.Quasithin.Background.F918Z8Kw2
import CFSG.GroupTheory.ABGLocalTools.FixedPointCount
import CFSG.Quasithin.Vol2.Ch12Sec2Lem25A
import CFSG.Quasithin.Background.F918Q2
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact31Holds
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact32Weight
import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims137
import CFSG.Quasithin.EmptyFaithful.Gap6R0E
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
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
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.CGT.PushingUp.BenderBridge
import CFSG.CGT.PushingUp.BlockOrder
import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
import CFSG.CGT.PushingUpLit.CGT6.EmbeddingNodes
import CFSG.CGT.PushingUpLit.Statements
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.Dihedral.FourgroupCycleControl
import CFSG.Dihedral.OriginalCentralizerOddCore
import CFSG.GH74.SectionalRank
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaMinusEightOrderThree
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaPiGroup
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Induction
import CFSG.LocalAnalysis.GLTheoremB.Input27_9_3Proof
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
import CFSG.Monster.B.Classical.PlaneAut
import CFSG.Monster.B.TwoA.Unitary.LinThree
import CFSG.Quasithin.Background.FFC4Tr2
import CFSG.Quasithin.Background.SmithB42L2Sl2
import CFSG.Quasithin.Background.SmithB51LnRealB
import CFSG.Quasithin.EmptyFaithful.Gap6R0A
import CFSG.Quasithin.Vol2.Ch12Sec2Lem25Stmts
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.Walter.J1

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet IsPStar O2Trivial)

variable {W : Type} [CommGroup W]

private noncomputable def gomiW (A : Subgroup (MulAut W)) : ℕ :=
  Nat.card A * Nat.card (fixV A)

private theorem gomiW_bot : gomiW (⊥ : Subgroup (MulAut W)) = Nat.card W := by
  unfold gomiW
  rw [Subgroup.card_bot, one_mul]
  have h : fixV (⊥ : Subgroup (MulAut W)) = ⊤ := by
    ext w
    simp [mem_fixV]
  rw [h, Subgroup.card_top]

private theorem gomiW_map_conj (A : Subgroup (MulAut W)) (g : MulAut W) :
    gomiW (A.map (MulAut.conj g).toMonoidHom) = gomiW A := by
  unfold gomiW
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
    CFSG.Quasithin.ConjTransport.card_fixV_map_conj]

private noncomputable instance fintypeMulAutOfFinite [Finite W] : Fintype (MulAut W) := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  exact Fintype.ofInjective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective

private noncomputable instance fintypeSubgroupMulAutOfFinite [Finite W] :
    Fintype (Subgroup (MulAut W)) := by
  classical
  letI : Fintype (MulAut W) := fintypeMulAutOfFinite
  exact Fintype.ofInjective (fun H : Subgroup (MulAut W) => (H : Set (MulAut W)))
    (fun H K h => Subgroup.ext (fun x => (Set.ext_iff.mp h) x))

private noncomputable instance fintypeGomiNSet [Finite W] (Y : Subgroup (MulAut W)) :
    Fintype (↥(gomiNSet Y)) :=
  Fintype.ofInjective (fun i : ↥(gomiNSet Y) => (i : Subgroup (MulAut W)))
    Subtype.val_injective

private theorem le_of_mem_Pset {Y A : Subgroup (MulAut W)} (h : A ∈ Pset Y) : A ≤ Y :=
  h.1

private theorem ne_bot_of_mem_Pset {Y A : Subgroup (MulAut W)} (h : A ∈ Pset Y) : A ≠ ⊥ :=
  h.2.1

private theorem isElemAbelian2_of_mem_Pset {Y A : Subgroup (MulAut W)} (h : A ∈ Pset Y) :
    IsElemAbelian2 A :=
  h.2.2.1

private theorem gomiW_le_of_mem_Pset {Y A B : Subgroup (MulAut W)} (h : A ∈ Pset Y)
    (hBA : B ≤ A) : gomiW B ≤ gomiW A :=
  h.2.2.2 B hBA

private theorem mem_Pset_map_conj {Y A : Subgroup (MulAut W)} (hA : A ∈ Pset Y)
    {g : MulAut W} (hg : g ∈ Y) : A.map (MulAut.conj g).toMonoidHom ∈ Pset Y := by
  obtain ⟨hAY, hA1, hAe, hAoff⟩ := hA
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hcomp' : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact Y.mul_mem (Y.mul_mem hg (hAY ha)) (Y.inv_mem hg)
  · intro h0
    exact hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h0)
  · obtain ⟨hc, hs⟩ := hAe
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hs a ha, map_one]
  · intro B hB
    have hB' : (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = B := by
      rw [Subgroup.map_map, hcomp', Subgroup.map_id]
    have hCB : (B.map (MulAut.conj g⁻¹).toMonoidHom) ≤ A := by
      have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hB
      rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at this
    have h1 := hAoff (B.map (MulAut.conj g⁻¹).toMonoidHom) hCB
    have hB'' : gomiW B = gomiW (B.map (MulAut.conj g⁻¹).toMonoidHom) := by
      calc gomiW B = gomiW ((B.map (MulAut.conj g⁻¹).toMonoidHom).map
            (MulAut.conj g).toMonoidHom) := by rw [hB']
        _ = gomiW (B.map (MulAut.conj g⁻¹).toMonoidHom) := gomiW_map_conj _ g
    calc gomiW B = gomiW (B.map (MulAut.conj g⁻¹).toMonoidHom) := hB''
      _ ≤ gomiW A := h1
      _ = gomiW (A.map (MulAut.conj g).toMonoidHom) := (gomiW_map_conj A g).symm

private theorem mem_PstarSet_map_conj {Y A : Subgroup (MulAut W)} (hA : A ∈ PstarSet Y)
    {g : MulAut W} (hg : g ∈ Y) : A.map (MulAut.conj g).toMonoidHom ∈ PstarSet Y := by
  refine ⟨mem_Pset_map_conj hA.1 hg, ?_⟩
  intro B hB hBA hweight
  let C : Subgroup (MulAut W) := B.map (MulAut.conj g⁻¹).toMonoidHom
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hcomp'' : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hCB : C ≤ A := by
    have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hBA
    rwa [Subgroup.map_map, hcomp'', Subgroup.map_id] at this
  have hC : C ∈ Pset Y := mem_Pset_map_conj hB (Y.inv_mem hg)
  have hCw : gomiW C = gomiW A := by
    dsimp only [C]
    rw [gomiW_map_conj]
    exact hweight.symm.trans (gomiW_map_conj A g)
  have hCA : C = A := hA.2 C hC hCB hCw.symm
  have hB' : C.map (MulAut.conj g).toMonoidHom = B := by
    rw [Subgroup.map_map]
    have hcomp' : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id (MulAut W) := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp', Subgroup.map_id]
  rw [← hCA, hB']

private theorem mem_gomiPstar0Set_map_conj {Y A : Subgroup (MulAut W)}
    (hA : A ∈ gomiPstar0Set Y) {g : MulAut W} (hg : g ∈ Y) :
    A.map (MulAut.conj g).toMonoidHom ∈ gomiPstar0Set Y := by
  refine ⟨mem_PstarSet_map_conj hA.1 hg, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp (hA.2 ha)
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, ?_, ?_⟩
  · exact (CFSG.GH74.GLS.pPrimePCore_normal 2 ↥Y).conj_mem k hk ⟨g, hg⟩
  · ext w
    simp [MulAut.conj_apply, mul_assoc]

private theorem map_sSup_eq_of_maps {S : Set (Subgroup (MulAut W))} {g : MulAut W}
    (h : ∀ A ∈ S, A.map (MulAut.conj g).toMonoidHom ∈ S)
    (h' : ∀ A ∈ S, A.map (MulAut.conj g⁻¹).toMonoidHom ∈ S) :
    (sSup S).map (MulAut.conj g).toMonoidHom = sSup S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A hA => ?_
    exact Subgroup.map_le_iff_le_comap.mp (le_sSup (h A hA))
  · have h2 : (sSup S).map (MulAut.conj g⁻¹).toMonoidHom ≤ sSup S := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun A hA => ?_
      exact Subgroup.map_le_iff_le_comap.mp (le_sSup (h' A hA))
    have h3 : ((sSup S).map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom ≤ (sSup S).map (MulAut.conj g).toMonoidHom :=
      Subgroup.map_mono h2
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id (MulAut W) := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h3

private theorem gomiGstar0_le_normalizer (Y : Subgroup (MulAut W)) :
    Y ≤ Subgroup.normalizer (gomiGstar0 Y : Set (MulAut W)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  unfold gomiGstar0
  exact map_sSup_eq_of_maps (fun A hA => mem_gomiPstar0Set_map_conj hA hg)
    (fun A hA => mem_gomiPstar0Set_map_conj hA (Y.inv_mem hg))

private theorem exists_minimal_Pstar_of_le [Finite W] {Y A C : Subgroup (MulAut W)}
    (hA : A ∈ Pset Y) (hC : C ≤ A) (hCne : C ≠ ⊥) (hw : gomiW C = gomiW A) :
    ∃ B : Subgroup (MulAut W), B ∈ PstarSet Y ∧ B ≤ C ∧ B ≠ ⊥ ∧ gomiW B = gomiW A := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have : Fintype (MulAut W) :=
    Fintype.ofInjective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Fintype (Subgroup (MulAut W)) :=
    Fintype.ofInjective (fun H : Subgroup (MulAut W) => (H : Set (MulAut W)))
      (fun H K h => Subgroup.ext (fun x => (Set.ext_iff.mp h) x))
  let S : Set (Subgroup (MulAut W)) := {B | B ≤ C ∧ B ≠ ⊥ ∧ gomiW B = gomiW A}
  have hSne : S.Nonempty := ⟨C, le_rfl, hCne, hw⟩
  obtain ⟨B, hBmin⟩ := (Set.toFinite S).exists_minimal hSne
  have hBC : B ≤ C := hBmin.prop.1
  have hBne : B ≠ ⊥ := hBmin.prop.2.1
  have hBw : gomiW B = gomiW A := hBmin.prop.2.2
  have hBleA : B ≤ A := hBC.trans hC
  have hAe := isElemAbelian2_of_mem_Pset hA
  have hBel : IsElemAbelian2 B :=
    ⟨fun x hx y hy => hAe.1 x (hBleA hx) y (hBleA hy),
      fun x hx => hAe.2 x (hBleA hx)⟩
  refine ⟨B, ⟨⟨hBleA.trans (le_of_mem_Pset hA), hBne, hBel, ?_⟩, ?_⟩, hBC, hBne, hBw⟩
  · intro D hD
    exact (gomiW_le_of_mem_Pset hA (hD.trans hBleA)).trans (le_of_eq hBw.symm)
  · intro B' hB' hB'le hB'w
    have hB'S : B' ∈ S :=
      ⟨hB'le.trans hBC, ne_bot_of_mem_Pset hB', hB'w.symm.trans hBw⟩
    exact le_antisymm hB'le (hBmin.le_of_le hB'S hB'le)

private theorem le_stabSub_commV_of_le_normalizer {N R : Subgroup (MulAut W)}
    (hR : R ≤ Subgroup.normalizer (N : Set (MulAut W))) : R ≤ stabSub (commV N) := by
  intro r hr
  have hN : N.map (MulAut.conj r).toMonoidHom = N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hR hr)
  have hH : (commV N).map r.toMonoidHom = commV N := by
    rw [← CFSG.Quasithin.commV_map_conj_eq N r, hN]
  intro u
  constructor
  · intro hu
    have hu' : r u ∈ (commV N).map r.toMonoidHom := by rwa [hH]
    have := (Subgroup.mem_map_equiv).mp hu'
    simpa using this
  · intro hu
    have : r u ∈ (commV N).map r.toMonoidHom := Subgroup.mem_map_of_mem r.toMonoidHom hu
    rwa [hH] at this

private theorem le_stabSub_fixV_of_le_normalizer {N R : Subgroup (MulAut W)}
    (hR : R ≤ Subgroup.normalizer (N : Set (MulAut W))) : R ≤ stabSub (fixV N) := by
  intro r hr
  have hN : N.map (MulAut.conj r).toMonoidHom = N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hR hr)
  have hH : (fixV N).map r.toMonoidHom = fixV N := by
    rw [← CFSG.Quasithin.fixV_map_conj_eq N r, hN]
  intro u
  constructor
  · intro hu
    have hu' : r u ∈ (fixV N).map r.toMonoidHom := by rwa [hH]
    have := (Subgroup.mem_map_equiv).mp hu'
    simpa using this
  · intro hu
    have : r u ∈ (fixV N).map r.toMonoidHom := Subgroup.mem_map_of_mem r.toMonoidHom hu
    rwa [hH] at this

private theorem card_fixV_eq_mul_of_isCompl {I J : Subgroup W}
    (hdisj : I ⊓ J = ⊥) (hsup : I ⊔ J = ⊤) {R : Subgroup (MulAut W)}
    (hI : R ≤ stabSub I) (hJ : R ≤ stabSub J) :
    Nat.card (fixV R) = Nat.card ↥(I ⊓ fixV R) * Nat.card ↥(J ⊓ fixV R) := by
  have h : fixV R = (I ⊓ fixV R) ⊔ (J ⊓ fixV R) :=
    CFSG.Quasithin.Gap6.fixV_eq_sup_of_summands hsup hdisj
      (fun g hg u hu => (mem_stabSub.mp (hI hg) u).2 hu)
      (fun g hg u hu => (mem_stabSub.mp (hJ hg) u).2 hu)
  have hinf : (I ⊓ fixV R) ⊓ (J ⊓ fixV R) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hxI : x ∈ I := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
    have hxJ : x ∈ J := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1
    have : x ∈ I ⊓ J := ⟨hxI, hxJ⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  have hcard := CFSG.Quasithin.card_sup_mul_card_inf (I ⊓ fixV R) (J ⊓ fixV R)
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  nth_rewrite 1 [h]
  exact hcard

private theorem gomiOrbitSpan_map_conj {Y A : Subgroup (MulAut W)} {g : MulAut W} (hg : g ∈ Y) :
    (gomiOrbitSpan Y A).map (MulAut.conj g).toMonoidHom =
      gomiOrbitSpan Y (A.map (MulAut.conj g).toMonoidHom) := by
  have hN : (gomiGstar0 Y).map (MulAut.conj g).toMonoidHom = gomiGstar0 Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (gomiGstar0_le_normalizer Y hg)
  have hN' : (gomiGstar0 Y).map (MulAut.conj g⁻¹).toMonoidHom = gomiGstar0 Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (gomiGstar0_le_normalizer Y (Y.inv_mem hg))
  have hmem : ∀ x ∈ gomiGstar0 Y, g * x * g⁻¹ ∈ gomiGstar0 Y := by
    intro x hx
    exact hN ▸ Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  have hmem' : ∀ x ∈ gomiGstar0 Y, g⁻¹ * x * g ∈ gomiGstar0 Y := by
    intro x hx
    exact hN' ▸ Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx
  unfold gomiOrbitSpan
  simp only [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    refine le_iSup₂_of_le (f := fun y (_ : y ∈ gomiGstar0 Y) =>
      (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj y).toMonoidHom)
      (g * x * g⁻¹) (hmem x hx) ?_
    apply le_of_eq
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  · refine iSup_le fun x => iSup_le fun hx => ?_
    refine le_iSup₂_of_le (f := fun y (_ : y ∈ gomiGstar0 Y) =>
      (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj g).toMonoidHom)
      (g⁻¹ * x * g) (hmem' x hx) ?_
    apply le_of_eq
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp [MulAut.conj_apply, mul_assoc]

private theorem mem_gomiNSet_map_conj {Y : Subgroup (MulAut W)} {N : Subgroup (MulAut W)}
    (hN : N ∈ gomiNSet Y) {g : MulAut W} (hg : g ∈ Y) :
    N.map (MulAut.conj g).toMonoidHom ∈ gomiNSet Y := by
  obtain ⟨A, hA, rfl⟩ := hN
  exact ⟨A.map (MulAut.conj g).toMonoidHom, mem_gomiPstar0Set_map_conj hA hg,
    (gomiOrbitSpan_map_conj hg)⟩

private theorem gomi31_facts (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y)) :
    ((∀ N ∈ gomiNSet Y, IsSLn ↥N 2 1) ∧ sSupIndep (gomiNSet Y) ∧
        (gomiNSet Y).Pairwise (fun N N' => ∀ x ∈ N, ∀ y ∈ N', x * y = y * x) ∧
        sSup (gomiNSet Y) = gomiGstar0 Y) ∧
      ((∀ N ∈ gomiNSet Y, BinaryNaturalSL N (commV N) ⊥ 2 1) ∧
        iSupIndep (fun N : ↥(gomiNSet Y) => commV (N : Subgroup (MulAut W))) ∧
        ⨆ N : ↥(gomiNSet Y), commV (N : Subgroup (MulAut W)) = commV (gomiGstar0 Y)) ∧
      commV (gomiGstar0 Y) ⊔ fixV (gomiGstar0 Y) = ⊤ ∧
        Disjoint (commV (gomiGstar0 Y)) (fixV (gomiGstar0 Y)) :=
  h31 W hW Y hne hO2

private theorem card_commV_of_mem_gomiNSet (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {N : Subgroup (MulAut W)} (hN : N ∈ gomiNSet Y) : Nat.card (commV N) = 4 := by
  have hNat : ∀ N ∈ gomiNSet Y, BinaryNaturalSL N (commV N) ⊥ 2 1 :=
    (gomi31_facts h31 hW hne hO2).2.1.1
  obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hNat N hN
  obtain ⟨π, hπ⟩ := hreal
  have hcardK : Nat.card K = 2 := by simpa using hKcard
  have h := CFSG.Quasithin.G64.RealizesVia.card_eq hπ
  rw [h, CFSG.Quasithin.G64.card_natMod, hcardK]
  norm_num

private theorem card_of_isSLn_two_one {N : Type} [Group N] [Finite N]
    (h : IsSLn N 2 1) : Nat.card N = 6 := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hKcard
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hK]
  norm_num

private theorem le_stabSub_of_binaryNaturalSL {N : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : ↥(CFSG.Open.StatedSL 2 (ZMod 2)) →* ↥N}
    (h : (FFModel.nat (CFSG.Open.StatedSL 2 (ZMod 2))).RealizesVia N U Z π) :
    N ≤ stabSub U := by
  intro n hn u
  constructor
  · intro hu
    have h1 : ((⟨n, hn⟩ : ↥N)⁻¹ : MulAut W) ((n : MulAut W) u) ∈ U :=
      h.2.2.2.1 ⟨n, hn⟩⁻¹ _ hu
    simpa using h1
  · intro hu
    exact h.2.2.2.1 ⟨n, hn⟩ u hu

private theorem inf_centSub_eq_bot_of_binaryNaturalSL {N : Subgroup (MulAut W)}
    {U Z : Subgroup W} {π : ↥(CFSG.Open.StatedSL 2 (ZMod 2)) →* ↥N}
    (h : (FFModel.nat (CFSG.Open.StatedSL 2 (ZMod 2))).RealizesVia N U Z π) :
    N ⊓ centSub U = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨hN, hcent⟩ := Subgroup.mem_inf.mp hn
  have htriv : ∀ u ∈ U, (n : MulAut W) u * u⁻¹ ∈ Z := by
    intro u hu
    rw [hcent u hu, mul_inv_cancel]
    exact Z.one_mem
  have h1 : (n : MulAut W) = 1 :=
    CFSG.Quasithin.G64.RealizesVia.eq_one_of_trivial (FFModel.nat_faithful _) h hN htriv
  rw [Subgroup.mem_bot]
  exact h1

private theorem autSub_eq_top_of_binaryNaturalSL (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {N : Subgroup (MulAut W)} (hN : N ∈ gomiNSet Y) :
    autSub N (commV N) = ⊤ := by
  have hNat : ∀ N ∈ gomiNSet Y, BinaryNaturalSL N (commV N) ⊥ 2 1 :=
    (gomi31_facts h31 hW hne hO2).2.1.1
  obtain ⟨π, hπ⟩ := CFSG.Quasithin.G64.BinaryNaturalSL.exists_zmod (hNat N hN)
  have hstab : N ≤ stabSub (commV N) := le_stabSub_of_binaryNaturalSL hπ
  have hcent : N ⊓ centSub (commV N) = ⊥ := inf_centSub_eq_bot_of_binaryNaturalSL hπ
  have hcardN : Nat.card N = 6 := card_of_isSLn_two_one ((gomi31_facts h31 hW hne hO2).1.1 N hN)
  have hcardU : Nat.card (commV N) = 4 := card_commV_of_mem_gomiNSet h31 hW hne hO2 hN
  have hcardAut : Nat.card (autSub N (commV N)) = 6 := by
    have h := CFSG.Quasithin.card_autSub_mul (A := N) (U := commV N) hstab
    rw [hcent, Subgroup.card_bot, mul_one, hcardN] at h
    exact h
  have hH2 : ∀ h : ↥(commV N), h ^ 2 = 1 := fun h => Subtype.ext (by simpa using hW (h : W))
  exact Subgroup.eq_top_of_card_eq (autSub N (commV N))
    (by rw [hcardAut, CFSG.CGT.PushingUpLit.CGT6.card_mulAut_of_card_four hH2 hcardU])

private theorem gomiNSet_le_centSub_of_ne (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {N N' : ↥(gomiNSet Y)} (hNN' : N ≠ N') :
    (N : Subgroup (MulAut W)) ≤ centSub (commV (N' : Subgroup (MulAut W))) := by
  have hfacts := gomi31_facts h31 hW hne hO2
  have hcomm : ∀ x ∈ (N : Subgroup (MulAut W)), ∀ y ∈ (N' : Subgroup (MulAut W)),
      x * y = y * x := hfacts.1.2.2.1 N.2 N'.2 (fun h => hNN' (Subtype.ext h))
  let H' : Subgroup W := commV (N' : Subgroup (MulAut W))
  have hNat' : BinaryNaturalSL (N' : Subgroup (MulAut W)) H' ⊥ 2 1 :=
    hfacts.2.1.1 (N' : Subgroup (MulAut W)) N'.2
  obtain ⟨π', hπ'⟩ := CFSG.Quasithin.G64.BinaryNaturalSL.exists_zmod hNat'
  have hstabN' : (N' : Subgroup (MulAut W)) ≤ stabSub H' := le_stabSub_of_binaryNaturalSL hπ'
  have hcardH' : Nat.card H' = 4 := card_commV_of_mem_gomiNSet h31 hW hne hO2 N'.2
  have hH'2 : ∀ h : H', h * h = 1 := fun h => Subtype.ext (by
    simpa [sq] using hW (h : W))
  have hcenter : Subgroup.center (MulAut H') = ⊥ :=
    CFSG.Quasithin.H13.Lem25.center_mulAut_eq_bot hH'2 (by omega)
  have hstabN : (N : Subgroup (MulAut W)) ≤ stabSub H' := by
    apply le_stabSub_commV_of_le_normalizer
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have h1 : (MulAut.conj x) y = y := by
        rw [MulAut.conj_apply, hcomm x hx y hy]
        group
      simpa [h1] using hy
    · intro y hy
      refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
      show (MulAut.conj x) y = y
      rw [MulAut.conj_apply, hcomm x hx y hy]
      group
  intro x hx u hu
  let φ : MulAut H' := resHom H' ⟨x, hstabN hx⟩
  have hφ : φ ∈ Subgroup.center (MulAut H') := by
    rw [Subgroup.mem_center_iff]
    intro ψ
    have hψ : ψ ∈ autSub (N' : Subgroup (MulAut W)) H' := by
      rw [autSub_eq_top_of_binaryNaturalSL h31 hW hne hO2 N'.2]
      trivial
    obtain ⟨s, hs, rfl⟩ := mem_autSub.mp hψ
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hcomm x hx s.1 hs).symm
  rw [hcenter, Subgroup.mem_bot] at hφ
  exact congrArg Subtype.val (show φ ⟨u, hu⟩ = ⟨u, hu⟩ by rw [hφ]; rfl)

private theorem autSub_perm_commV (_h31 : GomiFact31) [Finite W]
    (_hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (_hne : (gomiPstar0Set Y).Nonempty) (_hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    ∀ a ∈ autSub A (commV (gomiGstar0 Y)), ∀ i : ↥(gomiNSet Y),
      ∃ j : ↥(gomiNSet Y),
        ((commV (i : Subgroup (MulAut W))).subgroupOf (commV (gomiGstar0 Y))).map
            (a : MulAut (commV (gomiGstar0 Y))).toMonoidHom =
          (commV (j : Subgroup (MulAut W))).subgroupOf (commV (gomiGstar0 Y)) := by
  intro a ha i
  obtain ⟨s, hs, rfl⟩ := mem_autSub.mp ha
  have hsY : (s : MulAut W) ∈ Y := hA.1.1 hs
  let j : ↥(gomiNSet Y) :=
    ⟨(i : Subgroup (MulAut W)).map (MulAut.conj (s : MulAut W)).toMonoidHom,
      mem_gomiNSet_map_conj i.2 hsY⟩
  refine ⟨j, ?_⟩
  rw [CFSG.Quasithin.map_subgroupOf_resHomQ2]
  rw [CFSG.Quasithin.commV_map_conj_eq]

private theorem centSub_inf_eq_bot_of_isCompl {I J : Subgroup W}
    (hsup : I ⊔ J = ⊤) : centSub I ⊓ centSub J = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hbI, hbJ⟩ := Subgroup.mem_inf.mp hb
  rw [Subgroup.mem_bot]
  ext v
  have hv : v ∈ I ⊔ J := hsup ▸ Subgroup.mem_top v
  obtain ⟨i, hi, j, hj, rfl⟩ := Subgroup.mem_sup.mp hv
  rw [map_mul, mem_centSub.mp hbI i hi, mem_centSub.mp hbJ j hj]
  rfl

private def gomiOrbitA {Y : Subgroup (MulAut W)} (A : Subgroup (MulAut W)) :
    Subgroup (MulAut (commV (gomiGstar0 Y))) :=
  autSub A (commV (gomiGstar0 Y))

private def gomiOrbitFix {Y : Subgroup (MulAut W)} (A : Subgroup (MulAut W)) :
    Subgroup (commV (gomiGstar0 Y)) :=
  fixV (autSub A (commV (gomiGstar0 Y)))

private theorem gomi_orbit_Ae (_h31 : GomiFact31) [Finite W]
    (_hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (_hne : (gomiPstar0Set Y).Nonempty) (_hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    IsElemAbelian2 (autSub A (commV (gomiGstar0 Y))) := by
  classical
  let H : Subgroup W := commV (gomiGstar0 Y)
  constructor
  · intro x hx y hy
    obtain ⟨a, ha, hxa⟩ := mem_autSub.mp hx
    obtain ⟨b, hb, hxb⟩ := mem_autSub.mp hy
    rw [← hxa, ← hxb]
    calc resHom H a * resHom H b = resHom H (a * b) := (map_mul (resHom H) a b).symm
      _ = resHom H (b * a) := by
          congr 1
          ext z
          change (a.1 * b.1) z = (b.1 * a.1) z
          rw [(isElemAbelian2_of_mem_Pset hA.1).1 a.1 ha b.1 hb]
      _ = resHom H b * resHom H a := map_mul (resHom H) b a
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_autSub.mp hx
    rw [← hxa]
    calc resHom H a ^ 2 = resHom H (a ^ 2) := (map_pow (resHom H) a 2).symm
      _ = resHom H 1 := by
          congr 1
          ext z
          change (a.1 ^ 2) z = (1 : MulAut W) z
          rw [(isElemAbelian2_of_mem_Pset hA.1).2 a.1 ha]
      _ = 1 := map_one (resHom H)

private structure GomiOrbitSetup (H : Subgroup W) (S : Type)
    (V : S → Subgroup H) (A : Subgroup (MulAut W)) where
  fintype : Fintype S
  hH2 : ∀ h : H, h ^ 2 = 1
  hIndep : iSupIndep V
  hSup : ⨆ i, V i = ⊤
  hcard : ∀ i, Nat.card (V i) = 4
  hAe : IsElemAbelian2 (autSub A H)
  hperm : ∀ a ∈ autSub A H, ∀ i : S, ∃ j : S, (V i).map a.toMonoidHom = V j

private noncomputable def gomi_orbit_setup (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    let H : Subgroup W := commV (gomiGstar0 Y)
    let S := ↥(gomiNSet Y)
    let V : S → Subgroup H := fun i => (commV (i : Subgroup (MulAut W))).subgroupOf H
    GomiOrbitSetup H S V A := by
  classical
  let H : Subgroup W := commV (gomiGstar0 Y)
  let S := ↥(gomiNSet Y)
  let V : S → Subgroup H := fun i => (commV (i : Subgroup (MulAut W))).subgroupOf H
  have hfin : Fintype S := Fintype.ofFinite S
  have hH2 : ∀ h : H, h ^ 2 = 1 := fun h => Subtype.ext (by
    simpa [sq] using hW (h : W))
  have hIndepH : iSupIndep (fun i : S => commV (i : Subgroup (MulAut W))) :=
    (gomi31_facts h31 hW hne hO2).2.1.2.1
  have hSupH : (⨆ i : S, commV (i : Subgroup (MulAut W))) = H :=
    (gomi31_facts h31 hW hne hO2).2.1.2.2
  have hIndep : iSupIndep V := by
    have h := CFSG.RankThree.Classical.iSupIndep_comap_of_injective
      (f := H.subtype) H.subtype_injective hIndepH
    simpa [V, Subgroup.comap_subtype] using h
  have hSup : ⨆ i, V i = ⊤ := by
    have h := CFSG.RankThree.Classical.comap_iSup_of_le_range (f := H.subtype) H.subtype_injective
      (L := fun i : S => commV (i : Subgroup (MulAut W)))
      (fun i => by
        rw [Subgroup.range_subtype]
        rw [← hSupH]
        exact le_iSup (fun j : S => commV (j : Subgroup (MulAut W))) i)
    have h' : (⨆ i : S, commV (i : Subgroup (MulAut W))).comap H.subtype = ⨆ i, V i := by
      simpa [V, Subgroup.comap_subtype] using h
    rw [hSupH, Subgroup.comap_subtype, Subgroup.subgroupOf_self] at h'
    exact h'.symm
  have hcard : ∀ i, Nat.card (V i) = 4 := by
    intro i
    have hle : commV (i : Subgroup (MulAut W)) ≤ H := by
      rw [← hSupH]
      exact le_iSup (fun j : S => commV (j : Subgroup (MulAut W))) i
    dsimp only [V]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact card_commV_of_mem_gomiNSet h31 hW hne hO2 i.2
  exact ⟨hfin, hH2, hIndep, hSup, hcard,
    gomi_orbit_Ae h31 hW hne hO2 hA, autSub_perm_commV h31 hW hne hO2 hA⟩

private theorem gomi_orbit_ineq (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    Nat.card (gomiOrbitA (Y := Y) A) * Nat.card (gomiOrbitFix (Y := Y) A) ≤
      Nat.card ↥(commV (gomiGstar0 Y)) := by
  let H : Subgroup W := commV (gomiGstar0 Y)
  let S := ↥(gomiNSet Y)
  let V : S → Subgroup H := fun i => (commV (i : Subgroup (MulAut W))).subgroupOf H
  let D := gomi_orbit_setup h31 hW hne hO2 hA
  let := D.fintype
  dsimp only [gomiOrbitA, gomiOrbitFix]
  exact (card_mul_card_fixV_le_of_perm D.hH2 V D.hIndep D.hSup D.hcard D.hAe D.hperm).1

private theorem gomi_orbit_eq (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y)
    (heq : Nat.card (gomiOrbitA (Y := Y) A) * Nat.card (gomiOrbitFix (Y := Y) A) =
      Nat.card ↥(commV (gomiGstar0 Y))) :
    ∀ a ∈ gomiOrbitA (Y := Y) A, ∀ i : ↥(gomiNSet Y),
      ((commV (i : Subgroup (MulAut W))).subgroupOf (commV (gomiGstar0 Y))).map
          (a : MulAut (commV (gomiGstar0 Y))).toMonoidHom =
        (commV (i : Subgroup (MulAut W))).subgroupOf (commV (gomiGstar0 Y)) := by
  let H : Subgroup W := commV (gomiGstar0 Y)
  let S := ↥(gomiNSet Y)
  let V : S → Subgroup H := fun i => (commV (i : Subgroup (MulAut W))).subgroupOf H
  let D := gomi_orbit_setup h31 hW hne hO2 hA
  let := D.fintype
  dsimp only [gomiOrbitA, gomiOrbitFix] at heq
  exact (card_mul_card_fixV_le_of_perm D.hH2 V D.hIndep D.hSup D.hcard D.hAe D.hperm).2 heq

private theorem gomi_orbit_bound (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    Nat.card (gomiOrbitA (Y := Y) A) * Nat.card (gomiOrbitFix (Y := Y) A) ≤
      Nat.card ↥(commV (gomiGstar0 Y)) ∧
    (Nat.card (gomiOrbitA (Y := Y) A) * Nat.card (gomiOrbitFix (Y := Y) A) =
      Nat.card ↥(commV (gomiGstar0 Y)) →
      ∀ a ∈ gomiOrbitA (Y := Y) A, ∀ i : ↥(gomiNSet Y),
        ((commV (i : Subgroup (MulAut W))).subgroupOf (commV (gomiGstar0 Y))).map
            (a : MulAut (commV (gomiGstar0 Y))).toMonoidHom =
          (commV (i : Subgroup (MulAut W))).subgroupOf (commV (gomiGstar0 Y))) :=
  ⟨gomi_orbit_ineq h31 hW hne hO2 hA, gomi_orbit_eq h31 hW hne hO2 hA⟩

private theorem gomiP0_setup (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    A ≤ Subgroup.normalizer (gomiGstar0 Y : Set (MulAut W)) ∧
    A ≤ stabSub (commV (gomiGstar0 Y)) ∧
    A ≤ stabSub (fixV (gomiGstar0 Y)) ∧
    commV (gomiGstar0 Y) ⊔ fixV (gomiGstar0 Y) = ⊤ ∧
    commV (gomiGstar0 Y) ⊓ fixV (gomiGstar0 Y) = ⊥ := by
  have hA_le_norm : A ≤ Subgroup.normalizer (gomiGstar0 Y : Set (MulAut W)) :=
    hA.1.1.trans (gomiGstar0_le_normalizer Y)
  have hA_stabH : A ≤ stabSub (commV (gomiGstar0 Y)) :=
    le_stabSub_commV_of_le_normalizer hA_le_norm
  have hA_stabU : A ≤ stabSub (fixV (gomiGstar0 Y)) :=
    le_stabSub_fixV_of_le_normalizer hA_le_norm
  have hCompl : commV (gomiGstar0 Y) ⊔ fixV (gomiGstar0 Y) = ⊤ :=
    (gomi31_facts h31 hW hne hO2).2.2.1
  have hDisj : Disjoint (commV (gomiGstar0 Y)) (fixV (gomiGstar0 Y)) :=
    (gomi31_facts h31 hW hne hO2).2.2.2
  exact ⟨hA_le_norm, hA_stabH, hA_stabU, hCompl, hDisj.eq_bot⟩

private theorem gomiWeightCardFacts (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    let N : Subgroup (MulAut W) := gomiGstar0 Y
    let H : Subgroup W := commV N
    let U : Subgroup W := fixV N
    let A₁ : Subgroup (MulAut W) := A ⊓ centSub H
    Nat.card A = Nat.card (autSub A H) * Nat.card A₁ ∧
    Nat.card (fixV A) = Nat.card (fixV (autSub A H)) * Nat.card ↥(U ⊓ fixV A) ∧
    Nat.card (fixV A₁) = Nat.card H * Nat.card ↥(U ⊓ fixV A₁) := by
  let N : Subgroup (MulAut W) := gomiGstar0 Y
  let H : Subgroup W := commV N
  let U : Subgroup W := fixV N
  let A₁ : Subgroup (MulAut W) := A ⊓ centSub H
  obtain ⟨_, hA_stabH, hA_stabU, hCompl, hDisj'⟩ := gomiP0_setup h31 hW hne hO2 hA
  have hA₁_le_A : A₁ ≤ A := inf_le_left
  have hA₁_stabH : A₁ ≤ stabSub H := hA₁_le_A.trans hA_stabH
  have hA₁_stabU : A₁ ≤ stabSub U := hA₁_le_A.trans hA_stabU
  have hcardA : Nat.card A = Nat.card (autSub A H) * Nat.card A₁ := by
    have h := CFSG.Quasithin.card_autSub_mul (A := A) (U := H) hA_stabH
    exact h.symm
  have hcardFixH : Nat.card ↥(H ⊓ fixV A) = Nat.card (fixV (autSub A H)) := by
    rw [← CFSG.Quasithin.map_subtype_fixV_autSub hA_stabH,
      Subgroup.card_map_of_injective H.subtype_injective]
  have hcardFix : Nat.card (fixV A) =
      Nat.card (fixV (autSub A H)) * Nat.card ↥(U ⊓ fixV A) := by
    rw [card_fixV_eq_mul_of_isCompl hDisj' hCompl hA_stabH hA_stabU, hcardFixH]
  have hHle : H ≤ fixV A₁ := by
    intro h hh
    exact mem_fixV.mpr fun b hb => (Subgroup.mem_inf.mp hb).2 h hh
  have hcardFixA₁ : Nat.card (fixV A₁) = Nat.card H * Nat.card ↥(U ⊓ fixV A₁) := by
    rw [card_fixV_eq_mul_of_isCompl hDisj' hCompl hA₁_stabH hA₁_stabU,
      inf_eq_left.mpr hHle]
  exact ⟨hcardA, hcardFix, hcardFixA₁⟩

private theorem gomiW_A_le_gomiW_inf_centSub (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    gomiW A ≤ gomiW (A ⊓ centSub (commV (gomiGstar0 Y))) := by
  let N : Subgroup (MulAut W) := gomiGstar0 Y
  let H : Subgroup W := commV N
  let U : Subgroup W := fixV N
  let A₁ : Subgroup (MulAut W) := A ⊓ centSub H
  obtain ⟨_, hA_stabH, hA_stabU, hCompl, hDisj'⟩ := gomiP0_setup h31 hW hne hO2 hA
  obtain ⟨hcardA, hcardFix, hcardFixA₁⟩ :=
    gomiWeightCardFacts h31 hW hne hO2 hA
  have hA₁_le_A : A₁ ≤ A := inf_le_left
  have hU_le : Nat.card ↥(U ⊓ fixV A) ≤ Nat.card ↥(U ⊓ fixV A₁) :=
    Subgroup.card_le_of_le (inf_le_inf le_rfl (CFSG.Quasithin.fixV_anti hA₁_le_A))
  have horbit := (gomi_orbit_bound h31 hW hne hO2 hA).1
  have h1 : Nat.card (autSub A H) * Nat.card (fixV (autSub A H)) *
        Nat.card ↥(U ⊓ fixV A) ≤ Nat.card H * Nat.card ↥(U ⊓ fixV A₁) := by
    calc Nat.card (autSub A H) * Nat.card (fixV (autSub A H)) *
          Nat.card ↥(U ⊓ fixV A)
        ≤ Nat.card H * Nat.card ↥(U ⊓ fixV A) := Nat.mul_le_mul_right _ horbit
      _ ≤ Nat.card H * Nat.card ↥(U ⊓ fixV A₁) := Nat.mul_le_mul_left _ hU_le
  calc gomiW A = Nat.card A * Nat.card (fixV A) := rfl
    _ = (Nat.card (autSub A H) * Nat.card A₁) *
          (Nat.card (fixV (autSub A H)) * Nat.card ↥(U ⊓ fixV A)) := by
        rw [hcardA, hcardFix]
    _ = Nat.card A₁ * (Nat.card (autSub A H) * Nat.card (fixV (autSub A H))) *
          Nat.card ↥(U ⊓ fixV A) := by ring
    _ ≤ Nat.card A₁ * Nat.card H * Nat.card ↥(U ⊓ fixV A₁) := by
        calc Nat.card A₁ * (Nat.card (autSub A H) * Nat.card (fixV (autSub A H))) *
              Nat.card ↥(U ⊓ fixV A)
            = Nat.card A₁ * (Nat.card (autSub A H) * Nat.card (fixV (autSub A H)) *
                Nat.card ↥(U ⊓ fixV A)) := by ring
          _ ≤ Nat.card A₁ * (Nat.card H * Nat.card ↥(U ⊓ fixV A₁)) :=
              Nat.mul_le_mul_left _ h1
          _ = Nat.card A₁ * Nat.card H * Nat.card ↥(U ⊓ fixV A₁) := by ring
    _ = Nat.card A₁ * (Nat.card H * Nat.card ↥(U ⊓ fixV A₁)) := by ring
    _ = Nat.card A₁ * Nat.card (fixV A₁) := by rw [hcardFixA₁]
    _ = gomiW A₁ := rfl

private theorem inf_centSub_eq_bot_of_mem_P0 (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    A ⊓ centSub (commV (gomiGstar0 Y)) = ⊥ := by
  let N : Subgroup (MulAut W) := gomiGstar0 Y
  let H : Subgroup W := commV N
  let U : Subgroup W := fixV N
  let A₁ : Subgroup (MulAut W) := A ⊓ centSub H
  have hle : gomiW A ≤ gomiW A₁ := gomiW_A_le_gomiW_inf_centSub h31 hW hne hO2 hA
  have hle' : gomiW A₁ ≤ gomiW A := gomiW_le_of_mem_Pset hA.1 inf_le_left
  have hWeq : gomiW A = gomiW A₁ := le_antisymm hle hle'
  by_contra hA₁ne
  obtain ⟨B, hBstar, hBle, hBne, hBw⟩ :=
    exists_minimal_Pstar_of_le hA.1 inf_le_left hA₁ne hWeq.symm
  have hA₁_le_A : A₁ ≤ A := inf_le_left
  have hBleA : B ≤ A := hBle.trans hA₁_le_A
  have hBP0 : B ∈ gomiPstar0Set Y := ⟨hBstar, hBleA.trans hA.2⟩
  have hBN : B ≤ N := le_sSup hBP0
  have hBcentH : B ≤ centSub H := hBle.trans inf_le_right
  have hBcentU : B ≤ centSub U := by
    intro b hb u hu
    exact mem_fixV.mp hu b (hBN hb)
  have hCompl : H ⊔ U = ⊤ := (gomi31_facts h31 hW hne hO2).2.2.1
  have hbot : B ≤ ⊥ := by
    have hcent : centSub H ⊓ centSub U = ⊥ := centSub_inf_eq_bot_of_isCompl hCompl
    rw [← hcent]
    exact le_inf hBcentH hBcentU
  exact hBne (le_antisymm hbot bot_le)

private theorem noncommProd_apply_of_trivial_all {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → MulAut W) (v : W)
    (hcomm : (s : Set ι).Pairwise fun i j => Commute (f i) (f j))
    (htriv : ∀ i ∈ s, f i v = v) :
    (s.noncommProd f hcomm) v = v := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.noncommProd_insert_of_notMem t a f hcomm ha, MulAut.mul_apply]
      have htcomm : (t : Set ι).Pairwise fun i j => Commute (f i) (f j) :=
        hcomm.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
      have httriv : ∀ i ∈ t, f i v = v :=
        fun i hi => htriv i (Finset.mem_insert_of_mem hi)
      rw [ih htcomm httriv, htriv a (Finset.mem_insert_self a t)]

private theorem noncommProd_apply_of_trivial {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → MulAut W) (j : ι) (v : W) (hj : j ∈ s)
    (hcomm : (s : Set ι).Pairwise fun i j => Commute (f i) (f j))
    (htriv : ∀ i ∈ s, i ≠ j → f i v = v) :
    (s.noncommProd f hcomm) v = f j v := by
  induction s using Finset.induction_on with
  | empty => simp at hj
  | insert a t ha ih =>
      rw [Finset.noncommProd_insert_of_notMem t a f hcomm ha, MulAut.mul_apply]
      have htcomm : (t : Set ι).Pairwise fun i j => Commute (f i) (f j) :=
        hcomm.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
      have htriv' : ∀ i ∈ t, i ≠ j → f i v = v :=
        fun i hi hij => htriv i (Finset.mem_insert_of_mem hi) hij
      by_cases haj : a = j
      · subst haj
        have htrivall : ∀ i ∈ t, f i v = v := by
          intro i hi
          exact htriv i (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
        rw [noncommProd_apply_of_trivial_all t f v htcomm htrivall]
      · have hjt : j ∈ t := by
          rcases Finset.mem_insert.mp hj with h | h
          · exact absurd h (Ne.symm haj)
          · exact h
        rw [ih hjt htcomm htriv']
        have hcommaj : Commute (f a) (f j) :=
          hcomm (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hjt)
            haj
        rw [show (f a) ((f j) v) = (f j) ((f a) v) by
          rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcommaj.eq]]
        rw [htriv a (Finset.mem_insert_self a t) haj]

private theorem gomiP0_equality (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    let N : Subgroup (MulAut W) := gomiGstar0 Y
    let H : Subgroup W := commV N
    let U : Subgroup W := fixV N
    gomiW A = Nat.card W ∧
      Nat.card (autSub A H) * Nat.card (fixV (autSub A H)) = Nat.card H ∧
      U ≤ fixV A ∧
      (∀ a ∈ autSub A H, ∀ i : ↥(gomiNSet Y),
        ((commV i).subgroupOf H).map (a : MulAut H).toMonoidHom =
          (commV i).subgroupOf H) := by
  let N : Subgroup (MulAut W) := gomiGstar0 Y
  let H : Subgroup W := commV N
  let U : Subgroup W := fixV N
  let A₁ : Subgroup (MulAut W) := A ⊓ centSub H
  have hA₁ : A₁ = ⊥ := inf_centSub_eq_bot_of_mem_P0 h31 hW hne hO2 hA
  have hWeq : gomiW A = gomiW A₁ := le_antisymm
    (gomiW_A_le_gomiW_inf_centSub h31 hW hne hO2 hA)
    (gomiW_le_of_mem_Pset hA.1 inf_le_left)
  have hcardW : gomiW A = Nat.card W := by rw [hWeq, hA₁, gomiW_bot]
  obtain ⟨_, hA_stabH, hA_stabU, hCompl, hDisj'⟩ := gomiP0_setup h31 hW hne hO2 hA
  obtain ⟨hcardA, hcardFix, _⟩ := gomiWeightCardFacts h31 hW hne hO2 hA
  have hcardV : Nat.card W = Nat.card H * Nat.card U := by
    have h := CFSG.Quasithin.card_sup_mul_card_inf H U
    rw [hCompl, hDisj', Subgroup.card_top, Subgroup.card_bot, mul_one] at h
    exact h
  have hprod : (Nat.card (autSub A H) * Nat.card (fixV (autSub A H))) *
        Nat.card ↥(U ⊓ fixV A) = Nat.card H * Nat.card U := by
    have h1 : gomiW A = Nat.card (autSub A H) * Nat.card (fixV (autSub A H)) *
        Nat.card ↥(U ⊓ fixV A) := by
      have hA₁' : A ⊓ centSub (commV (gomiGstar0 Y)) = ⊥ := hA₁
      dsimp only [N, H, U]
      rw [gomiW, hcardA, hcardFix, hA₁', Subgroup.card_bot, mul_one]
      ring
    rw [← hcardV, ← hcardW, h1]
  have hU_le : Nat.card ↥(U ⊓ fixV A) ≤ Nat.card U :=
    Subgroup.card_le_of_le inf_le_left
  have hEq := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims137.eq_of_mul_eq_mul_of_le
    (gomi_orbit_bound h31 hW hne hO2 hA).1 hU_le Nat.card_pos Nat.card_pos hprod
  have hH_eq : Nat.card (autSub A H) * Nat.card (fixV (autSub A H)) = Nat.card H := hEq.1
  have hU_eq : Nat.card ↥(U ⊓ fixV A) = Nat.card U := hEq.2
  have hUle : U ≤ fixV A := by
    have hUinf : U ⊓ fixV A = U := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hU_eq]
    exact hUinf ▸ inf_le_right
  have hPres := (gomi_orbit_bound h31 hW hne hO2 hA).2 hH_eq
  exact ⟨hcardW, hH_eq, hUle, hPres⟩

private theorem map_eq_of_subgroupOf_map_eq [Finite W] {Y : Subgroup W} {J : Subgroup W}
    (hJY : J ≤ Y) {f : MulAut W} (hf : f ∈ stabSub Y)
    (h : (J.subgroupOf Y).map (resHom Y ⟨f, hf⟩) = J.subgroupOf Y) :
    J.map f.toMonoidHom = J := by
  have hle : J.map f.toMonoidHom ≤ J := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
    have hfjY : f j ∈ Y := (mem_stabSub.mp hf j).2 (hJY hj)
    have hmem : (⟨f j, hfjY⟩ : Y) ∈ (J.subgroupOf Y).map (resHom Y ⟨f, hf⟩) := by
      refine Subgroup.mem_map.mpr ⟨⟨j, hJY hj⟩, Subgroup.mem_subgroupOf.mpr hj, ?_⟩
      rfl
    rw [h] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hcard : Nat.card ↥(J.map f.toMonoidHom) = Nat.card ↥J :=
    Subgroup.card_map_of_injective (f := f.toMonoidHom) f.injective
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])

private theorem gomi_step4_stab_commV [Finite W] {Y : Subgroup (MulAut W)} {H : Subgroup W}
    {A : Subgroup (MulAut W)}
    (hSupH : (⨆ i : ↥(gomiNSet Y), commV (i : Subgroup (MulAut W))) = H)
    (hA_stabH : A ≤ stabSub H)
    (hPres : ∀ a ∈ autSub A H, ∀ i : ↥(gomiNSet Y),
      ((commV i).subgroupOf H).map (a : MulAut H).toMonoidHom = (commV i).subgroupOf H) :
    ∀ i : ↥(gomiNSet Y), A ≤ stabSub (commV (i : Subgroup (MulAut W))) := by
  intro i a ha
  rw [mem_stabSub_iff_map_eq]
  have h2 : ((commV i).subgroupOf H).map (resHom H ⟨a, hA_stabH ha⟩) =
      (commV i).subgroupOf H := by
    have hmem : resHom H ⟨a, hA_stabH ha⟩ ∈ autSub A H :=
      mem_autSub.mpr ⟨⟨a, hA_stabH ha⟩, ha, rfl⟩
    exact hPres _ hmem i
  have hJY : commV (i : Subgroup (MulAut W)) ≤ H := by
    rw [← hSupH]
    exact le_iSup (fun j : ↥(gomiNSet Y) => commV (j : Subgroup (MulAut W))) i
  exact map_eq_of_subgroupOf_map_eq hJY (hA_stabH ha) h2

private structure GomiStep4Context (Y : Subgroup (MulAut W)) (A : Subgroup (MulAut W)) where
  N : Subgroup (MulAut W)
  N_eq : N = gomiGstar0 Y
  H : Subgroup W
  U : Subgroup W
  hCompl : H ⊔ U = ⊤
  hSupH : (⨆ i : ↥(gomiNSet Y), commV (i : Subgroup (MulAut W))) = H
  hSupN : sSup (gomiNSet Y) = N
  hN_stab : ∀ i : ↥(gomiNSet Y), (i : Subgroup (MulAut W)) ≤ stabSub (commV i)
  hAut : ∀ i : ↥(gomiNSet Y), autSub (i : Subgroup (MulAut W)) (commV i) = ⊤
  hcommN : ∀ i j : ↥(gomiNSet Y), i ≠ j → ∀ x ∈ (i : Subgroup (MulAut W)),
    ∀ y ∈ (j : Subgroup (MulAut W)), x * y = y * x
  hcent : ∀ i j : ↥(gomiNSet Y), i ≠ j → (i : Subgroup (MulAut W)) ≤
    centSub (commV (j : Subgroup (MulAut W)))
  hA_stabH : A ≤ stabSub H
  hA_stab_commV : ∀ i : ↥(gomiNSet Y), A ≤ stabSub (commV i)
  hPres : ∀ a ∈ autSub A H, ∀ i : ↥(gomiNSet Y),
    ((commV i).subgroupOf H).map (a : MulAut H).toMonoidHom = (commV i).subgroupOf H
  hUle : U ≤ fixV A

private noncomputable def gomi_step4_context (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) : GomiStep4Context Y A := by
  classical
  let N : Subgroup (MulAut W) := gomiGstar0 Y
  let H : Subgroup W := commV N
  let U : Subgroup W := fixV N
  let S := ↥(gomiNSet Y)
  obtain ⟨_, _, hUle, hPres⟩ := gomiP0_equality h31 hW hne hO2 hA
  have hCompl : H ⊔ U = ⊤ := (gomi31_facts h31 hW hne hO2).2.2.1
  have hA_le_norm : A ≤ Subgroup.normalizer (N : Set (MulAut W)) :=
    hA.1.1.trans (gomiGstar0_le_normalizer Y)
  have hA_stabH : A ≤ stabSub H := le_stabSub_commV_of_le_normalizer hA_le_norm
  have hSupH : (⨆ i : S, commV (i : Subgroup (MulAut W))) = H :=
    (gomi31_facts h31 hW hne hO2).2.1.2.2
  have hSupN : sSup (gomiNSet Y) = N :=
    (gomi31_facts h31 hW hne hO2).1.2.2.2
  have hNat : ∀ i : S, BinaryNaturalSL (i : Subgroup (MulAut W))
      (commV (i : Subgroup (MulAut W))) ⊥ 2 1 := fun i =>
    (gomi31_facts h31 hW hne hO2).2.1.1 (i : Subgroup (MulAut W)) i.2
  have hN_stab : ∀ i : S, (i : Subgroup (MulAut W)) ≤
      stabSub (commV (i : Subgroup (MulAut W))) := by
    intro i
    obtain ⟨πi, hπi⟩ := CFSG.Quasithin.G64.BinaryNaturalSL.exists_zmod (hNat i)
    exact le_stabSub_of_binaryNaturalSL hπi
  have hAut : ∀ i : S, autSub (i : Subgroup (MulAut W))
      (commV (i : Subgroup (MulAut W))) = ⊤ := fun i =>
    autSub_eq_top_of_binaryNaturalSL h31 hW hne hO2 i.2
  have hcommN : ∀ i j : S, i ≠ j → ∀ x ∈ (i : Subgroup (MulAut W)),
      ∀ y ∈ (j : Subgroup (MulAut W)), x * y = y * x := by
    intro i j hij
    exact (gomi31_facts h31 hW hne hO2).1.2.2.1 i.2 j.2 (fun h => hij (Subtype.ext h))
  have hcent : ∀ i j : S, i ≠ j → (i : Subgroup (MulAut W)) ≤
      centSub (commV (j : Subgroup (MulAut W))) := by
    intro i j hij
    exact gomiNSet_le_centSub_of_ne h31 hW hne hO2
      (fun h => hij (Subtype.ext (congrArg Subtype.val h)))
  have hA_stab_commV : ∀ i : S, A ≤ stabSub (commV (i : Subgroup (MulAut W))) :=
    gomi_step4_stab_commV hSupH hA_stabH hPres
  have hN_eq : N = gomiGstar0 Y := by
    rw [← hSupN]
    exact (gomi31_facts h31 hW hne hO2).1.2.2.2
  exact ⟨N, hN_eq, H, U, hCompl, hSupH, hSupN, hN_stab, hAut, hcommN,
    hcent, hA_stabH, hA_stab_commV, hPres, hUle⟩

private structure GomiNChoice (Y : Subgroup (MulAut W)) (A : Subgroup (MulAut W))
    (C : GomiStep4Context Y A) where
  n : (↥(gomiNSet Y)) → A → MulAut W
  mem : ∀ (i : ↥(gomiNSet Y)) (a : A), n i a ∈ (i : Subgroup (MulAut W))
  stab : ∀ (i : ↥(gomiNSet Y)) (a : A), n i a ∈
    stabSub (commV (i : Subgroup (MulAut W)))
  res : ∀ (i : ↥(gomiNSet Y)) (a : A),
    resHom (commV (i : Subgroup (MulAut W))) ⟨n i a, stab i a⟩ =
      resHom (commV (i : Subgroup (MulAut W))) ⟨a.1, C.hA_stab_commV i a.2⟩
  memN : ∀ (i : ↥(gomiNSet Y)) (a : A), n i a ∈ C.N

private noncomputable def gomi_step4_choose (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) :
    GomiNChoice Y A (gomi_step4_context h31 hW hne hO2 hA) := by
  classical
  let C := gomi_step4_context h31 hW hne hO2 hA
  let S := ↥(gomiNSet Y)
  let n : S → A → MulAut W := fun i a =>
    (Classical.choose (mem_autSub.mp (show
      resHom (commV (i : Subgroup (MulAut W)))
          ⟨a.1, C.hA_stab_commV i a.2⟩ ∈ autSub (i : Subgroup (MulAut W))
            (commV (i : Subgroup (MulAut W))) by
        rw [C.hAut i]
        exact Subgroup.mem_top _))).1
  have hn_mem : ∀ (i : S) (a : A), n i a ∈ (i : Subgroup (MulAut W)) := by
    intro i a
    exact (Classical.choose_spec (mem_autSub.mp (show
      resHom (commV (i : Subgroup (MulAut W)))
          ⟨a.1, C.hA_stab_commV i a.2⟩ ∈ autSub (i : Subgroup (MulAut W))
            (commV (i : Subgroup (MulAut W))) by
        rw [C.hAut i]
        exact Subgroup.mem_top _))).1
  have hn_stab : ∀ (i : S) (a : A), n i a ∈
      stabSub (commV (i : Subgroup (MulAut W))) :=
    fun i a => C.hN_stab i (hn_mem i a)
  have hn_res : ∀ (i : S) (a : A),
      resHom (commV (i : Subgroup (MulAut W))) ⟨n i a, hn_stab i a⟩ =
        resHom (commV (i : Subgroup (MulAut W))) ⟨a.1, C.hA_stab_commV i a.2⟩ := by
    intro i a
    exact (Classical.choose_spec (mem_autSub.mp (show
      resHom (commV (i : Subgroup (MulAut W)))
          ⟨a.1, C.hA_stab_commV i a.2⟩ ∈ autSub (i : Subgroup (MulAut W))
            (commV (i : Subgroup (MulAut W))) by
        rw [C.hAut i]
        exact Subgroup.mem_top _))).2
  have hN_mem : ∀ (i : S) (a : A), n i a ∈ C.N := by
    intro i a
    have h1 : (i : Subgroup (MulAut W)) ≤ C.N := by
      rw [← C.hSupN]
      exact le_sSup i.2
    exact h1 (hn_mem i a)
  exact ⟨n, hn_mem, hn_stab, hn_res, hN_mem⟩

private noncomputable def gomi_step4_nsum [Finite W] {Y : Subgroup (MulAut W)}
    {A : Subgroup (MulAut W)} {C : GomiStep4Context Y A}
    (D : GomiNChoice Y A C) (a : A) : MulAut W := by
  classical
  letI : Fintype (↥(gomiNSet Y)) := fintypeGomiNSet Y
  exact (Finset.univ : Finset (↥(gomiNSet Y))).noncommProd (fun i => D.n i a) (by
    intro i _ j _ hij
    exact show Commute (D.n i a) (D.n j a) from
      C.hcommN i j hij (D.n i a) (D.mem i a) (D.n j a) (D.mem j a))

private noncomputable def gomi_step4_nsum_mem_plift [Finite W] {Y : Subgroup (MulAut W)}
    {A : Subgroup (MulAut W)} {C : GomiStep4Context Y A}
    (D : GomiNChoice Y A C) (a : A) : PLift (gomi_step4_nsum D a ∈ C.N) := by
  classical
  letI : Fintype (↥(gomiNSet Y)) := fintypeGomiNSet Y
  exact ⟨Subgroup.noncommProd_mem C.N _ (fun i _ => D.memN i a)⟩

private theorem gomi_step4_nsum_mem [Finite W] {Y : Subgroup (MulAut W)}
    {A : Subgroup (MulAut W)} {C : GomiStep4Context Y A}
    (D : GomiNChoice Y A C) (a : A) : gomi_step4_nsum D a ∈ C.N :=
  (gomi_step4_nsum_mem_plift D a).down

private noncomputable def gomi_step4_nsum_apply_plift [Finite W] {Y : Subgroup (MulAut W)}
    {A : Subgroup (MulAut W)} {C : GomiStep4Context Y A}
    (D : GomiNChoice Y A C) (a : A) (j : ↥(gomiNSet Y)) (v : W)
    (hv : v ∈ commV (j : Subgroup (MulAut W))) :
    PLift (gomi_step4_nsum D a v = a.1 v) := by
  classical
  letI : Fintype (↥(gomiNSet Y)) := fintypeGomiNSet Y
  have hcomm : ((Finset.univ : Finset (↥(gomiNSet Y))) : Set _).Pairwise
      fun i k => Commute (D.n i a) (D.n k a) := by
    intro i _ k _ hik
    exact show Commute (D.n i a) (D.n k a) from
      C.hcommN i k hik (D.n i a) (D.mem i a) (D.n k a) (D.mem k a)
  have htriv : ∀ i ∈ (Finset.univ : Finset (↥(gomiNSet Y))), i ≠ j →
      D.n i a v = v := by
    intro i _ hij
    have hcent : (i : Subgroup (MulAut W)) ≤ centSub (commV (j : Subgroup (MulAut W))) :=
      C.hcent i j hij
    exact hcent (D.mem i a) v hv
  have h := noncommProd_apply_of_trivial (Finset.univ : Finset (↥(gomiNSet Y)))
    (fun i => D.n i a) j v (Finset.mem_univ j) hcomm htriv
  rw [show gomi_step4_nsum D a = (Finset.univ : Finset (↥(gomiNSet Y))).noncommProd
    (fun i => D.n i a) _ from rfl]
  rw [h]
  have hres := D.res j a
  have hv' : ((⟨D.n j a, D.stab j a⟩ :
      stabSub (commV (j : Subgroup (MulAut W)))) : MulAut W) v = a.1 v := by
    have := congrArg (fun f : MulAut (commV (j : Subgroup (MulAut W))) =>
      (f ⟨v, hv⟩ : commV (j : Subgroup (MulAut W)))) hres
    exact congrArg Subtype.val this
  exact ⟨hv'⟩

private theorem gomi_step4_nsum_apply [Finite W] {Y : Subgroup (MulAut W)}
    {A : Subgroup (MulAut W)} {C : GomiStep4Context Y A}
    (D : GomiNChoice Y A C) (a : A) (j : ↥(gomiNSet Y)) (v : W)
    (hv : v ∈ commV (j : Subgroup (MulAut W))) :
    gomi_step4_nsum D a v = a.1 v :=
  (gomi_step4_nsum_apply_plift D a j v hv).down

private theorem gomi_step4_eq (h31 : GomiFact31) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hne : (gomiPstar0Set Y).Nonempty) (hO2 : O2Trivial (gomiGstar0 Y))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiP0Set Y) : A ≤ gomiGstar0 Y := by
  let C := gomi_step4_context h31 hW hne hO2 hA
  let D := gomi_step4_choose h31 hW hne hO2 hA
  intro a ha
  let a' : A := ⟨a, ha⟩
  let nsum : MulAut W := gomi_step4_nsum D a'
  have hnsum_mem : nsum ∈ C.N := gomi_step4_nsum_mem D a'
  have hnsum_apply : ∀ (i : ↥(gomiNSet Y)) (v : W),
      v ∈ commV (i : Subgroup (MulAut W)) → nsum v = a v := by
    intro i v hv
    exact gomi_step4_nsum_apply D a' i v hv
  let E : Subgroup W :=
    { carrier := {x : W | nsum x = a x}
      one_mem' := by
        show nsum 1 = a 1
        rw [map_one, map_one]
      mul_mem' := by
        intro x y hx hy
        show nsum (x * y) = a (x * y)
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        show nsum x⁻¹ = a x⁻¹
        rw [map_inv, map_inv, hx] }
  have hH_le : C.H ≤ E := by
    rw [← C.hSupH]
    refine iSup_le fun i => ?_
    intro x hx
    exact hnsum_apply i x hx
  have hU_le : C.U ≤ E := by
    intro u hu
    show nsum u = a u
    rw [mem_fixV.mp hu _ hnsum_mem, mem_fixV.mp (C.hUle hu) a ha]
  have hEqAut : a = nsum := by
    ext w
    have hEtop : E = ⊤ := by
      rw [eq_top_iff, ← C.hCompl]
      exact sup_le hH_le hU_le
    exact (show w ∈ E from hEtop ▸ Subgroup.mem_top w).symm
  have haN : a ∈ C.N := by
    rw [hEqAut]
    exact hnsum_mem
  rw [← C.N_eq]
  exact haN

theorem gomiFact32_of_gomiFact31 (h31 : GomiFact31) : GomiFact32 := by
  intro W _ _ hW Y hO2
  by_cases hne : (gomiPstar0Set Y).Nonempty
  · apply le_antisymm
    · refine sSup_le fun A hA => ?_
      exact gomi_step4_eq h31 hW hne hO2 hA
    · refine sSup_le fun A hA => ?_
      exact le_sSup (show A ∈ gomiP0Set Y from ⟨hA.1.1, hA.2⟩)
  · have hP0 : gomiP0Set Y = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro A hA
      obtain ⟨B, hBstar, hBle, hBne, hBw⟩ :=
        exists_minimal_Pstar_of_le hA.1 le_rfl (ne_bot_of_mem_Pset hA.1) rfl
      exact hne ⟨B, hBstar, hBle.trans hA.2⟩
    have hPstar0 : gomiPstar0Set Y = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [gomiG0, gomiGstar0, hP0, hPstar0]

theorem gomiFact32_holds : GomiFact32 :=
  gomiFact32_of_gomiFact31 gomiFact31_holds

end CFSG.GroupTheory

end
