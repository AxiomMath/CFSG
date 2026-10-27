module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClInner
public import CFSG.Assembly.LargeEvenGLABridge
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5ClassAb
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.Assembly.OpenBridges
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClRed
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.Line63.H5 CFSG.StandardType.TableBUD

@[expose] def U6Type9LayerInner : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData 2 n K), 3 ∣ 2 ^ n + 1 →
    ∀ (M N : GL (Fin 6) K) (_ : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n))
      (_ : N ∈ LargeEvenGUSet (Fin 6) K (2 ^ n))
      (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
      (hNN : N ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
      M ^ 3 = 1 → M ∉ LargeEvenScalars (Fin 6) K →
      N * M * N⁻¹ * M⁻¹ ∈ LargeEvenScalars (Fin 6) K →
      CFSG.Assembly.IsComponentOf
          (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)))
          (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)) →
      ∃ (g : GL (Fin 6) K) (hg : g ∈ unitarySU 2 n K 6),
        LargeEvenProjMk (unitarySU 2 n K 6) ⟨g, hg⟩ ∈
            LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)) ∧
          ∀ t ∈ LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)),
            TableB.projConj (unitarySU 2 n K 6) ⟨N, hNN⟩ t =
              TableB.projConj (unitarySU 2 n K 6) ⟨g, Subgroup.le_normalizer hg⟩ t


theorem mem_scalars_of_projConj_commutator {n : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) {M N : GL (Fin 6) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hN : N ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hc : TableB.projConj (unitarySU 2 n K 6) ⟨N, hN⟩ *
        TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩ =
      TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩ *
        TableB.projConj (unitarySU 2 n K 6) ⟨N, hN⟩) :
    N * M * N⁻¹ * M⁻¹ ∈ LargeEvenScalars (Fin 6) K := by
  have hXN : N * M * N⁻¹ * M⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hN hM) (Subgroup.inv_mem _ hN))
      (Subgroup.inv_mem _ hM)
  have hproj : TableB.projConj (unitarySU 2 n K 6) ⟨N * M * N⁻¹ * M⁻¹, hXN⟩ = 1 := by
    have heq : (⟨N * M * N⁻¹ * M⁻¹, hXN⟩ :
        ↥(Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))) =
        ⟨N, hN⟩ * ⟨M, hM⟩ * ⟨N, hN⟩⁻¹ * ⟨M, hM⟩⁻¹ := Subtype.ext rfl
    rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hproj' : TableB.projConj (unitarySU 2 n K 6) ⟨N * M * N⁻¹ * M⁻¹, hXN⟩ =
      TableB.projConj (unitarySU 2 n K 6) ⟨1, Subgroup.one_mem _⟩ := by
    rw [hproj]
    exact (map_one _).symm
  obtain ⟨c, hc'⟩ := exists_scalar_mul_of_projConj_eq (M := N * M * N⁻¹ * M⁻¹) (M' := 1)
    h hpq hXN (Subgroup.one_mem _) hproj'
  rw [mul_one] at hc'
  rw [largeEvenScalars_def, hc']
  exact ⟨c, rfl⟩

section Certificates


theorem u6Type9Core_of_descent_of_layerInner (hD : ComponentDescent)
    (hInner : U6Type9LayerInner) : U6Type9Core := by
  intro G _ _ L J A d b n K _ _ h θ hS hpq hmark M hMgu hMN hM3 hφd
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hdA : d ∈ A := hS.d_mem
  have hbA : b ∈ A := hS.b_mem
  have hbd : b * d = d * b := by
    have h1 := hS.elem.1.is_comm.comm ⟨b, hbA⟩ ⟨d, hdA⟩
    exact congrArg Subtype.val h1
  have hLperf : Group.IsPerfect ↥L := ⟨hS.qs.1⟩
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hdA
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hbA
  have hMnotscal : M ∉ LargeEvenScalars (Fin 6) K := by
    intro hsc
    have hcM : TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ = 1 :=
      TableB.projConj_of_scalar _ hsc
    rw [hcM] at hφd
    have hcenter := exists_center_of_largeEvenInduces_one (L := L) hdN hφd
    have hcent : d ∈ Subgroup.centralizer (L : Set G) :=
      centralizes_of_conjRel_center (L := L) hdN hcenter hLperf
    have hbot : d ∈ (⊥ : Subgroup G) := by
      have hmem : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hdA, hcent⟩
      rwa [hS.faithful] at hmem
    exact hS.d_ne (Subgroup.mem_bot.mp hbot)
  have hdes := hD G L hS.qs (LargeEvenProj (unitarySU 2 n K 6)) θ d hdN
    (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) hφd J
    ((isComponentOf_iff_open).mpr hS.comp.1)
    (by rw [CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer]; exact hS.comp.2)
  obtain ⟨hdes1, hdes2⟩ := hdes
  have hfix : ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) =
      CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
        (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) := rfl
  have hcomp : CFSG.Assembly.IsComponentOf
      (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)) := by
    rw [hfix, hdes2]
    exact hdes1
  obtain ⟨φb, hφb_mem, hφb_ind⟩ := hmark b hbA
  obtain ⟨N, hNgu, hφb_eq⟩ := TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer h) hφb_mem
  have hNN : N ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer h hNgu
  have hφN : TableB.projConj (unitarySU 2 n K 6) ⟨N, hNN⟩ = φb := by
    rw [hφb_eq]
    exact congrArg _ (Subtype.ext rfl)
  have hcongr : TableB.projConj (unitarySU 2 n K 6) ⟨N, hNN⟩ *
      TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ =
      TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ *
        TableB.projConj (unitarySU 2 n K 6) ⟨N, hNN⟩ := by
    have h1 : LargeEvenInduces θ (conjRel (b * d))
        (φb * TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) :=
      largeEvenInduces_mul hbN hdN hbd hφb_ind hφd
    have h2 : LargeEvenInduces θ (conjRel (d * b))
        (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ * φb) :=
      largeEvenInduces_mul hdN hbN hbd.symm hφd hφb_ind
    rw [← hbd] at h2
    have huniq := largeEvenInduces_unique h1 h2
      (conjRel_total (Subgroup.mul_mem _ hbN hdN))
    rw [hφN]
    exact huniq
  have hscal : N * M * N⁻¹ * M⁻¹ ∈ LargeEvenScalars (Fin 6) K :=
    mem_scalars_of_projConj_commutator h hpq hMN hNN hcongr
  obtain ⟨g, hgSU, hglayer, hgact⟩ :=
    hInner n K h hpq M N hMgu hNgu hMN hNN hM3 hMnotscal hscal hcomp
  have hT : LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)) =
      (J.subgroupOf L).map (piCenterQuot θ) := by
    rw [hfix, hdes2]
  obtain ⟨x, hxJ, hxeq⟩ := Subgroup.mem_map.mp (by rw [← hT]; exact hglayer)
  have hxG : ((x : ↥L) : G) ∈ J := Subgroup.mem_subgroupOf.mp hxJ
  have hmod : ∀ j ∈ J, ∃ z : ↥L, (z : G) ∈ J ∧ z ∈ Subgroup.center ↥L ∧
      b⁻¹ * j * b = (((x : ↥L) : G) * j * ((x : ↥L) : G)⁻¹) * (z : G) := by
    intro j hj
    have hjL : j ∈ L := (hS.comp.1.1 hj).1
    have hbjJ : b⁻¹ * j * b ∈ J :=
      (Subgroup.mem_normalizer_iff''.mp hS.b_norm j).mp hj
    have hbjL : b⁻¹ * j * b ∈ L := (hS.comp.1.1 hbjJ).1
    have hkjL : ((x : ↥L) : G) * j * ((x : ↥L) : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem x.2 hjL) (L.inv_mem x.2)
    let jL : ↥L := ⟨j, hjL⟩
    let bjL : ↥L := ⟨b⁻¹ * j * b, hbjL⟩
    let kL : ↥L := ⟨((x : ↥L) : G) * j * ((x : ↥L) : G)⁻¹, hkjL⟩
    have h1 : φb (θ (QuotientGroup.mk jL)) = θ (QuotientGroup.mk bjL) :=
      hφb_ind jL bjL rfl
    have h2 : θ (QuotientGroup.mk bjL) =
        TableB.projConj (unitarySU 2 n K 6) ⟨N, hNN⟩ (θ (QuotientGroup.mk jL)) := by
      rw [hφN]
      exact h1.symm
    have hjT : θ (QuotientGroup.mk jL) ∈
        LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩)) := by
      rw [hT]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hj)
    have h3 : TableB.projConj (unitarySU 2 n K 6) ⟨N, hNN⟩ (θ (QuotientGroup.mk jL)) =
        TableB.projConj (unitarySU 2 n K 6) ⟨g, Subgroup.le_normalizer hgSU⟩
          (θ (QuotientGroup.mk jL)) :=
      hgact _ hjT
    have h4 : TableB.projConj (unitarySU 2 n K 6) ⟨g, Subgroup.le_normalizer hgSU⟩
          (θ (QuotientGroup.mk jL)) = θ (QuotientGroup.mk kL) := by
      rw [TableB.projConj_of_mem (unitarySU 2 n K 6) g hgSU, MulAut.conj_apply]
      have h7 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) * QuotientGroup.mk jL *
          (QuotientGroup.mk x)⁻¹ = QuotientGroup.mk kL := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subtype.ext rfl)
      have h7b : (piCenterQuot θ) x * θ (QuotientGroup.mk jL) * ((piCenterQuot θ) x)⁻¹ =
          θ (QuotientGroup.mk kL) := by
        have hxe : (piCenterQuot θ) x = θ (QuotientGroup.mk x) := rfl
        rw [hxe, ← h7, map_mul, map_mul, map_inv]
      calc (LargeEvenProjMk (unitarySU 2 n K 6) ⟨g, hgSU⟩) * θ (QuotientGroup.mk jL) *
            (LargeEvenProjMk (unitarySU 2 n K 6) ⟨g, hgSU⟩)⁻¹
          = (piCenterQuot θ) x * θ (QuotientGroup.mk jL) * ((piCenterQuot θ) x)⁻¹ := by
            rw [← hxeq]
        _ = θ (QuotientGroup.mk kL) := h7b
    have h8 : θ (QuotientGroup.mk bjL) = θ (QuotientGroup.mk kL) := by
      rw [h2, h3, h4]
    have h8' : QuotientGroup.mk bjL = QuotientGroup.mk kL := θ.injective h8
    have hz : bjL⁻¹ * kL ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.eq]
      exact h8'
    have hkJ : (((x : ↥L) : G) * j * ((x : ↥L) : G)⁻¹) ∈ J :=
      J.mul_mem (J.mul_mem hxG hj) (J.inv_mem hxG)
    have hzJ : ((kL⁻¹ * bjL : ↥L) : G) ∈ J := by
      have h1 : ((kL⁻¹ * bjL : ↥L) : G) =
          ((kL : ↥L) : G)⁻¹ * ((bjL : ↥L) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h1]
      exact J.mul_mem (J.inv_mem hkJ) hbjJ
    have hz' : kL⁻¹ * bjL ∈ Subgroup.center ↥L := by
      have h1 : kL⁻¹ * bjL = (bjL⁻¹ * kL)⁻¹ := by group
      rw [h1]
      exact Subgroup.inv_mem _ hz
    refine ⟨kL⁻¹ * bjL, hzJ, hz', ?_⟩
    have h9 : ((kL⁻¹ * bjL : ↥L) : G) =
        (((x : ↥L) : G) * j * ((x : ↥L) : G)⁻¹)⁻¹ * (b⁻¹ * j * b) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h9]
    group
  haveI hJperf : Group.IsPerfect ↥J := ⟨hS.comp.1.2.2.1⟩
  set σb : MulAut ↥J := J.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hS.b_norm⟩ with hσbdef
  set σx : MulAut ↥J := J.normalizerMonoidHom ⟨((x : ↥L) : G), Subgroup.le_normalizer hxG⟩
    with hσxdef
  have hσb_apply : ∀ y : ↥J, ((σb y : ↥J) : G) = b⁻¹ * (y : G) * b := by
    intro y
    show b⁻¹ * (y : G) * (b⁻¹)⁻¹ = b⁻¹ * (y : G) * b
    rw [inv_inv]
  have hσx_apply : ∀ y : ↥J,
      ((σx y : ↥J) : G) = ((x : ↥L) : G) * (y : G) * ((x : ↥L) : G)⁻¹ := by
    intro y
    show ((x : ↥L) : G) * (y : G) * (((x : ↥L) : G))⁻¹ = _
    rfl
  have hdisp : ∀ y : ↥J, y⁻¹ * ((σb * σx⁻¹) y) ∈ Subgroup.center ↥J := by
    intro y
    obtain ⟨z, hzJ, hzZ, hzy⟩ := hmod ((σx⁻¹ y : ↥J) : G) (σx⁻¹ y).2
    have hzJc : (⟨(z : G), hzJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      show (w : G) * (z : G) = (z : G) * (w : G)
      have hwL : (w : G) ∈ L := (hS.comp.1.1 w.2).1
      have hcz := Subgroup.mem_center_iff.mp hzZ ⟨(w : G), hwL⟩
      exact congrArg Subtype.val hcz
    have hval : ((σb * σx⁻¹) y : ↥J) = y * ⟨(z : G), hzJ⟩ := by
      apply Subtype.ext
      show ((σb (σx⁻¹ y) : ↥J) : G) = (y : G) * (z : G)
      rw [hσb_apply, hzy]
      have hxw : (((x : ↥L) : G) * ((σx⁻¹ y : ↥J) : G) * ((x : ↥L) : G)⁻¹) = (y : G) := by
        have h1 : σx (σx⁻¹ y) = y := by simp
        rw [← hσx_apply]
        exact congrArg Subtype.val h1
      rw [hxw]
    rw [hval]
    have he : y⁻¹ * (y * ⟨(z : G), hzJ⟩) = ⟨(z : G), hzJ⟩ := by group
    rw [he]
    exact hzJc
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    (G := ↥J) (σb * σx⁻¹) hdisp
  have hσinv : (σb * σx⁻¹ : MulAut ↥J) = 1 := by
    ext z
    have hz : (σb * σx⁻¹) z = z := by
      have h := DFunLike.congr_fun hid z
      simpa using h
    simpa using hz
  have hσeq : σb = σx := by
    calc σb = σb * σx⁻¹ * σx := by group
      _ = 1 * σx := by rw [hσinv]
      _ = σx := one_mul _
  refine hS.nonID (innDiagOn_of_innerOn hS.prime hS.pcomp hS.chevJ hS.b_norm ?_)
  refine ⟨((x : ↥L) : G)⁻¹, J.inv_mem hxG, fun j hj => ?_⟩
  have hbjJ : b * j * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hS.b_norm j).mp hj
  have h1 := congrArg (fun f : MulAut ↥J => f ⟨b * j * b⁻¹, hbjJ⟩) hσeq
  have h2 : ((σb ⟨b * j * b⁻¹, hbjJ⟩ : ↥J) : G) = j := by
    rw [hσb_apply]
    group
  have h3 : ((σx ⟨b * j * b⁻¹, hbjJ⟩ : ↥J) : G) =
      ((x : ↥L) : G) * (b * j * b⁻¹) * ((x : ↥L) : G)⁻¹ := by
    rw [hσx_apply]
  have h4 : j = ((x : ↥L) : G) * (b * j * b⁻¹) * ((x : ↥L) : G)⁻¹ := by
    have h5 := congrArg Subtype.val h1
    rw [h2, h3] at h5
    exact h5
  have key : b * j * b⁻¹ = ((x : ↥L) : G)⁻¹ * j * ((x : ↥L) : G) := by
    conv_rhs => rw [h4]
    group
  simpa using key

theorem u6Type9_of_descent_of_layerInner (hD : ComponentDescent)
    (hInner : U6Type9LayerInner) : U6Type9 :=
  u6Type9_of_core (u6Type9Core_of_descent_of_layerInner hD hInner)

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
