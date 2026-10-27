module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.Basic

import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.NT44.RigidPump
import CFSG.GH74.GLS.NT44.RigidCoverage
import CFSG.GH74.GLS.NT44.RigidPumpExistence
import CFSG.GH74.GLS.NT44.RigidCenterSylow
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
import CFSG.GH74.GLS.C3.Layer1.St1RigGen
import CFSG.GH74.GLS.C3.Layer1.Th2Pump
import CFSG.GH74.GLS.NT44.RigidCenterInclusion
import CFSG.GH74.GLS.NT44.RigidCentralInvolution
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.GH74.GLS.Bg.Iii2.CMAux
import CFSG.GH74.GLS.Bg.Iii2.CMPU
import CFSG.GH74.GLS.Bg.Iii2.ExtBasic
import CFSG.GH74.GLS.Bg.Pu5.Statements
import CFSG.GH74.GLS.IVK.Lifted.GroupAux
import CFSG.GH74.GLS.IVK.Lifted.IIAutB
import CFSG.GH74.GLS.IVK.Lifted.Strong
import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1
import CFSG.GH74.GLS.Stage1.Thm4.Core98
import CFSG.GH74.Uniqueness.SU.KInputs2
import CFSG.GH74.Uniqueness.SU.SU13TA1Class
import CFSG.GH74.Uniqueness.SU.SU8Stmts
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS.Stage1.Thm4

theorem mem_inf_zStar_kz_of_isConj_of_mem_cSec_of_even
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {x y : G} {K T : Subgroup G}
    (hK : K ∈ RigidSet fullQ x)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (Subgroup.centralizer ({x} : Set G)))
    (hEven : Even (Nat.card (Subgroup.center fullQ)))
    (hxZ : x ∈ zStar (Kz fullQ x))
    (hmax : ∀ a : G, orderOf a = 2 →
      (RigidSet fullQ a).ncard ≤ (RigidSet fullQ x).ncard)
    (hyT : y ∈ T)
    (hconj : IsConj x y)
    (hysec : y ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    y ∈ T ⊓ zStar (Kz fullQ x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : IsRigidOfType fullQ x K := hK
  have hx2 : orderOf x = 2 := hK'.1.1.1
  have hKil : IsILo 2 x K := hK'.1.1
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hK'.1.1.2.2
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    let Y : Subgroup G := centralizer ({x} : Set G)
    have hcomp : CFSG.IsComponent
        (CFSG.GH74.GLS.C3.Layer1.PumpCalc.bar x K) :=
      CFSG.GH74.GLS.C3.Layer1.PumpCalc.isComponent_bar (u := x) hKc
    obtain ⟨a, _ha, b, _hb, hab⟩ :=
      CFSG.GH74.GLS.C3.Layer1.PumpRigid.exists_noncomm_of_isComponent
        (L := CFSG.GH74.GLS.C3.Layer1.PumpCalc.bar x K) hcomp
    obtain ⟨a0, ha0⟩ := CFSG.GH74.GLS.TwoThin.barMk_surjective (Y := Y) a
    obtain ⟨b0, hb0⟩ := CFSG.GH74.GLS.TwoThin.barMk_surjective (Y := Y) b
    refine ⟨(a0 : G), (b0 : G), ?_⟩
    intro hcomm
    apply hab
    have hY : a0 * b0 = b0 * a0 := Subtype.ext hcomm
    have hq : CFSG.GH74.GLS.TwoThin.barMk Y a0 * CFSG.GH74.GLS.TwoThin.barMk Y b0 =
        CFSG.GH74.GLS.TwoThin.barMk Y b0 * CFSG.GH74.GLS.TwoThin.barMk Y a0 := by
      rw [← map_mul, hY, map_mul]
    simpa only [ha0, hb0] using hq
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hcy : y = c * x * c⁻¹ := hc.symm
  have hy2 : orderOf y = 2 := by
    rw [hcy]
    exact (CFSG.GH74.GLS.Bg.Pu5.orderOf_conj_eq' c x).trans hx2
  let Cx : Subgroup G := centralizer ({x} : Set G)
  let Zx : Subgroup G := zStar (Kz fullQ x)
  let W : Subgroup G := T ⊓ Zx
  let Cy : Subgroup G := centralizer ({y} : Set G)
  let Zy : Subgroup G := zStar (Kz fullQ y)
  let A : Subgroup G := T ⊓ Cy
  have hZxle : Zx ≤ Cx := by
    intro z hz
    exact kz_le_centralizer (Q := fullQ) (z := x) hz.1
  have hCxNP : Cx ≤ normalizer (Kz fullQ x : Set G) := by
    simpa only [Cx] using (centralizer_le_normalizer_kz (Q := fullQ) (z := x))
  have hCxNZ : Cx ≤ normalizer (Zx : Set G) := by
    intro z hz
    exact CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_normalizer_zStar
      (K := Kz fullQ x) (hCxNP hz)
  have hW : CFSG.ABGLocalTools.IsSylowOf 2 W Zx :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hT hZxle hCxNZ
  obtain ⟨s, hsTZ, hs2⟩ := exists_involution_inf_zStar_of_mem_rigidSet_of_even hK hT hEven
  have hsW : s ∈ W :=
    ⟨hsTZ.1, zStar_le_zStar_kz_of_mem_rigidSet hK hsTZ.2⟩
  have hyCx : y ∈ Cx := hT.le hyT
  have h3x : 3 ≤ pRank 2 ↥Cx := by
    have h2 : oBound 2 ≤ pRank 2 ↥Cx := hKil.2.1
    have h3' : oBound 2 = 3 := by simp [oBound]
    rwa [h3'] at h2
  have h3G : 3 ≤ pRank 2 G :=
    h3x.trans (CFSG.GH74.GLS.Bg.pRank_subgroup_le (p := 2) (by norm_num) Cx)
  have hRy : 3 ≤ pRank 2 ↥Cy :=
    CFSG.GH74.GLS.TwoThin.rankThreeCentralizers G
      (inferInstance : IsSimpleGroup G) hnonab h3G y hy2
  obtain ⟨M, hM⟩ :=
    CFSG.GH74.GLS.TwoThin.exists_pumpup_of_involution (x := x) (u := y) (K := K)
      hx2 hy2 hKc hyCx hysec hKil hRy
  have hsy : s * y = y * s :=
    CFSG.GH74.GLS.Bg.Pu5.comm_of_mem_cSec hT.isPGroup hsTZ.1 hyT hsTZ.2.1 hysec
  have hsCy : s ∈ Cy := Subgroup.mem_centralizer_singleton_iff.mpr hsy
  have hs2pow : ∃ n : ℕ, s ^ (2 ^ n) = 1 :=
    ⟨1, by have := pow_orderOf_eq_one s; rwa [hs2, ← pow_one 2] at this⟩
  have hsZy : s ∈ zStar (Kz fullQ y) :=
    mem_zStar_kz_of_pumpUpLT (fullQ := fullQ) (x := x) (t := y) (y := s)
      (K := K) (K' := M) hK' hM hsTZ.2 hs2pow hsCy
  have hyZ : y ∈ zStar (Kz fullQ y) := by
    rw [hcy, kz_conj (Q := fullQ) c]
    change c * x * c⁻¹ ∈ CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap c (Kz fullQ x) ∧
      c * x * c⁻¹ ∈ centralizerSection (CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap c (Kz fullQ x))
        (pPrimeCoreOf 2 (CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap c (Kz fullQ x)))
    exact ⟨CFSG.GH74.GLS.Bg.Pu5.conj_mem_cmap' hxZ.1 c,
      CFSG.GH74.GLS.Bg.Pu5.conj_mem_cSec_cmap hxZ.2 c⟩
  have hny : (RigidSet fullQ y).ncard = (RigidSet fullQ x).ncard := by
    rw [hcy]
    exact ncard_rigidSet_conj (Q := fullQ) (z := x) c
  have hZyle : Zy ≤ Cy := by
    intro z hz
    exact kz_le_centralizer (Q := fullQ) (z := y) hz.1
  have hCyNP : Cy ≤ normalizer (Kz fullQ y : Set G) := by
    simpa only [Cy] using (centralizer_le_normalizer_kz (Q := fullQ) (z := y))
  have hCyNZ : Cy ≤ normalizer (Zy : Set G) := by
    intro z hz
    exact CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_normalizer_zStar
      (K := Kz fullQ y) (hCyNP hz)
  have hyCy : y ∈ Cy := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hA2 : IsPGroup 2 ↥A := hT.isPGroup.to_inf_left
  have hACy : A ≤ Cy := inf_le_right
  obtain ⟨U, hU, hAU⟩ :=
    CFSG.GH74.GLS.Stage1.Thm4.P92.exists_sylow_ge (S := A) (C := Cy) hA2 hACy
  let V : Subgroup G := U ⊓ Zy
  have hV : CFSG.ABGLocalTools.IsSylowOf 2 V Zy :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hU hZyle hCyNZ
  have hsV : s ∈ V := ⟨hAU ⟨hsTZ.1, hsCy⟩, hsZy⟩
  have hyV : y ∈ V := ⟨hAU ⟨hyT, hyCy⟩, hyZ⟩
  have hsCx : s ∈ Cx := kz_le_centralizer (Q := fullQ) (z := x) hsW.2.1
  have hxCs : x ∈ centralizer ({s} : Set G) :=
    CFSG.GH74.GLS.TwoThin.mem_centralizer_symm hsCx
  have hmaxsx : (RigidSet fullQ s).ncard ≤ (RigidSet fullQ x).ncard := hmax s hs2
  have hmaxsy : (RigidSet fullQ s).ncard ≤ (RigidSet fullQ y).ncard := by
    rw [hny]
    exact hmax s hs2
  obtain ⟨Jx, hJx⟩ :=
    exists_pump_family_of_mem_zStar_kz (fullQ := fullQ) (x := x) (t := s)
      hnonab hs2 hsW.2
  have hcovx := rigid_product_coverage (fullQ := fullQ) (x := x) (t := s)
    Jx hxCs hJx hmaxsx
  have hWs : CFSG.ABGLocalTools.IsSylowOf 2 W (zStar (Kz fullQ s)) :=
    isSylowOf_zStar_kz_of_coverage (fullQ := fullQ) (x := x) (t := s) (W := W)
      hW hsW hcovx.1 hcovx.2
  have hsCyx : s ∈ Cy := kz_le_centralizer (Q := fullQ) (z := y) hsZy.1
  have hyCs : y ∈ centralizer ({s} : Set G) :=
    CFSG.GH74.GLS.TwoThin.mem_centralizer_symm hsCyx
  obtain ⟨Jy, hJy⟩ :=
    exists_pump_family_of_mem_zStar_kz (fullQ := fullQ) (x := y) (t := s)
      hnonab hs2 hsZy
  have hcovy := rigid_product_coverage (fullQ := fullQ) (x := y) (t := s)
    Jy hyCs hJy hmaxsy
  have hVs : CFSG.ABGLocalTools.IsSylowOf 2 V (zStar (Kz fullQ s)) :=
    isSylowOf_zStar_kz_of_coverage (fullQ := fullQ) (x := y) (t := s) (W := V)
      hV hsV hcovy.1 hcovy.2
  have hyZs : y ∈ zStar (Kz fullQ s) := hVs.le hyV
  let B : Subgroup G := T ⊓ zStar (Kz fullQ s)
  have hB2 : IsPGroup 2 ↥B := hT.isPGroup.to_inf_left
  have hWB : W ≤ B := le_inf (fun w hw => hw.1) hWs.le
  have hBZs : B ≤ zStar (Kz fullQ s) := inf_le_right
  have hBeq : B = W := CFSG.ABGLocalTools.IsSylowOf.eq_of_le hWs hWB hBZs hB2
  have hyB : y ∈ B := ⟨hyT, hyZs⟩
  rw [hBeq] at hyB
  exact hyB

end CFSG.GH74.GLS.NT44

end
