module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.Basic
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.Bg.Pu5.BalBBasic
import CFSG.GH74.GLS.C3.Layer1.Th2Pump
import CFSG.GH74.GLS.TwoThin.Rank
import CFSG.GH74.GLS.Bg.Rank
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
import CFSG.GH74.GLS.Bg.Iii2.Statements
import CFSG.GH74.GLS.Bg.Pu5.BalStatements
import CFSG.GH74.GLS.Bg.Pu5.Statements
import CFSG.GH74.GLS.IVK.Lifted.GroupAux
import CFSG.GH74.GLS.IVK.Lifted.IIAutB
import CFSG.GH74.GLS.IVK.Lifted.Strong
import CFSG.GH74.Uniqueness.SU.KInputs2
import CFSG.GH74.Uniqueness.SU.SU13TA1Class
import CFSG.GH74.Uniqueness.SU.SU8Stmts
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4
open scoped commutatorElement

theorem exists_pump_family_of_mem_zStar_kz {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ] {x t : G}
    (hnonab : ∃ a b : G, a * b ≠ b * a) (ht2 : orderOf t = 2)
    (htZ : t ∈ zStar (Kz fullQ x)) :
    ∃ J : Subgroup G → Subgroup G, ∀ K ∈ RigidSet fullQ x, PumpUpLT 2 x K t (J K) := by
  classical
  have hPle : Kz fullQ x ≤ pLayerOf 2 (centralizer ({x} : Set G)) := by
    unfold Kz
    exact sSup_le_sSup fun K hK => hK.1.1.2.2
  have hpoint : ∀ K ∈ RigidSet fullQ x, ∃ M : Subgroup G, PumpUpLT 2 x K t M := by
    intro K hK
    have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hK.1.1.2.2
    have hKil : IsILo 2 x K := hK.1.1
    have hKP : K ≤ Kz fullQ x := le_sSup hK
    have htL : t ∈ pLayerOf 2 (centralizer ({x} : Set G)) := hPle htZ.1
    have htN : t ∈ normalizer (K : Set G) :=
      CFSG.GH74.GLS.Stage1.Thm2.Recip.pLayerOf_le_normalizer hKc htL
    have htO : t ∈ normalizer (pPrimeCoreOf 2 K : Set G) :=
      CFSG.GH74.GLS.TwoThin.mem_normalizer_pPrimeCoreOf htN
    have htcs : t ∈ centralizerSection K (pPrimeCoreOf 2 K) := by
      refine ⟨htN, htO, fun k hk => ?_⟩
      have hkP : k ∈ Kz fullQ x := hKP hk
      have h1 : ⁅k, t⁆ ∈ pPrimeCoreOf 2 (Kz fullQ x) := htZ.2.2.2 k hkP
      have h2 : ⁅k, t⁆ ∈ K := by
        have e : ⁅k, t⁆ = k * (t * k⁻¹ * t⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp htN k⁻¹).mp (K.inv_mem hk))
      exact CFSG.GH74.GLS.Bg.Pu5.inf_pPrimeCoreOf_le hKP ⟨h2, h1⟩
    have htCx : t ∈ centralizer ({x} : Set G) :=
      CFSG.GH74.GLS.NT44.kz_le_centralizer (Q := fullQ) htZ.1
    have h3x : 3 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := by
      have h2 : oBound 2 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := hKil.2.1
      have h3' : oBound 2 = 3 := by simp [oBound]
      exact h3' ▸ h2
    have h3 : 3 ≤ pRank 2 G :=
      h3x.trans (CFSG.GH74.GLS.Bg.pRank_subgroup_le (by norm_num)
        (centralizer ({x} : Set G)))
    have hRt : 3 ≤ pRank 2 ↥(centralizer ({t} : Set G)) :=
      CFSG.GH74.GLS.TwoThin.rankThreeCentralizers G (inferInstance : IsSimpleGroup G)
        hnonab h3 t ht2
    exact CFSG.GH74.GLS.TwoThin.exists_pumpup_of_involution hKil.1 ht2 hKc htCx htcs hKil hRt
  choose! J hJ using hpoint
  exact ⟨J, hJ⟩

end CFSG.GH74.GLS.NT44

end
