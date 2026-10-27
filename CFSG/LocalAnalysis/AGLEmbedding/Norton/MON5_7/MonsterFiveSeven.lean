module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.TwoAEdge
public import CFSG.YGroups.Y443.Tri.AssemblyLit
public import CFSG.Monster.GMS.ASegConnH87
public import CFSG.Monster.GMS.ASegTitsTri
public import CFSG.Monster.Existence.TwoPoint.EvenShapes
public import CFSG.Monster.Existence.AssemblyHS
public import CFSG.Monster.Existence.BabyAmbient
public import CFSG.Sporadic.Bridge.BFusFive
public import CFSG.Sporadic.Bridge.BFusSevenMain
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.Monster.Tri.TriangleStabMaximal
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
public import CFSG.Sporadic.Co1.Module.Co2Stab
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

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7

open CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint CFSG.Monster.Existence CFSG.Monster.GMS
  CFSG.Monster.Generated CFSG.Monster.Griess


theorem fusionGenerationOf_MGriess_of_baby
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpE : p ∣ CFSG.Open.ordTwistedE6 2) (hB : FusionGenerationOf NativeSporadic.B p) :
    FusionGenerationOf MGriess p := by
  have hfin : Finite MGriess := inferInstance
  have hcl := CFSG.YGroups.Y443.monster_clauses_MGriess
  have I := CFSG.YGroups.Y443.gmsInterfaces_MGriess
  have hG := gmsF1Type_MGriess_uncond
  have hconn := twoAGraph_preconnected I hG
  have hu := uGriess_mem_twoANbr
  let v : ConjVert tGriess := ⟨tGriess, IsConj.refl _⟩
  let w : ConjVert tGriess := ⟨uGriess, hu.1⟩
  have hadj : (twoAGraph tGriess).Adj v w :=
    ⟨fun h => uGriess_ne_tGriess (congrArg Subtype.val h).symm, hu.2⟩
  have hKW : Subgroup.centralizer ({tGriess} : Set MGriess) ⊔ edgeStab v w = ⊤ :=
    CFSG.Monster.B.Recog.sup_eq_top_of_preconnected (fun g _ _ h => twoAGraph_adj_smul g h) hconn
      (fun y hy => harc_twoAGraph I hG v w v y hadj hy)
      (harc_twoAGraph I hG v w w v hadj hadj.symm) (fun g => (smul_eq_self_iff g v).symm)
      (fun g => mem_edgeStab)
  have hW : ∀ g, g ∈ edgeStab v w ↔ (g * tGriess * g⁻¹ = tGriess ∧ g * uGriess * g⁻¹ = uGriess) ∨
      (g * tGriess * g⁻¹ = uGriess ∧ g * uGriess * g⁻¹ = tGriess) := by
    intro g
    rw [mem_edgeStab]
    exact or_congr (and_congr (smul_mk_eq_mk_iff _ _ g) (smul_mk_eq_mk_iff _ _ g))
      (and_congr (smul_mk_eq_mk_iff _ _ g) (smul_mk_eq_mk_iff _ _ g))
  have hD : p ∣ Nat.card ↥(cent tGriess ⊓ cent uGriess) := by
    obtain ⟨N, hN, -, -, hlie⟩ := twoPointShape_one_MGriess
    have hc := CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_twistedE6 hlie
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hc]
    exact Dvd.dvd.mul_right hpE _
  exact fusionGenerationOf_of_twoA_edge hp2 orderOf_tGriess hcl.2.2 (edgeStab v w) hW hKW hD hB

theorem fusionGenerationOf_MGriess_five
    : FusionGenerationOf MGriess 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  fusionGenerationOf_MGriess_of_baby (by norm_num)
    (by norm_num [CFSG.Open.ordTwistedE6]) CFSG.Sporadic.Bridge.B.fusionGenerationOf_B_five

theorem fusionGenerationOf_MGriess_seven
    : FusionGenerationOf MGriess 7 :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  fusionGenerationOf_MGriess_of_baby (by norm_num)
    (by norm_num [CFSG.Open.ordTwistedE6]) CFSG.Sporadic.Bridge.B.fusionGenerationOf_B_seven

theorem fusionGenerationOf_Monster_of_MGriess
    {T : Type*} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) {p : ℕ} (h : FusionGenerationOf MGriess p) :
    FusionGenerationOf T p := by
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  have hG := CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  exact fusionGenerationOf_congr ((CFSG.YGroups.Y443.griessEquivGmat hG).trans ε.symm) h

theorem fusionGenerationOf_Monster_five
    {T : Type*} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) : FusionGenerationOf T 5 :=
  fusionGenerationOf_Monster_of_MGriess e fusionGenerationOf_MGriess_five

theorem fusionGenerationOf_Monster_seven
    {T : Type*} [Group T] [IsSimpleGroup T]
    (e : T ≃* NativeSporadic.Carrier .M) : FusionGenerationOf T 7 :=
  fusionGenerationOf_Monster_of_MGriess e fusionGenerationOf_MGriess_seven

end CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7
