module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29A
public import CFSG.GH74.GLS.C3.Layer1.Th2Pump
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.GLS.Bg.Iii2.L41Main
public import CFSG.GH74.GLS.C3.Layer1.Th2L84Syl
public import CFSG.GH74.GLS.C3.Layer1.Th2HYStruct
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma55
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Th2L83Gen
public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.GH74.GLS.C3.Layer1.Th2P812
public import CFSG.GH74.GLS.C3.Layer1.Th2P812Rows
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace S3Sec29A1

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_pumpUp_of_le {u : G} {J Λ M : Subgroup G}
    (hlay : pLayerOf 2 (J ⊓ centralizer ({u} : Set G)) = Λ)
    (hM : IsPCompIn 2 (centralizer ({u} : Set G)) M)
    (hMJ : M.subgroupOf (centralizer ({u} : Set G)) ≤
      pumpupY (Λ.subgroupOf (centralizer ({u} : Set G)))) :
    IsPCompIn 2 (pumpUp 2 J u) M := by
  have hJ : pumpUp 2 J u = (pumpupY (Λ.subgroupOf (centralizer ({u} : Set G)))).map
      (centralizer ({u} : Set G)).subtype := by
    rw [pumpUp_eq_map_pumpupY, hlay]
  have hMJ' : M ≤ pumpUp 2 J u := by
    rw [hJ]
    intro m hm
    exact ⟨⟨m, hM.1 hm⟩, hMJ (Subgroup.mem_subgroupOf.mpr hm), rfl⟩
  exact ⟨hMJ', (CatalogueBAlternating.pComponent_two_iff _).mpr
    (TwoComponentTransport.restrict_nested M (pumpUp 2 J u) (centralizer ({u} : Set G)) hMJ'
      (pumpUp_le_centralizer J u) (isPCompIn_two_iff.mp hM).2)⟩

theorem pumpup_dichotomy {z u : G} {J Λ M : Subgroup G} (hz : orderOf z = 2)
    (hzu : z ∈ centralizer ({u} : Set G)) (hΛ : IsLam z u J Λ)
    (hM : IsPCompIn 2 (centralizer ({u} : Set G)) M) :
    IsPCompIn 2 (pumpUp 2 J u) M ∨ ⁅PumpCalc.bar u Λ, PumpCalc.bar u M⁆ = ⊥ := by
  set Y' := centralizer ({u} : Set G) with hY'
  have hso : orderOf (⟨z, hzu⟩ : ↥Y') = 2 := orderOf_mk_centralizer hzu hz
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛ.pcW).1 hzu
  have hΛ2 := isTwoComponent_centralizer_mk hΛ.pcW hzu
  obtain ⟨hΛE, hJsub, L, hL, hcases, hLJ, hLsJ, hiff⟩ := pumpupY_structure hso hΛC hΛ2
  have hM2 := (isPCompIn_two_iff.mp hM).2
  have hMc : CFSG.IsComponent (PumpCalc.bar u M) := isComponent_bar hM
  by_cases hMeq : PumpCalc.bar u M = L ∨ PumpCalc.bar u M = conjSub (barMk ↥Y' ⟨z, hzu⟩)⁻¹ L
  · left
    exact isPCompIn_pumpUp_of_le hΛ.layer hM ((hiff _ hM2).mpr hMeq)
  · right
    push Not at hMeq
    obtain ⟨hne1, hne2⟩ := hMeq
    have hLs : CFSG.IsComponent (conjSub (barMk ↥Y' ⟨z, hzu⟩)⁻¹ L) := isComponent_conjSub hL _
    have hc1 : ⁅L, PumpCalc.bar u M⁆ = ⊥ :=
      (distinct_components_commute hL hMc).resolve_left (fun h => hne1 h.symm)
    have hc2 : ⁅conjSub (barMk ↥Y' ⟨z, hzu⟩)⁻¹ L, PumpCalc.bar u M⁆ = ⊥ :=
      (distinct_components_commute hLs hMc).resolve_left (fun h => hne2 h.symm)
    have hcc : L ⊔ conjSub (barMk ↥Y' ⟨z, hzu⟩)⁻¹ L ≤
        Subgroup.centralizer ((PumpCalc.bar u M : Subgroup _) : Set _) :=
      sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc1)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc2)
    have hΛL : PumpCalc.bar u Λ ≤ L ⊔ conjSub (barMk ↥Y' ⟨z, hzu⟩)⁻¹ L := by
      rcases hcases with ⟨-, hAL⟩ | ⟨-, hAB, hAD⟩
      · exact hAL.trans le_sup_left
      · refine hAD.trans ?_
        rintro _ ⟨x, rfl⟩
        exact swapDiag_mem_sup hAB x
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hΛL.trans hcc)

theorem exists_Ku (hr4 : pRank 2 G = 4) {x u : G} {K : Subgroup G} (hterm : IsTwoTerminal x K)
    (hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hu2 : orderOf u = 2)
    (hux : u ∈ centralizer ({x} : Set G)) (hucs : u ∈ centralizerSection K (pPrimeCoreOf 2 K))
    (hR : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G))) (hKcen : CenterlessBar K) :
    ∃ M : Subgroup G, PumpUpLT 2 x K u M ∧ x ∈ normalizer (M : Set G) ∧
      Nonempty (kBar M ≃* kBar K) ∧ CenterlessBar M ∧
      (∀ c ∈ centralizer ({u} : Set G), c ∈ normalizer (M : Set G)) ∧
      ∃ Λ : Subgroup G, IsLam x u K Λ ∧ Λ ≤ M := by
  obtain ⟨M, hlt⟩ := exists_pumpup_of_involution hterm.1.1 hu2 hKc hux hucs hterm.1 hR
  obtain ⟨hxM, ⟨e⟩⟩ := hterm.2.1 u M hlt
  have hcenM : CenterlessBar M := Th2.centerlessBar_of_equiv hKcen e
  have hMc : IsPCompIn 2 (centralizer ({u} : Set G)) M := hlt.2.1.2.2
  have hq : CFSG.IsQuasisimple (kBar M) := isQuasisimple_hat hMc
  have hcen : center (kBar M) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => hcenM z (fun b => ?_)
    exact ((Subgroup.mem_center_iff.1 hz) b).symm
  have hKuN : ∀ c ∈ centralizer ({u} : Set G), c ∈ normalizer (M : Set G) := fun c hc =>
    PumpGen.mem_normalizer_of_centerless hr4 ⟨hu2, hMc⟩ hq hcen hc
  obtain ⟨Λ, hΛ, -, hΛM⟩ :=
    Bg.Iii2.L41.trivial_pumpup_data hlt hxM (Nat.card_congr e.toEquiv).le
  exact ⟨M, hlt, hxM, ⟨e⟩, hcenM, hKuN, Λ, hΛ, hΛM⟩

theorem mem_cSec_Ku {x u r : G} {K Ku : Subgroup G}
    (hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K) (hlt : PumpUpLT 2 x K u Ku)
    (e : kBar Ku ≃* kBar K) (hxKu : x ∈ normalizer (Ku : Set G))
    (hrY : r ∈ centralizer ({u} : Set G)) (hrx : r ∈ centralizer ({x} : Set G))
    (hr : r ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    r ∈ centralizerSection Ku (pPrimeCoreOf 2 Ku) := by
  have hcm : r ∈ CMbar (centralizer ({x} : Set G)) K :=
    Th2.HY.mem_CMbar_of_comm hKc.1 hrx (fun k hk =>
      Th2.Bal.pPrimeCoreOf_le_of_pCompIn hKc (hr.2.2 k hk))
  have := Th2.L84Syl.mem_CxK_of_cmbar hKc.1 hlt e hxKu hrY hcm
  exact (Subgroup.mem_inf.1 this).2

theorem center_kBar_eq_bot {b : G} {J : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({b} : Set G)) J)
    (hty : IsA7Bar J ∨ IsL2OddNonSquare J) : center (kBar J) = ⊥ := by
  have hq : CFSG.IsQuasisimple (kBar J) := isQuasisimple_hat hJ
  have hs : IsSimpleGroup (kBar J) := by
    rcases hty with ⟨⟨e⟩⟩ | ⟨r, m, -, -, -, hlie⟩
    · have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
    · exact ComponentClassification.GSThmB.isSimpleGroup_of_lieModel_psl_two hlie
  exact center_eq_bot_of_isSimple hs hq

end S3Sec29A1

end CFSG.GH74.Generic.BProg.B3
