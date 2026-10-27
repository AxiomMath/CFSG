module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171U42Bridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6C3
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6C4
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6C56
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6C7
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6U42
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Bound
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6CaseA
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6PR
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Pat
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6CaseAU
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6CaseB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6


theorem t171InnerU6Fact_holds : T171.T171InnerU6Fact := by
  intro Ω _ _ B x L _ hcfg hLn hmax hex hsmall hT hcat
  haveI : L.Normal := hLn
  obtain ⟨e⟩ := HSubT.nonempty_S6_of_isU6two hcat
  have hS : Setup B x L := ⟨hcfg, hmax, hsmall⟩
  haveI : Group.IsPerfect ↥L := isPerfect_of_cfg hcfg
  obtain ⟨D, K, hpre⟩ := hex
  obtain ⟨d, hdD, hdx⟩ := S171.exists_y hcfg.prime hcfg.ne_one hpre
  have hLx : L ≤ Subgroup.centralizer ({x} : Set Ω) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp ((hcfg.cent x hcfg.mem).mpr
      (Subgroup.mem_zpowers x)) l hl)
  have hKcomp : IsComponentOf K (L ⊓ Subgroup.centralizer ({d} : Set Ω)) := by
    rw [← S171.L_cs_eq hcfg.prime hcfg.ne_one hpre hdD hdx hLx]
    exact hpre.2.2.2.2.2.1
  have hd3 : d ^ 3 = 1 := hcfg.elem.2 d (hpre.1 hdD)
  have hU42 : CFSG.Assembly.LargeEvenIsU42 ↥K := by
    rcases hsmall D K hpre with h | h
    · exact h
    · exact absurd h (S171.noAlt6CompOf_u6 Ω L K d hcfg.qs hcat
        (S171.innerDiagMarking_mono hcfg.idiag
          ((Subgroup.zpowers_le (G := Ω)).mpr (hpre.1 hdD))) hd3 hKcomp)
  have hKq : CFSG.Open.IsQuasisimple ↥K := hpre.2.2.2.2.2.1.2.2
  have hcatK : catalogIs ↥K S9.isU4two := (S171.catalog_pSimple_u42 hKq hU42).1
  have hKcard : Nat.card ↥K = 25920 := CFSG.StandardType.IOneOrthEnd.card_of_isU42 hU42
  have hKsimple : IsSimpleGroup ↥K := by
    obtain ⟨F, hF, hfin, hcard, ⟨eK⟩⟩ := hU42
    exact eK.isSimpleGroup_congr.mpr
      (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 1
        (by rw [hcard]; norm_num) 4 (by norm_num) (by decide))
  by_contra hcon
  push Not at hcon
  obtain ⟨b₀, hb₀, hb₀n⟩ := hcon
  have hni : ∀ s : S6, theta L e b₀ ≠ MulAut.conj s := fun s hs =>
    hb₀n (inducesInnerMod_of_theta_eq_conj e hs)
  have hPR := stepPR_holds prFix_holds Ω B x L e hS
  have hPat := stepPat_holds pat4OfSmall_holds Ω B x L e hS hPR D K hpre hcatK hKsimple hKcard
  obtain ⟨hB243, hcase⟩ :=
    stepBound_holds u42Rank_holds Ω B x L hS D K hpre hcatK hKsimple hKcard
  obtain ⟨hB, U, hU2, hUne, hUn⟩ : Nat.card B = 243 ∧ ∃ U : Subgroup PGU6, IsPGroup 2 U ∧
      U ≠ ⊥ ∧ Bt B L e ≤ Subgroup.normalizer (U : Set PGU6) := by
    rcases hcase with ⟨E, hE1, hE2, hE3, hE4, hE5⟩ | hdec
    · obtain ⟨T, hT1, hT2, hT3, hT4, hT5⟩ := hT
      obtain ⟨hc, hnc⟩ := stepCaseACard_holds u42E9_holds u42E27_holds Ω B x L hS D K hpre hcatK
        hKsimple hKcard hB243 E hE1 hE2 hE3 hE4 hE5 T hT1 hT2 hT3 hT4 hT5
      exact ⟨hc, stepCaseAU_holds Ω B x L e hS T hT3 hT4 hnc⟩
    · exact stepCaseB_holds pat4Inv_holds u42E27_holds Ω B x L e hS D K hpre hcatK hKsimple
        hKcard hPat hB243 hdec b₀ hb₀ hni
  obtain ⟨g, hgBt, hg⟩ := exists_mem_Bt e (fun b hb => hcfg.elem.2 b hb) (hpre.1 hdD)
  have hg4 : Pat4 g := hPat d hdD hdx g hg
  have hBt := isElemAbelian_Bt (L := L) e hcfg.elem
  obtain ⟨hab, hexp⟩ := pat4Abelian_holds g (Bt B L e) hg4
    (fun a ha => hBt.comm ha hgBt) (fun a ha b hb => hBt.comm ha hb) (fun a ha => hBt.2 a ha)
  have hcard : 81 ≤ Nat.card (Bt B L e) := by
    have := card_Bt e hcfg
    omega
  obtain ⟨a, haBt, hapr⟩ := prFromTwoGroup_holds (Bt B L e) U hab hexp hcard hU2 hUne hUn
  obtain ⟨b, hb, hba⟩ := (mem_Bt e).1 haBt
  exact hPR b hb a hba.symm hapr

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
