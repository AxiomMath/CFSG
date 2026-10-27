module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def NoAlt6CompOf (X : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (b : G), CFSG.Open.IsQuasisimple ↥L →
    catalogIs (↥L ⧸ Subgroup.center ↥L) X →
    InnerDiagMarking (Subgroup.zpowers b) L → b ^ 3 = 1 →
    IsComponentOf K (L ⊓ Subgroup.centralizer ({b} : Set G)) →
    ¬ Nonempty (K ≃* alternatingGroup (Fin 6))

theorem noAlt6CompOf_split (h5 : NoAlt6CompOf S9.isU5two) (h6 : NoAlt6CompOf S9.isU6two)
    (hD : NoAlt6CompOf S9.isD4two) :
    NoAlt6CompOf (fun i => S9.isU5two i ∨ S9.isU6two i ∨ S9.isD4two i) := by
  intro G _ _ L K b hq hcat hidm hb3 hcomp hA
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with h | h | h
  · exact h5 G L K b hq ⟨i, h, ⟨e⟩⟩ hidm hb3 hcomp hA
  · exact h6 G L K b hq ⟨i, h, ⟨e⟩⟩ hidm hb3 hcomp hA
  · exact hD G L K b hq ⟨i, h, ⟨e⟩⟩ hidm hb3 hcomp hA

theorem catalog_pSimple_u42 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hU : CFSG.Assembly.LargeEvenIsU42 ↥K) :
    catalogIs ↥K S9.isU4two ∧ catalogIs (PSimple 3 K) S9.isU4two := by
  have hK25920 : Nat.card ↥K = 25920 := CFSG.StandardType.IOneOrthEnd.card_of_isU42 hU
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hU
  have hcatK : catalogIs ↥K S9.isU4two := CFSG.LocalAnalysis.GLTheoremA.CatB.catalogIs_u4two_of_statedProj hcard e
  have hsimpS : IsSimpleGroup (StatedProj (StatedSU 4 (2 ^ 1) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 1 (by rw [hcard]; norm_num) 4
      (by norm_num) (by decide)
  have hsimpK : IsSimpleGroup ↥K := e.isSimpleGroup_congr.mpr hsimpS
  have hZ : Subgroup.center ↥K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · exact h
    · exfalso
      have hbot : commutator ↥K = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro g _
        have hg : g ∈ Subgroup.center ↥K := by rw [h]; exact Subgroup.mem_top g
        rw [Subgroup.mem_centralizer_iff]
        intro x _
        exact (Subgroup.mem_center_iff.1 hg x)
      have htb : (⊤ : Subgroup ↥K) = ⊥ := hq.1.symm.trans hbot
      have h1 : Nat.card ↥K = 1 := by
        have := congrArg (fun H : Subgroup ↥K => Nat.card H) htb
        simpa [Subgroup.card_top, Subgroup.card_bot] using this
      rw [hK25920] at h1
      norm_num at h1
  have hO : GLAPPrimeCore 3 ↥K = ⊥ := by
    unfold GLAPPrimeCore CFSG.pPrimeCore
    refine le_bot_iff.1 (sSup_le fun N hN => ?_)
    obtain ⟨hNn, hNc⟩ := hN
    haveI := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · rw [h]
    · exfalso
      rw [h, Subgroup.card_top, hK25920] at hNc
      norm_num at hNc
  have hcen : Subgroup.center (PQuot 3 K) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) c
    have hk : k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := Subgroup.mem_center_iff.1 hc (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) g)
      rw [← map_mul, ← map_mul] at h1
      have h2 := QuotientGroup.eq.1 h1
      rw [hO, Subgroup.mem_bot] at h2
      exact inv_mul_eq_one.1 h2
    rw [hZ, Subgroup.mem_bot] at hk
    rw [Subgroup.mem_bot, hk, map_one]
  have hbij : Function.Bijective (CFSG.LocalAnalysis.GLTheoremA.CatB.toSimple 3 K) := by
    refine ⟨?_, CFSG.LocalAnalysis.GLTheoremA.CatB.toSimple_surjective 3 K⟩
    rw [injective_iff_map_eq_one]
    intro k hk
    simp only [CFSG.LocalAnalysis.GLTheoremA.CatB.toSimple, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply] at hk
    rw [QuotientGroup.eq_one_iff, hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hO,
      Subgroup.mem_bot] at hk
    exact hk
  exact ⟨hcatK, (catalogIs_congr (MulEquiv.ofBijective _ hbij)).1 hcatK⟩

theorem i171SmallIsU42Fact_of_noAlt6 (hN : NoAlt6CompOf (fun i => S9.isU5two i ∨ S9.isU6two i ∨ S9.isD4two i)) :
    I171SmallIsU42Fact := by
  intro G _ _ L K b hq hcat hidm hb3 hcomp hsmall
  rcases hsmall with hU | hA6
  · exact catalog_pSimple_u42 hcomp.2.2 hU
  · exact absurd hA6 (hN G L K b hq hcat hidm hb3 hcomp)

end CFSG.LocalAnalysis.GLTheoremA.S171

end
