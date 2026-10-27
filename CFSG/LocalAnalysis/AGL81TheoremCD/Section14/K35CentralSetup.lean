module

public import CFSG.Foundations.Basic
public import CFSG.Open.RankThreeDefs
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.IndexGen
public import CFSG.LieType.Seitz.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Inner
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3

theorem alphaList_hyps_of_isComponent
    (hNC : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentreRank)
    {X : Type} [Group X] [Finite X] (hKX : CFSG.Open.IsKGroup X)
    (hO : CFSG.pPrimeCore 3 X = ⊥) {K : Subgroup X} (hK : CFSG.IsComponent K)
    (hK2 : CFSG.Open.pRank 3 K ≤ 2) :
    CFSG.Open.IsQuasisimple ↥K ∧ CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) ∧
      IsPGroup 3 (Subgroup.center ↥K) ∧ IsCyclic (Subgroup.center ↥K) ∧
      Odd (Nat.card (Subgroup.center ↥K)) ∧ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 2 := by
  have hQ : CFSG.Open.IsQuasisimple ↥K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.2.1.mp hK.1
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
  have hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hKX K hK.1.2.2
      (QuotientGroup.mk' (Subgroup.center ↥K))
      (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZP : IsPGroup 3 (Subgroup.center ↥K) :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree.isPGroup_center_of_isComponent
      (p := 3) hK hO
  obtain ⟨k, hk⟩ := hZP.exists_card_eq
  have hodd : Odd (Nat.card (Subgroup.center ↥K)) := by
    rw [hk]
    exact Odd.pow (n := k) (by decide : Odd 3)
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ 2 := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) K]
  have hcyc : IsCyclic (Subgroup.center ↥K) := by
    by_contra hnc
    have h4 := hNC ↥K hQ hcat hZP hnc
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) K] at h4
    omega
  exact ⟨hQ, hcat, hZP, hcyc, hodd, hrank⟩

theorem centGenI_le_rankThreeGamma {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (L : Subgroup X) :
    GL83.CompFam.centGenI 3 E L ≤ CFSG.Open.rankThreeGamma 1 3 E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  change GL83.CompFam.centGenI 3 E L ≤ CFSG.Open.GLBCore 3 1 E
  refine iSup_le fun A => ?_
  obtain ⟨hAE, hAc⟩ := A.2
  have hAel : CFSG.Open.IsElemAbelian 3 A.1 := GL83.CompFam.elem_mono hE hAE
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hAel
  have hj1 : 1 ≤ j := by
    have h9 : 9 ≤ 3 * Nat.card A.1 := by
      rw [← hE9]
      exact hAc
    have h3 : 3 ≤ Nat.card A.1 := by omega
    rw [hj] at h3
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 (by simpa using h3)
  have hrk : 1 ≤ CFSG.Open.pRank 3 A.1 :=
    hj1.trans (CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hAel hj)
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (A.1 : Set X)).trans
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hAE hrk))

theorem le_rankThreeGamma_of_forall_seitzHyperGamma {X : Type} [Group X] [Finite X]
    {K E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEN : E ≤ Subgroup.normalizer (K : Set X))
    (h : ∀ A : Subgroup (MulAut ↥K), CFSG.Open.IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
      CFSG.LieType.Seitz.seitzHyperGamma 3 A = ⊤) :
    K ≤ CFSG.Open.rankThreeGamma 1 3 E := by
  by_cases hBC : E ⊓ Subgroup.centralizer (K : Set X) = ⊥
  · have hAel : CFSG.Open.IsElemAbelian 3 (autIm E K) := isElemAbelian_autIm hE K
    have hAcard : Nat.card (autIm E K) = 9 := by
      rw [card_autIm hEN hBC]
      exact hE9
    have hgen : K ≤ GL83.CompFam.centGenI 3 E K :=
      le_centGenI_of_autIm hEN hBC (h (autIm E K) hAel (by rw [hAcard]; norm_num))
    exact hgen.trans (centGenI_le_rankThreeGamma hE hE9 K)
  · obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBC
    have he1' : e ≠ 1 := fun h1 => he1 (Subtype.ext h1)
    have hKcent : K ≤ Subgroup.centralizer ({e} : Set X) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp he.2 k hk
    exact hKcent.trans
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35.centralizer_le_gamma hE he.1 he1')

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central
