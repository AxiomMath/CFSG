module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Base
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617PThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5LargeSteps

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

variable {G : Type} [Group G] [Finite G]

theorem slotP614StepL617Large_holds :
    SlotP614StepL617Large := by
  intro G _ _ hS hD1 p hp5 P M hsit x z hx hz H S hopt
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  have hpl : SmallRankPlane p (P : Subgroup G) x z := SmallRankPlane.of_situation hS hsit hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hHtop : H ≠ ⊤ := n4_isTwoLocal_ne_top hS hopt.ext.pair.isTwoLocal
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hSHM : S ≤ H ⊓ M := hopt.ext.pair.isMax.1.1
  have hSH : S ≤ H := hSHM.trans inf_le_left
  have hSM : S ≤ M := hSHM.trans inf_le_right
  obtain ⟨⟨-, hS2, hBS⟩, hSmax⟩ := hopt.maxInv
  have hOH : rankThreePrimeCore p H ≤ H := CFSG.AGLEmbedding.glbPrimeCore_le p H
  have hHO : H ≤ normalizer (rankThreePrimeCore p H : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p H
  have hOcop : Nat.Coprime p (Nat.card (rankThreePrimeCore p H)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p H
  suffices hNM : (rankThreePrimeCore p H ⊔ S) ≤ M from le_sup_left.trans hNM
  by_contra hNM
  set N : Subgroup G := rankThreePrimeCore p H ⊔ S with hN
  have hNH : N ≤ H := sup_le hOH hSH
  have hNtop : N ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ hNH))
  have hNp : ¬ p ∣ Nat.card N :=
    not_dvd_card_sup hprime hp2 hOH hSH hHO hOcop hS2
  have hKN : CFSG.Open.IsKGroup ↥N :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper N hNtop)
  have hBN : zpowers x ⊔ zpowers z ≤ normalizer (N : Set G) := fun b hb =>
    mem_normalizer_sup (hHO (hBH hb)) (hBS hb)
  have hSsylow : CFSG.QuasithinUnique.IsSylowTwoOf S N := by
    obtain ⟨S₁, hS₁, hSS₁, hBS₁⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      hprime Nat.prime_two hB3 hNp hBN le_sup_right hS2 hBS
    have hS₁S : S₁ = S := hSmax S₁ ⟨hS₁.1.trans hNH, hS₁.2.1, hBS₁⟩ hSS₁
    rw [hS₁S] at hS₁
    obtain ⟨P2, hP2⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS₁
    have hsub : S.subgroupOf N = (P2 : Subgroup N) := by
      rw [← hP2]
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    exact ⟨hS₁.1, hS2, by have h := P2.not_dvd_index; rwa [← hsub] at h⟩
  have hchar : CFSG.QuasithinUnique.CharTwo N := by
    have hH := hS.charTwo H hopt.ext.pair.isTwoLocal
    have hQ := pCoreOf_le_pCoreOf hNH (hopt.core_le.trans le_sup_right)
    intro g hg
    obtain ⟨hgN, hgC⟩ := Subgroup.mem_inf.mp hg
    exact hQ (hH (Subgroup.mem_inf.mpr ⟨hNH hgN, Subgroup.centralizer_le hQ hgC⟩))
  have hcgs : CFSG.Quasithin.cgsIn N S ≤ M := by
    refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC0 => iSup_le fun hCc => ?_
    exact inf_le_right.trans (hopt.char_le C hCS hC0 hCc)
  have hcore_le : pCoreOf 2 H ≤ pCoreOf 2 N :=
    pCoreOf_le_pCoreOf hNH (hopt.core_le.trans le_sup_right)
  have hSN : S ≤ N := le_sup_right
  have hN2S : pCoreOf 2 N ≤ S := pCoreOf_le_of_isSylowTwoOf hSsylow
  have hBN2 : S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (pCoreOf 2 N : Set G) :=
    sup_le (hSN.trans (localGroup_le_normalizer_pCoreOf 2 N))
      (fun b hb => normalizer_le_normalizer_pCoreOf' N (hBN hb))
  by_cases hlt : pCoreOf 2 H < pCoreOf 2 N
  · exact hNM ((localGroup_le_normalizer_pCoreOf 2 N).trans
      (hopt.norm_le (pCoreOf 2 N) hlt hN2S hBN2))
  obtain ⟨Y, hY, hYM⟩ := CFSG.CGT.PushingUpLit.AschbacherLocalFactorization.relative
    CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
    (CFSG.AGLEmbedding.LocalCGT.kProper_of_isKGroup hKN)
    (CFSG.AGLEmbedding.LocalCGT.isCharacteristicP_of_charTwo hchar)
    (CFSG.AGLEmbedding.LocalCGT.isSylowOf_of_isSylowTwoOf hSsylow)
    ((CFSG.AGLEmbedding.LocalCGT.centralizer_inf_le_cgsIn hS2 hopt.ext.pair.ne_bot).trans hcgs)
    (fun B hB0 hBS' hBc =>
      (CFSG.AGLEmbedding.LocalCGT.normalizer_inf_le_cgsIn B hB0 hBS' hBc).trans hcgs) hNM
  have hzN : z ∈ normalizer (N : Set G) := hBN (mem_sup_right (mem_zpowers z))
  have hzS : z ∈ normalizer (S : Set G) := hBS (mem_sup_right (mem_zpowers z))
  by_cases hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) ∨ z ∈ normalizer (Y : Set G)
  · exact hYM ((kFactBlocksInSylowCentralizerQS_holds G p N S z hprime hp5 hKN hchar hSsylow hNp
      hzN hzS hz.pow_eq_one Y hY hq).trans
      (sup_le hSM (inf_le_right.trans (n4_centralizer_le_of_central hS hsit hz))))
  ·
    push Not at hq
    exfalso
    have hzB : z ∈ zpowers x ⊔ zpowers z := mem_sup_right (mem_zpowers z)
    have hBab : ∀ a ∈ zpowers x ⊔ zpowers z, ∀ b ∈ zpowers x ⊔ zpowers z, a * b = b * a :=
      fun a ha b hb =>
        congrArg Subtype.val (hpl.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    obtain ⟨F, E, hFne, hF3, hFE, hEN, hE3, hEp, hFz, hBF, hFY⟩ :=
      L617P.exists_three_subgroup' hprime hB3 hBab hzB hz.pow_eq_one hBN hNp
        (CFSG.AGLEmbedding.LocalCGT.isCharacteristicP_of_charTwo hchar) hY hq.1 hq.2
    have h1 : Open.pRank 3 E ≤ Open.pRank 3 H :=
      CFSG.SectionRank.pRank_mono (by norm_num) (hEN.trans hNH)
    have h2 : Open.pRank 3 H ≤ evenRank G :=
      local_pRank_le_evenRank 3 Nat.prime_three (by norm_num) H hopt.ext.pair.isTwoLocal
    have h3 := hS.rank
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
