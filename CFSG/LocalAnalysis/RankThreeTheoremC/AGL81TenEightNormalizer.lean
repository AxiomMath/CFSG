module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightEscape
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.GLTheoremA.S8.Close
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeX
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightNormalizerQ
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenClaimOf
import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightComponents

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem normalizer_conj_le_of_not_normal (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR2 : KFactNineThreeRankTwo) (hK342 : TenThirteen.KFactThreeFourTwo)
    (h98 : AGL81NineEightTwo G) (h101 : AGL81TenOneExists G) (h1031 : AGL81TenThreeOneAt G)
    (hS : Setting G) {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hNL : ¬ (L.subgroupOf M).Normal)
    {I₀ : Subgroup G} (hI₀ : I₀ ∈ cZero (H ⊓ L))
    (hExcl : ∀ m ∈ M, ∀ (q : ℕ) (iK iJ : TauCeti.CFSGIndex),
      TenThirteen.IsThreeFourPair q iK iJ →
      ∀ f : ↥(L.map (MulAut.conj m).toMonoidHom) →* iJ.Group, ¬ Function.Surjective f)
    {m : G} (hm : m ∈ M) :
    normalizer ((L.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) ≤ M := by
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hp : p.Prime := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hLc : IsTwoPrimeComponent M L := hL.toIsTwoPrimeComponent
  set J : Subgroup G := L.map (MulAut.conj m).toMonoidHom with hJdef
  have hJc : IsTwoPrimeComponent M J := hLc.map_conj hm
  have hIL : CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ L :=
    (oUpperTwo_le_self I₀).trans (hI₀.le.trans inf_le_right)
  have h3L : 3 ∣ Nat.card L :=
    (h1031 hS p P M H Q K hd L hL I₀ hI₀).trans (Subgroup.card_dvd_of_le hIL)
  have h3J : 3 ∣ Nat.card J := by
    rwa [hJdef, Subgroup.card_map_of_injective (MulAut.conj m).injective]
  have hO2 : pCoreOf 2 J ≠ ⊥ := pCoreOf_ne_bot_of_three_dvd hS.charTwo he.maxTwoLocal_M.1 hJc h3J
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 J : Set G)) :=
    ⟨pCoreOf 2 J, hO2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J, rfl⟩
  obtain ⟨N', hN', hNN'⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le hloc
  have hJN' : normalizer (J : Set G) ≤ N' :=
    (normalizer_localGroup_le_normalizer_pCoreOf 2 J).trans hNN'
  by_cases hN'M : N' ≤ M
  · exact hJN'.trans hN'M
  exfalso
  have hcomp : ∀ J₁ : Subgroup G, IsTwoPrimeComponent M J₁ → J₁ ≤ N' :=
    fun J₁ hJ₁ => (le_normalizer_of_isTwoPrimeComponent hJc hJ₁).trans hJN'
  obtain ⟨B, hB, hBJ⟩ := exists_isAGLQ_le_normalizer hS he hd.base hJc h3J
  have hBN' : B ≤ N' := hBJ.trans hJN'
  obtain ⟨Q₀, -, hQ₀N', hQ₀, S, hS₀⟩ := exists_sylowBase he hB hBN'
  have hNtop : N' ≠ ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top hS.simple hS.nonab hN'.1
  haveI hKn : (d1KBar p M N').Normal := by
    by_cases hK : d1KBar p M N' = ⊥
    · rw [hK]
      exact Subgroup.normal_bot
    · exact d1KBar_normal_of_escape he hB hBN' hK
  have hsyl := sylowK_of_sylow (K := d1KBar p M N') S hS₀
  rcases h98 hS p P M H₁ R₁ he N' Q₀ hQ₀ hQ₀N' hN' hN'M hsyl with hb3 | ⟨hp3, L₃, hL₃, hL₃X, -⟩
  · obtain ⟨L'', hL''⟩ := h101 hS p P M H₁ R₁ he N' Q₀ hQ₀ hQ₀N' hN' hN'M hsyl hb3
    exact hL''.not_le_normalizer
      ((hcomp L'' hL''.toIsTwoPrimeComponent).trans (localGroup_le_normalizer_pCoreOf 2 N'))
  · subst hp3
    have hK : d1KBar 3 M N' ≠ ⊥ := d1KBar_ne_bot ⟨L₃, hL₃, hL₃X⟩
    have hin := kFactInputs_of_escape h31 h75 hR2 hS he hB hBN' hNtop hK
    have hXM : d1PlusCore 3 N' (d1KBar 3 M N') ≤ M := d1PlusCore_le_of_escape he hB hBN' hK
    have hrank := pRank_d1PlusCore_le_one_of_escape he hB hBN' hK
    have key : ∀ m' ∈ M,
        L.map (MulAut.conj m').toMonoidHom ≤ d1PlusCore 3 N' (d1KBar 3 M N') := by
      intro m' hm'
      have hc' := hLc.map_conj hm'
      rcases le_d1PlusCore_or_pair hK342 hin hc' (hcomp _ hc') with h | ⟨iK, iJ, hpair, f, hf⟩
      · exact h
      · exact absurd hf (hExcl m' hm' 3 iK iJ hpair f)
    obtain ⟨m₁, hm₁, hne⟩ : ∃ m₁ ∈ M, L.map (MulAut.conj m₁).toMonoidHom ≠ L := by
      by_contra hcon
      push Not at hcon
      apply hNL
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h := hcon g g.2
      rw [← h]
      exact ⟨n, hn, by simp [MulAut.conj_apply]⟩
    have hLX : L ≤ d1PlusCore 3 N' (d1KBar 3 M N') := by
      have h1 := key 1 M.one_mem
      rwa [TenTenClaim.map_conj_one] at h1
    have hA : IsTwoPrimeComponent (d1PlusCore 3 N' (d1KBar 3 M N')) L :=
      IsTwoPrimeComponent.of_le hLc hLX hXM
    have hA' : IsTwoPrimeComponent (d1PlusCore 3 N' (d1KBar 3 M N'))
        (L.map (MulAut.conj m₁).toMonoidHom) :=
      IsTwoPrimeComponent.of_le (hLc.map_conj hm₁) (key m₁ hm₁) hXM
    have h3L' : 3 ∣ Nat.card (L.map (MulAut.conj m₁).toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective (MulAut.conj m₁).injective]
    have h2 := two_le_pRank_three_of_two_components hA hA' (Ne.symm hne) h3L h3L'
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
