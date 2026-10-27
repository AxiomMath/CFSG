module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowClauseO
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaModels
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaGamma
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaCount
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaType
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaBlockTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaBlockRest
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenBlock
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeNormalRank
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Normalizes
import CFSG.Timmesfeld.Opposite.Moufang
public import CFSG.Open.GriessAllModelsStatement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open TwelveSigma

variable {G : Type} [Group G] [Finite G]

theorem agl81TenTwelveSolvSigma_of (hKP : KFactParabolicSymThreeNormal) (hU : OutU33)
    (hGA : GriessAllModelsStatement) (hTPL : CitedBlockTransvectionPLType)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G) : AGL81TenTwelveSolvSigma G := by
  intro hS h3σ P M H Q K hd L hL I₀ hI₀ hb htarget J hJ hJK hJ3 hJsub hdir
  by_contra hJne
  have h984 : AGL81NineEightFour G := agl81NineEightFour_holds
  set O : Subgroup ↥H := primeComplementCore (G := H) 3 with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  set Bbar : Subgroup (↥H ⧸ O) := ((H ⊓ L).subgroupOf H).map π with hBbar
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hKne : K ≠ ⊥ := fun h => hd.not_le_X0 (by rw [h]; exact bot_le)
  have hKn : K.Normal := by
    rw [hd.kbar]
    exact d1KBar_normal_of_escape he hd.base hd.le_H (by rwa [← hd.kbar])
  have hI₀H : I₀ ≤ H := hI₀.le.trans inf_le_left
  have hI₀M : I₀ ≤ M := (hI₀.le.trans inf_le_right).trans hL.le
  obtain ⟨Syl, hSylK⟩ := hd.sylowK
  have hSfacts : SolvSigmaSylowFacts ↥K := solvSigmaSylowFacts_of_target htarget
  have hQX0 : (Q.subgroupOf H).map π ≤ d1X0 3 M H :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_inf hd.le_H hd.base.1))
  have hSY : (Syl : Subgroup ↥K).map K.subtype ≤ d1X0 3 M H := by
    rw [hSylK]
    exact inf_le_left.trans hQX0
  have hγ : ∀ A : Subgroup ↥K, A ≤ Syl → IsElemAbelian 3 A → Nat.card A = 27 →
      normalizer ((A.map K.subtype : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) ≤ d1X0 3 M H := by
    intro A hAS hA hA27
    have hAQ : A.map K.subtype ≤ (Q.subgroupOf H).map π := by
      calc A.map K.subtype ≤ (Syl : Subgroup ↥K).map K.subtype := Subgroup.map_mono hAS
        _ = (Q.subgroupOf H).map π ⊓ K := hSylK
        _ ≤ (Q.subgroupOf H).map π := inf_le_left
    refine normalizer_le_d1X0_of_elemAbelian (A := A.map K.subtype) (P := P) (M := M) (H := H)
      (Q := Q) hd hAQ (hA.map K.subtype) ?_
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hA27
  have htype : (∀ a ∈ J, ∀ b ∈ J, a * b = b * a) → Nat.card J = 3 :=
    fun hab => card_eq_three_of_comm hI₀H hb hJ hJ3 hJne hab
  obtain ⟨hJcard, y, hyX0, hy3, hyN, hy27⟩ :=
    exists_three_elt_not_mem_normalizer hKn hSfacts Syl hSY hγ hJK hJ3 hJne hJsub hdir htype
  have hb3 : Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3)) := by
    rcases hb with hb | hb
    · exact hb
    · exfalso
      refine not_comm_of_suThreeTwo hI₀H hb hJ ?_
      intro a ha b hbJ
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic ↥J := isCyclic_of_prime_card (p := 3) (by simpa using hJcard)
      exact Subtype.ext_iff.mp (hcyc.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hbJ⟩)
  obtain ⟨x, hxH, hxM, hx3, hxy⟩ := exists_three_elt_lift hyX0 hy3
  have hP : IsPGroup 3 (Subgroup.zpowers x) := by
    obtain ⟨k, hk⟩ := hx3
    refine IsPGroup.of_card_dvd_pow (p := 3) (n := k) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hk
  have hxL : x ∈ normalizer (L : Set G) :=
    le_normalizer_of_isPGroup_three3 hS.rank h3σ he.maxTwoLocal_M.1 hL.toIsTwoPrimeComponent hP
      (Subgroup.zpowers_le.mpr hxM) (Subgroup.mem_zpowers x)
  have hxHL : x ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := H) (K := L)
      ⟨Subgroup.le_normalizer hxH, hxL⟩
  have hAB : CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ H ⊓ L :=
    (CFSG.AGLEmbedding.oUpperTwo_le_self I₀).trans hI₀.le
  have hAx : ∀ n : ℕ, (CFSG.ComponentClassification.AS76b.oUpperTwo I₀).map
      (MulAut.conj (x ^ n)).toMonoidHom ≤ H ⊓ L := by
    intro n z hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    have hxn : x ^ n ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := pow_mem hxHL n
    exact (Subgroup.mem_normalizer_iff.mp hxn a).mp (hAB ha)
  have hconj : ∀ n : ℕ, J.map (MulAut.conj (y ^ n)).toMonoidHom ≤ Bbar := by
    intro n
    have hyx : π ((⟨x, hxH⟩ : ↥H) ^ n) = y ^ n := by rw [map_pow, hxy]
    rw [← hyx, hJ, ← CFSG.Timmesfeld.RankOne.map_map_conj,
      CFSG.Timmesfeld.map_conj_subgroupOf]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H (hAx n))
  have hJ0 : J ≤ Bbar := by
    rw [hJ]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hAB)
  have hJ1 : J.map (MulAut.conj y).toMonoidHom ≤ Bbar := by simpa using hconj 1
  have h27B : 27 ∣ Nat.card Bbar := by
    rw [← hy27]
    exact Subgroup.card_dvd_of_le (sup_le (sup_le hJ0 hJ1) (hconj 2))
  have h27PL : 27 ∣ Nat.card (blockParabolic M (pCoreOf 2 H) L) := by
    rw [blockParabolic_eq_of_cfg h984 hS hd L]
    exact twentySeven_dvd_card_barM inf_le_left (inf_le_right.trans hL.le) h27B
  have hr : Open.pRank 3 (barM M L) ≤ 3 :=
    pRank_barM_le_three_of_cfg hS hd L 3 Nat.prime_three (by norm_num)
  have hTHM : barM M I₀ ∈ cZero (blockParabolic M (pCoreOf 2 H) L) := by
    rw [blockParabolic_eq_of_cfg h984 hS hd L]
    exact (barM_mem_cZero (M := M) (X := H ⊓ L) (I := I₀) (inf_le_right.trans hL.le)
      hI₀ hb3).1
  have hT3 : Nonempty (↥(barM M I₀) ⧸ CFSG.pCore 2 ↥(barM M I₀) ≃* Equiv.Perm (Fin 3)) :=
    (barM_mem_cZero (M := M) (X := H ⊓ L) (I := I₀) (inf_le_right.trans hL.le) hI₀ hb3).2
  have hblock : BlockL28Hyps M (pCoreOf 2 H) L :=
    blockL28Hyps_of_cfg h85 h93 hD2 h984 hS hd hL
  obtain ⟨hK8, hA, -, hconc, hX, hSyl⟩ := hblock
  have hxLbar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈
      normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    CFSG.AGLEmbedding.mem_normalizer_barM hxM hxL
  have hxP : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈
      normalizer (blockParabolic M (pCoreOf 2 H) L :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [blockParabolic_eq_of_cfg h984 hS hd L]
    exact CFSG.AGLEmbedding.mem_normalizer_barM hxM hxHL
  have hxM3 : ∃ k : ℕ, (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩) ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hx3
    refine ⟨k, ?_⟩
    rw [← map_pow, show (⟨x, hxM⟩ : ↥M) ^ 3 ^ k = 1 from Subtype.ext hk, map_one]
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact hX h1
  · apply hyN
    rw [← hxy]
    have hres := mk_mem_normalizer_of_barM (M := M) (H := H) (I₀ := I₀) hI₀H hI₀M hA.twoCore_le
      hxH hxM (mem_normalizer_of_nineThreeTwo hKP hU hGA hL h2 hr hTHM hT3 hxM3 hxLbar hxP)
    simpa [hJ, hπ, hO] using hres
  · exact false_of_nineThreeRest hTPL hK8 hA hL hX hSyl (Or.inl h3) hr hTHM hT3 h27PL
  · exact false_of_nineThreeRest hTPL hK8 hA hL hX hSyl (Or.inr (Or.inl h4)) hr hTHM hT3 h27PL
  · exact false_of_nineThreeRest hTPL hK8 hA hL hX hSyl (Or.inr (Or.inr (Or.inl h5)))
      hr hTHM hT3 h27PL
  · exact false_of_nineThreeRest hTPL hK8 hA hL hX hSyl (Or.inr (Or.inr (Or.inr (Or.inl h6))))
      hr hTHM hT3 h27PL
  · exact false_of_nineThreeRest hTPL hK8 hA hL hX hSyl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))) hr hTHM hT3 h27PL
  · exact false_of_nineThreeRest hTPL hK8 hA hL hX hSyl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h8))))) hr hTHM hT3 h27PL

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
