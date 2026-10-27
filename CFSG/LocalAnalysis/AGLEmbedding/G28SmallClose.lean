module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBlockInner
public import CFSG.LocalAnalysis.AGLEmbedding.G28Small
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorCommutator
public import CFSG.LocalAnalysis.AGLEmbedding.A9MSideOneAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section CaseTwoClose

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G} {z : G}

omit [Finite G] in
theorem blockParabolic_le_barM {L : Subgroup G} (hKeq : H ⊓ M = M ⊓
      Subgroup.normalizer (pCoreOf 2 H : Set G)) (hLM : L ≤ M) {T : Subgroup G}
    (hPi : (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ≤ T) :
    blockParabolic M (pCoreOf 2 H) L ≤ barM M T := by
  refine Subgroup.map_mono (Subgroup.comap_mono (fun x hx => hPi ⟨?_, ?_⟩))
  · exact hKeq ▸ ⟨hLM hx.2, hx.1⟩
  · exact Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1
      (Subgroup.mem_iSup_of_mem (H ⊓ M).one_mem ⟨x, hx.2, by simp⟩))

theorem D1G28Data.false_of_le_zpowers_sup (h : D1G28Data P M H R z) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer) (hOut : KFactBlockThreeOut)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hPi : (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ≤ Subgroup.zpowers z ⊔ GLBPrimeCore 3 H) :
    False := by
  have h3 := h.ph3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  set S := pCoreOf 2 H with hSdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLbdef
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  set T := Subgroup.zpowers z ⊔ GLBPrimeCore 3 H with hT
  obtain ⟨hTM, hTH, hQT, hT3⟩ := h.small_T
  have hRL := h.le_normalizer_block hB3 hL hPi
  have hC := h.inf_blockCentralizer_eq_bot hB3 hL hPi
  have hRM : R ≤ M := h3.le_M
  have hR3 : IsPGroup 3 R := h3.isPGroup_R
  have hUS : barM M R ≤ barM M (Subgroup.normalizer (S : Set G)) :=
    Subgroup.map_mono (Subgroup.comap_mono ((hKeq ▸ h3.le_inf).trans inf_le_right))
  have hUN : barM M R ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hL' : L.map (MulAut.conj (x : G)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRL (Subgroup.mem_subgroupOf.mp hx))
    have hLbar : (barM M L).map (MulAut.conj (mk x)).toMonoidHom = barM M L := by
      rw [← barM_map_conj x.2, hL']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLbar
  have hU3 : IsPGroup 3 (barM M R) := (hR3.comap_subtype (K := M)).map _
  have hPLT := blockParabolic_le_barM hKeq hL.le hPi
  have hTN : ⁅T, T⁆ ≤ GLBPrimeCore 3 H :=
    commutator_sup_le_of_comm (fun a ha b hb' => by
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb'
      exact (Commute.zpow_zpow_self z i j).eq)
      (Subgroup.zpowers_le.mpr (le_normalizer_glbPrimeCore 3 H (h3.le_H h.z_mem)))
  have hperf : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockParabolic M S L →
      ⁅W, W⁆ = W → Nat.Coprime 3 (Nat.card W) := by
    intro W hW hWW
    have hWN : W ≤ barM M (GLBPrimeCore 3 H) := by
      rw [← hWW]
      exact (Subgroup.commutator_mono (hW.trans hPLT) (hW.trans hPLT)).trans
        ((commutator_barM_le M T).trans (Subgroup.map_mono (Subgroup.comap_mono hTN)))
    exact Nat.Coprime.coprime_dvd_right ((Subgroup.card_dvd_of_le hWN).trans
      (card_barM_dvd h3.primeCore_le)) (glbPrimeCore_coprime 3 H)
  have hγ := hOut G M S L h3.isKGroup.1 h3.asc81bHyp hL (h3.nineThree h93 hL)
    (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL) hperf
    (barM M R) hUS hUN hU3
  set I := barM M R ⊓ (Lb ⊔ Cb) with hI
  have hIC : I ⊓ Cb = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨⟨⟨r, hrM⟩, hr, rfl⟩, -⟩, hrC⟩
    have hrC' : r ∈ R ⊓ blockCentralizer M L :=
      ⟨Subgroup.mem_subgroupOf.mp hr, (mem_blockCentralizer_iff ⟨r, hrM⟩).mpr hrC⟩
    rw [hC, Subgroup.mem_bot] at hrC'
    subst hrC'
    exact Subgroup.mem_bot.mpr (map_one (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))
  have hLbN : Lb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := Subgroup.le_normalizer
  have hPLL : blockParabolic M S L ≤ Lb := Subgroup.map_mono (Subgroup.comap_mono inf_le_right)
  have hIdvd : Nat.card I ∣ Nat.card (blockParabolic M S L) :=
    card_dvd_of_faithful_inner (inf_le_left.trans hUN) (hPLL.trans hLbN) hIC fun x hx =>
      h3.exists_mem_blockParabolic h84 h86 hD2 hb hL (hUS hx.1) hx.2
  have hI3 : Nat.card I ≤ 3 := by
    obtain ⟨a, ha⟩ := (hU3.to_le (inf_le_left : I ≤ barM M R)).exists_card_eq
    rw [ha]
    refine pow_le_of_dvd_card hT3 ((ha ▸ hIdvd).trans ((Subgroup.card_dvd_of_le hPLT).trans
      (card_barM_dvd hTM)))
  have hcardU : Nat.card (barM M R) = 3 ^ 6 := by
    rw [card_barM_of_isPGroup Nat.prime_three (by norm_num) hRM hR3, h.card_R]
  have hmul := (I.subgroupOf (barM M R)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : I ≤ barM M R)).toEquiv,
    hcardU] at hmul
  have hidx : (I.subgroupOf (barM M R)).index ≤ 3 := hγ
  have := Nat.mul_le_mul hI3 hidx
  rw [hmul] at this
  norm_num at this

end CaseTwoClose

end CFSG.AGLEmbedding
