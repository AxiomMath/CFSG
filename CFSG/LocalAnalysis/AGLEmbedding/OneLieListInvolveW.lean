module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0ThreeCases
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJ
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.four_le_evenRank (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) : 4 ≤ evenRank G := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set A := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K with hA
  have h3 : 3 ≤ Open.pRank p A := by
    have h := hd.three_le_pRank_d1LiftX hT
    rwa [← Subgroup.map_subgroupOf_eq_of_le (d1LiftX_le_H p H R K),
      ← pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      hd.cfg.map_d1LiftX_eq_inf] at h
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  have hz1 : z ≠ 1 := fun h => hzK (h ▸ K.one_mem)
  have hzA : z ∈ Subgroup.centralizer (A : Set (H ⧸ primeComplementCore (G := H) p)) :=
    Subgroup.centralizer_le inf_le_right hzc
  have hdisj : Subgroup.zpowers z ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxz, hxA⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hx1' : (⟨x, hxz⟩ : Subgroup.zpowers z) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have htop := zpowers_eq_top_of_prime_card (G := Subgroup.zpowers z)
      (by rw [Nat.card_zpowers, hzp]) hx1'
    have hmem : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
        Subgroup.zpowers (⟨x, hxz⟩ : Subgroup.zpowers z) := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm⟩ := hmem
    apply hzK
    have hxm : x ^ m = z := congrArg Subtype.val hm
    rw [← hxm]
    exact K.zpow_mem (Subgroup.mem_inf.mp hxA).2 m
  have h4 := CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers (q := p) A
    (by have h := pow_orderOf_eq_one z; rwa [hzp] at h) hz1 hzA hdisj
  have hR : Open.pRank p (A ⊔ Subgroup.zpowers z) ≤
      Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
    pRank_mono p hp (sup_le inf_le_left (Subgroup.zpowers_le.mpr hzR))
  have hRR : Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) =
      Open.pRank p R := by
    rw [hd.cfg.rbar, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      Subgroup.map_subgroupOf_eq_of_le hd.cfg.ext.le_H]
  have hRH : Open.pRank p R ≤ Open.pRank p H := pRank_mono p hp hd.cfg.ext.le_H
  have hHe := local_pRank_le_evenRank p hp hd.cfg.red.ne_two H hd.cfg.ext.maxTwoLocal_H.1
  omega

@[expose] def KFactOneLieListInvolveW : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      ((∃ d : TauCeti.ValidLieTypeIndex, IsP1ChevTwoSurvivor p d ∧
          Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
        Nonempty (L ≃* alternatingGroup (Fin (3 * p))) ∨
        (p = 3 ∧ Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .J3).Group))) →
      ∀ (Y : Subgroup L) (φ : Y →* K), Function.Surjective φ →
        p.Coprime (Nat.card φ.ker) → False

end CFSG.AGLEmbedding
