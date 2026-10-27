module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFiveOfRankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.Open CFSG.SectionRank CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def CentRankThreeAt (p : ℕ) (M : Subgroup G) : Prop :=
  ∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
    3 ≤ Open.pRank p (centralizer (E : Set G) ⊓ M)

@[expose] def AGL81TenElevenOneDisc (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (L W : Subgroup G) (a₀ : G),
    AGL81ElevenNineData 3 P M H Q K L W a₀ → ∀ V : Sylow 3 G, (V : Subgroup G) ≤ M →
      ¬ CentRankThreeAt 3 M → HasNormalIndex M 3 →
      rankThreeGamma 2 3 (V : Subgroup G) ≤ M ∨
        Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* alternatingGroup (Fin 10)) ∨
        Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* Equiv.Perm (Fin 10))

theorem rankThreeGamma_le_of_centRankThreeAt {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (hesc : D1Escape p P M H₁ R₁) (V : Sylow p G) (hVM : (V : Subgroup G) ≤ M)
    (hc : CentRankThreeAt p M) :
    rankThreeGamma 2 p (V : Subgroup G) ≤ M := by
  haveI : Fact p.Prime := ⟨hesc.prime⟩
  obtain ⟨m, hm, hVeq⟩ := exists_mem_eq_map_conj_of_sylow_le P V hesc.sylow_le hVM
  have hW : GLBWeakCore p (V : Subgroup G) ≤ M := by
    rw [hVeq]; exact weakCore_conj_le hesc.prime hesc.weakCore_le hm
  have h3 : 3 ≤ Open.pRank p (V : Subgroup G) := by
    rw [← sylow_pRank_eq p hesc.prime P V]
    exact hesc.three_le_pRank.trans (pRank_mono hesc.prime.one_lt hesc.le_P)
  exact pGroupLemmaFiveOneFive p hesc.prime hesc.ne_two M V hVM h3 hW hc

theorem AGL81ElevenNineData.tenElevenOne (hS : Setting G) {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L W : Subgroup G} {a₀ : G}
    (hd : AGL81ElevenNineData 3 P M H Q K L W a₀) (h : AGL81TenElevenOneDisc G)
    (V : Sylow 3 G) (hVM : (V : Subgroup G) ≤ M) (hNI : HasNormalIndex M 3) :
    rankThreeGamma 2 3 (V : Subgroup G) ≤ M ∨
      Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* alternatingGroup (Fin 10)) ∨
      Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* Equiv.Perm (Fin 10)) := by
  by_cases hc : CentRankThreeAt 3 M
  · obtain ⟨H₁, R₁, hesc⟩ := hd.data.escape
    exact Or.inl (rankThreeGamma_le_of_centRankThreeAt hesc V hVM hc)
  · exact h hS P M H Q K L W a₀ hd V hVM hc hNI

end CFSG.LocalAnalysis.RankThreeTheoremC
