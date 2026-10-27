module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
import CFSG.LocalAnalysis.AGLEmbeddingD2.GuestThree
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem four_le_pRank_of_fi22 (hFA : KFactFi22AltSection) (hK6 : KFactFi22GuestRank)
    {p : ℕ} {H : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hFi : IsFi22 K) : 4 ≤ Open.pRank 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup H := primeComplementCore (G := H) p with hN
  obtain ⟨n, J, hn, ⟨e⟩⟩ := hFA K hFi
  rw [SectionRank.pRank_eq_pRank_top_subgroup H]
  have hsec := AGLEmbeddingD2.le_pRank_of_alt_le_range (QuotientGroup.mk' N) hn (J.map K.subtype)
    (by rw [QuotientGroup.range_mk']; exact le_top)
    ((J.equivMapOfInjective K.subtype K.subtype_injective).symm.trans e)
  by_cases h3N : 3 ∣ Nat.card N
  · exact hsec.2 (by rwa [QuotientGroup.ker_mk'])
  · have heq := pRank_quotient_map_of_coprime_normal 3 Nat.prime_three N h3N ⊤
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at heq
    rw [← heq]
    obtain ⟨T₁⟩ : Nonempty (Sylow 5 K) := inferInstance
    obtain ⟨E, -, hE, hEcard⟩ := hK6 K hFi T₁
    have hE' := elementary_abelian_map 3 hE K.subtype
    have hcard : Nat.card (E.map K.subtype) = 3 ^ 4 := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard]
    exact le_csSup (pRank_bddAbove 3 Nat.prime_three _) ⟨E.map K.subtype, le_top, hE', hcard⟩

theorem d1SmallGEVNormalFi22_of (hFA : KFactFi22AltSection) (hK6 : KFactFi22GuestRank) :
    D1SmallGEVNormalFi22 := by
  intro G _ _ p P M H R Rbar K hd z _ _ _ _ _ _ hFi h3 _ _ _ _ _ _
  exact h3 (mem_glbBetaFour_of_le_pRank Nat.prime_three (by norm_num)
    hd.cfg.ext.maxTwoLocal_H.1 le_rfl (four_le_pRank_of_fi22 hFA hK6 hFi))

end CFSG.AGLEmbedding
