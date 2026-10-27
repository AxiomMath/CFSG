module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbCore
public import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.false_of_le_centralizer_comps (hd : D1OneSmallData 3 P M H R Rbar K)
    (h3 : D1PhaseThree 3 P M H R) (hU : KFactUPrime 3 K) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hO : CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥)
    {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hAp : IsPGroup 3 A) (hA1 : A ≠ ⊥)
    (hcomp : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      A ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hodd : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ 3 →
      A ≤ Subgroup.centralizer ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      4 ≤ CFSG.Open.pRank s (CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))) : False := by
  have hle : A ≤ CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) := by
    refine le_pCore_of_le_centralizer_components hAp hcomp fun l hl => ?_
    by_cases hl2 : l = 2
    · rw [hl2, pCore_quotient_pCore_eq_bot']
      exact Subgroup.le_centralizer_iff.mp bot_le
    by_cases hl3 : l = 3
    · rw [hl3, hO]
      exact Subgroup.le_centralizer_iff.mp bot_le
    rcases hodd l hl hl2 hl3 with h | h
    · exact h
    · exfalso
      have hcop : l.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
        rw [hk]
        exact ((Nat.coprime_primes hl Nat.prime_two).mpr hl2).pow_right k
      have hmap := pRank_map_mk_eq_pRank_map_subtype hl (CFSG.pCore 2 ↥M) hcop
        ((CFSG.pCore l (↥M ⧸ CFSG.pCore 2 ↥M)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))
      rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hmap
      exact hd.false_of_four_le_pRank h3 hU h84 hD2 hl hl2 hl3 (hmap ▸ h)
  rw [hO] at hle
  exact hA1 (le_bot_iff.mp hle)

theorem mem_centralizer_weakSBlock_of_kFact (hKB : KFactBlockThreeCentCoprime)
    (h3 : D1PhaseThree 3 P M H R) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {zb : ↥M ⧸ CFSG.pCore 2 ↥M} (hzb3 : zb ^ 3 = 1)
    (hZ : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → D = ⊥)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {t : ↥M ⧸ CFSG.pCore 2 ↥M}
    (htL : t ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (htz : t ∈ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (ht6 : Nat.Coprime 6 (orderOf t)) :
    t ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hKeq := h3.inf_eq_inf_normalizer_twoCore
  have hperfM : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) →
      ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y) := fun Y hY hYp =>
    hperf Y (hKeq ▸ hY) hYp
  exact hKB G M (pCoreOf 2 H) L h3.isKGroup.1 h3.asc81bHyp hL (h3.nineThree h93 hL)
    (h3.nineThree_not_one h85 hD2 hL).1 (h3.not_isSylowTwoOf_inf h85 hD2 hL) hperfM zb
    (mem_normalizer_of_no_perfect_centralizer hL.component hzb3 hZ) hzb3
    (not_mem_centralizer_of_no_perfect_centralizer hL.component hZ)
    (fun D _ hD hDz => hZ D hD hDz) t htL htz ht6

theorem le_centralizer_threeComponents_of_torus (hKB : KFactBlockThreeCentCoprime)
    (h3 : D1PhaseThree 3 P M H R) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hrank : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {zb : ↥M ⧸ CFSG.pCore 2 ↥M} (hzb3 : zb ^ 3 = 1)
    (hZ : ∀ D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → D = ⊥)
    {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hA : IsMulCommutative A) (hA4 : 4 ≤ Nat.card A)
    {t : ↥M ⧸ CFSG.pCore 2 ↥M} (htr : Nat.Coprime 6 (orderOf t))
    (htz : t ∈ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (htA : t ∈ Subgroup.normalizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hnt : ∃ x ∈ A, t * x * t⁻¹ ≠ x)
    (hirr : ∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), F ≤ A →
      t ∈ Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → F = ⊥ ∨ F = A)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (h3d : ¬ Nat.Coprime 3 (Nat.card Lb)) :
    A ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨L, hL, rfl⟩ := (weakSBlock_or_coprime_of_component h3 hperf hLb).resolve_right h3d
  have htL := mem_normalizer_of_coprime_six h3 hB3 hrank hperf hLb h3d htr
  have hAL := le_normalizer_of_irreducible h3 hB3 hrank hperf hLb h3d hA4 htA htL hirr
  exact le_centralizer_of_irreducible hA htA hirr hnt hAL
    (mem_centralizer_weakSBlock_of_kFact hKB h3 h85 h93 hD2 hperf hzb3 hZ hL htL htz htr)

theorem oddCore_dichotomy_of_torus {M : Subgroup G} {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hA : IsElemAbelian 3 A) (hA9 : 3 ^ 2 ≤ Nat.card A) {t : ↥M ⧸ CFSG.pCore 2 ↥M} {r : ℕ}
    (hr4 : 4 ≤ r) (htA : t ∈ Subgroup.normalizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hirr : ∀ k : ℕ, ¬ r ∣ k → ∀ Y₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Y₀ ≤ A →
      t ^ k ∈ Subgroup.normalizer (Y₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → Y₀ = ⊥ ∨ Y₀ = A)
    (s : ℕ) (hs : s.Prime) (hs2 : s ≠ 2) (hs3 : s ≠ 3) :
    A ≤ Subgroup.centralizer ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      4 ≤ CFSG.Open.pRank s (CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  by_cases hc : A ≤ Subgroup.centralizer ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) :
      Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  · exact Or.inl hc
  right
  have : Fact s.Prime := ⟨hs⟩
  have hn : (CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).Normal := CFSG.pCore_normal
  have hN : ∀ g : ↥M ⧸ CFSG.pCore 2 ↥M,
      g ∈ Subgroup.normalizer ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hn]
    exact Subgroup.mem_top g
  have h := stmtOddCoreRank' hs hs2 Nat.prime_three hs3 (CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)) A
    t CFSG.pCore_isPGroup (fun a _ => hN a) hA hA9 (hN t) htA hirr hc
  omega

end CFSG.AGLEmbedding
