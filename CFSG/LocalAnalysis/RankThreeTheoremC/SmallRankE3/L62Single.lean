module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.K3Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem single_component_delta {X : Type} [Group X] [Finite X] (hT : T29.GL83I291Three)
    {S : Sylow 3 X} {x : X} (hSr : 3 ≤ CFSG.Open.pRank 3 (S : Subgroup X)) (hxS : x ∈ (S : Subgroup X))
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hxr : CFSG.Open.pRank 3 (centralizer ({x} : Set X)) ≤ 2)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections X)
    (hcore : primeComplementCore (G := X) 3 = ⊥) {L : Subgroup X} (hLc : IsComponentOf L ⊤)
    (huniq : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = L)
    (hno : ∀ N : Subgroup X, N.Normal → N.index ≠ 3) :
    IsCyclic ↥(CFSG.pCore 3 X) ∧ 9 ≤ Nat.card ↥(CFSG.pCore 3 X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    hSr.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top)
  have hcent : CFSG.Open.pRank 3 (centralizer ({x} : Set X)) = 2 :=
    T29.pRank_centralizer_eq_two_of_sylow hSr hxS hxord hxr
  have hsetup : T29.T29Setup X L x := ⟨hcat, hcore, hLc, huniq, hrank, hxord, hcent⟩
  obtain ⟨hcyc, -, -, hconc⟩ := hT X hcat hcore L hLc huniq hrank x hxord hcent
  rcases hconc with ⟨hLε, -, -, -, hfield | h9⟩ | hb
  · obtain ⟨y, hy, hyf⟩ := hfield
    obtain ⟨N, hN, hNi⟩ := T29.exists_normal_index_three_of_field hsetup hLε hy hyf
    exact absurd hNi (hno N hN)
  · exact ⟨hcyc, h9⟩
  · obtain ⟨e', -, -⟩ := id hb
    have hZ : center ↥L = ⊥ := T29.k3_center_eq_bot_of_psl227 hLc.2.2.1 e'
    have hC : centralizer (L : Set X) = ⊥ := hsetup.centralizer_eq_bot hZ
    haveI : L.Normal := hsetup.normal
    obtain ⟨N, hN, hNi⟩ := K2.exists_index_three_normal hsetup.normal ⟨e'⟩ hC
      (T29.index_eq_of_fieldAut_L227 hC hb)
    exact absurd hNi (hno N hN)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
