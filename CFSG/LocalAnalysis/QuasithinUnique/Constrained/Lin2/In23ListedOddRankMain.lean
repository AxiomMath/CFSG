module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankLin3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankSp4

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.QuasithinUnique.Lin2.OddRank

theorem listedLin2OddRank
    : ListedLin2OddRank := by
  intro G _ _ M S K L z n hn hs hl hZ hLK hq hlist
  have hn2 : 2 ≤ n := hn
  have hd := two_pow_dvd_card_K hs hl hZ hLK
  rcases hlist with hB | hR | hA7 | hL33 | hL2p | hS | h42
  · exact (false_bender hs hl hZ hn2 hLK hB).elim
  · rcases hR with ⟨m, hm, hmod⟩ | ⟨m, hm, hmod⟩ | ⟨⟨e⟩⟩ | hcov | ⟨-, hc, ⟨e⟩⟩
    ·
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmod
      obtain ⟨p, hp, hpd, hprk⟩ := exists_prime_pRank_psl3 (m := m) hm hn2
        ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
        (fun ℓ hℓ hdvd => exists_norm_elem_K hs hl hZ hn2 hLK hℓ hdvd)
      exact ⟨p, hp, hpd, le_pRank_of_equiv (MulEquiv.refl ↥K) hp.one_lt hprk⟩
    ·
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmod
      obtain ⟨p, hp, hpd, hprk⟩ := exists_prime_pRank_psp4 (m := m) hn2
        ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
        (fun ℓ _ hdvd => prime_dvd_card_of_le hl hLK hdvd)
      exact ⟨p, hp, hpd, le_pRank_of_equiv (MulEquiv.refl ↥K) hp.one_lt hprk⟩
    · exact (false_alt_six hn2 hd e).elim
    ·
      obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hcov
      obtain ⟨p, hp, hpd, hprk⟩ := exists_prime_pRank_psl3 (m := 2) (by norm_num) hn2
        ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
        (fun ℓ hℓ hdvd => exists_norm_elem_quot hs hl hZ hn2 hq hLK hℓ
          (ne_two_of_dvd_two_pow_sub_one (by omega) hdvd) hdvd)
      exact ⟨p, hp, hpd, two_le_pRank_of_quot hp
        (ne_two_of_dvd_two_pow_sub_one (by omega) hpd) hprk⟩
    · exact (false_cover_six hn2 hd hc e).elim
  · rcases hA7.1 with ⟨⟨e⟩⟩ | ⟨-, hc, ⟨e⟩⟩
    · exact (false_alt_seven hn2 hd e).elim
    · exact (false_cover_seven hn2 hd hc e).elim
  · rcases hL33.1 with h | ⟨⟨e⟩⟩
    · exact (false_L33 hn2 hd h).elim
    · exact (false_M11 hn2 hd e).elim
  · obtain ⟨p, hp, h⟩ := hL2p.1
    exact (false_L2p hs hl hZ hn2 hLK hp h).elim
  · rcases hS with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · obtain ⟨Ub, -, hUe, hcard, -, -⟩ := exists_blockU_K hs hl hZ hn2 hLK
      exact concl_M22 hn2 e hUe hcard
    · obtain ⟨Ub, hUe, hcard⟩ := exists_blockU_quot hs hl hZ hq hLK
      exact concl_M22_cover hn2 e hUe hcard
    · obtain ⟨Ub, -, hUe, hcard, -, -⟩ := exists_blockU_K hs hl hZ hn2 hLK
      exact concl_M23 hn2 e hUe hcard
  · exact concl_L42 hn2 hd h42.1

end CFSG.QuasithinUnique.Lin2
