module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLieCharRankProof
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinTwo
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open scoped MatrixGroups

theorem kdI278ChevP_holds :
    KDI278ChevP := by
  intro p hp hp5 K _ _ hs hnab hlie hrk
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨d, ⟨e⟩, hchar⟩ := hlie
  by_cases hsmall : CFSG.AGLEmbeddingD2.IsD2LieCharSmall p d.1
  · obtain ⟨q, hqp, h⟩ := hsmall
    rcases h with ⟨hexp, hd⟩ | ⟨hexp, hd | hd⟩
    · have hpos := q.exponent_pos
      rcases (by omega : q.exponent = 1 ∨ q.exponent = 2) with h1 | h2
      · exfalso
        have := CFSG.AGLEmbeddingD2.kFactLinTwoPrimeRank K d ⟨e⟩ p hp hp2 ⟨q, hqp, h1, hd⟩
        omega
      · left
        obtain ⟨f⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := p) (n := 2)
          (d := d) ⟨q, hd, hqp, h2⟩
        exact ⟨⟨hp⟩, ⟨e.trans f⟩⟩
    · right
      left
      obtain ⟨dv, hv⟩ := d
      simp only at hd
      subst hd
      obtain ⟨-, F, hF, hFin, hcard, ⟨e'⟩⟩ :=
        CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      refine ⟨F, hF, hFin, ?_, ⟨?_⟩⟩
      · rw [hcard, hqp, hexp, pow_one]
      · exact e'
    · right
      right
      obtain ⟨dv, hv⟩ := d
      simp only at hd
      subst hd
      obtain ⟨-, F, hF, hFin, hcard, ⟨e'⟩⟩ :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hpe : q.p ^ q.exponent = p := by rw [hqp, hexp, pow_one]
      have key : ∀ N : ℕ, N = p → (K ≃* StatedProj (StatedSU 3 N F)) →
          Nonempty (K ≃* StatedProj (StatedSU 3 p F)) := by
        intro N hN e''
        subst hN
        exact ⟨e''⟩
      exact ⟨F, hF, hFin, by rw [hcard, hpe], key _ hpe e'⟩
  · exfalso
    have := CFSG.AGLEmbeddingD2.kFactLieCharRank K d ⟨e⟩ p hp hp2 hchar.symm hsmall
    omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
