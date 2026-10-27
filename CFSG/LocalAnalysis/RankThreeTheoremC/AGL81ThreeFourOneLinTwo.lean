module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneTrivialOn
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryLin
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialFamilies
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.NonUnitary
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

theorem signalizerThreeLinTwo_holds : SignalizerThreeLinTwo := by
  intro p hp hp5 q d hqp hqe hd K _ _ hK
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  refine signalizerThreeOn_of_signalizerTrivialOn hp (by omega) fun P W hW hnorm => ?_
  have hdL : IsLinTwoIndex p q.exponent d := ⟨q, hd, hqp, rfl⟩
  have D := smallRankOneData_of_isLinTwo hp2 hqe hdL hK P
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdL
  set e : K ≃* PSL2GF p q.exponent := e₁.trans e₂
  have hfs : Function.Surjective e.toMonoidHom := e.surjective
  have hmap := (Sylow.coe_mapSurjective hfs P).symm
  obtain ⟨hel, hcard⟩ := psl2GF_sylow p q.exponent (by omega) (P.mapSurjective hfs)
  have hPcard : Nat.card (P : Subgroup K) = p ^ q.exponent := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap]
    exact hcard
  have hPexp : ∀ x ∈ (P : Subgroup K), x ^ p = 1 := by
    intro x hx
    have h1 : e x ∈ ((P.mapSurjective hfs : Sylow p (PSL2GF p q.exponent)) :
        Subgroup (PSL2GF p q.exponent)) := by
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    apply e.injective
    rw [map_pow, hel.2 (e x) h1, map_one]
  exact signalizer_eq_bot_of_ti_planes hp P D.center D.ti D.inner
    (le_iSup_planes_of_card _ hqe hPcard hPexp) W hW hnorm

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
