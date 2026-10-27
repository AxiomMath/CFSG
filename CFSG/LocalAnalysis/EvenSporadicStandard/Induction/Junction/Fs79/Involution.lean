module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.LtStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Last
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Thm13Guarded

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup Relation CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem conn_of_involution_at (h13 : FS79Thm13UseAt H) (hQ : Sol78RankOne) (hD : Sol78ExcClosed)
    (hcor : ∀ (G : Type) [Group G] [Finite G],
      CFSG.SignalizerFunctorTheorem.IsSectionOf G H → Nat.card G < Nat.card H → Cor23SAt G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {N : Subgroup H} (hN : FStarSimple N)
    (hperf : ∀ P : Subgroup H, ⁅P, P⁆ = P → P ≤ N)
    {t : H} (ht : orderOf t = 2) {K : Subgroup H} (hK : IsCompIn K (centralizer ({t} : Set H)))
    (hexc : NotExc K) : LConn K N := by
  obtain ⟨M, hKM, hmax, -⟩ := HSStd.Zassenhaus.exists_maximalF_above (⟨t, ht, hK⟩ : InLF K)
  have hconn : LConn K M := by
    rcases hKM with rfl | hKM'
    · exact LConn.refl (isPGroup_zpowers_of_orderOf_two ht) (by
        rw [centralizer_zpowers_eq]
        exact hK)
    · exact transGen_ltF_conn hD hcor hkp hKM' hexc
  have hexcM : NotExc M := hconn.notExc hD hexc
  have hstd : StdBare M :=
    h13 hkp N hN hperf M hmax fun hr1 =>
      absurd (hQ ↥M hmax.1.isQuasisimple hr1) (notExc_iff.1 hexcM)
  obtain ⟨t', ht', hMt'⟩ := hmax.1
  exact hconn.trans (last_link hN hperf ht' hMt' hstd)

end CFSG.EvenSporadicStandard.Induction.Junction
