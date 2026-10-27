module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslCoprime
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslDiag
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Linear

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

theorem crossClassical_psl : CrossClassical .PSL 3 := by
  intro K _ _ n ℓ f p _ hp2 hpℓ hn hnot h
  have hp := (Fact.out : p.Prime)
  have h' := h
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h'
  have hℓ : ℓ.Prime := hadm.1
  have hpq : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  haveI : NeZero n := ⟨by omega⟩
  haveI : Finite (StatedProj (StatedSL n F)) := Finite.of_equiv K e.toEquiv
  by_cases hq1 : p ∣ Nat.card F - 1
  · by_cases hpn : p ∣ n
    · have hspec : ¬ (n = 3 ∧ p = 3 ∧ ¬ 9 ∣ ℓ ^ f - 1) := by
        rintro ⟨rfl, rfl, h9⟩
        apply hnot
        have hq3 : 3 ∣ ℓ ^ f - 1 := by rw [← hF]; exact hq1
        right
        right
        refine ⟨rfl, rfl, Or.inl ⟨rfl, ?_⟩⟩
        omega
      refine WCOn.of_not_isMulCommutative fun P => ?_
      exact InnerAction.n1PSL_holds K n ℓ f h p hp hp2 hpn (by rw [← hF]; exact hq1) hspec P
        P.isPGroup' P.not_dvd_index
    · exact WCOn.of_mulEquiv e (wcOn_projSL_of_dvd_sub_one hp2 hn hq1 hpn)
  · exact WCOn.of_mulEquiv e (wcOn_projSL_of_not_dvd_sub_one hp2 hpq hq1)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
