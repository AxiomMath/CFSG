module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoSec
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoPartner

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

theorem twoSec_central_of_caseI (htri : ExactShapeTrichotomy) (hlookup : AltComponentLookup)
    (hHN : CFSG.ComponentClassification.RestrictedStd.Spor.HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : CFSG.ComponentClassification.RestrictedStd.Spor.FourExactOuterInput)
    (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) (hn12 : n ≠ 12)
    {S₀ : Finset (Fin n)} (hk : S₀.card = 3 ∨ S₀.card = 4) (hkn : S₀.card + 7 ≤ n)
    (hI : CaseIAt θ z S₀) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf T.toBase θ hx).IsSwap) (hx2 : x * x = 1) :
    ∀ c ∈ centralizer ({x} : Set G), ∃ o ∈ oddCoreOf (centralizer ({x} : Set G)),
      o * c ∈ centralizer ({z} : Set G) := by
  obtain ⟨-, hx1⟩ := swap_elt_ne T.toBase θ hx hτ
  have hzx : z ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.1 hx).symm
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hnear : ∀ (b : G) (hb : b ∈ centralizer ({z} : Set G)), IsConj z b → b ≠ z →
      5 ≤ (fixFin (permOf T.toBase θ hb)).card → (fixFin (permOf T.toBase θ hb)).card ≠ 6 →
        False := by
    intro b hb hzb hbz h5 h6
    obtain ⟨c, hc⟩ := isConj_iff.1 hzb
    exact near_partner_false T θ hk hkn hI hb hc hbz ⟨h5, h6⟩
  have hfus : ¬ IsConj z (z * x) := by
    intro hc
    have hzxC : z * x ∈ centralizer ({z} : Set G) := mul_mem hzC hx
    have hp : permOf T.toBase θ hzxC = permOf T.toBase θ hx := by
      rw [permOf_mul T.toBase θ hzC hx hzxC,
        (permOf_eq_one_iff T.toBase θ hzC).2 (T.cyc.le T.cyc.mem), one_mul]
    refine hnear (z * x) hzxC hc ?_ ?_ ?_
    · intro h'
      exact hx1 (mul_eq_left.1 h')
    · rw [hp, card_fixFin_of_isSwap hτ]; omega
    · rw [hp, card_fixFin_of_isSwap hτ]; omega
  rcases twoSec_cases_O htri hlookup hHN hOut hFour T θ hn hx hτ hx2 hfus hzx with
    h1 | ⟨b, hb, hzb, hbz, hcard⟩ | h1
  · exact h1
  · exfalso
    rcases hcard with h2 | h2 | h2 <;> exact hnear b hb hzb hbz (by omega) (by omega)
  · omega

end CFSG.OddStandard.AltStdCycTwo.Two
