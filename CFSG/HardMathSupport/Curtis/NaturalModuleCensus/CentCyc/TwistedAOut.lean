module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime
import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThree.PartOne.OutStructure

theorem not_dvd_add_one_of_torusFree {p : ℕ} (hp5 : 5 ≤ p)
    {q : TauCeti.PrimePower} {r₀ : ℕ}
    (ht : IndexTorusFree p (.twistedA r₀ q)) : ¬ p ∣ q.card + 1 := by
  simp only [IndexTorusFree] at ht
  rcases ht with h2 | hn
  · rw [h2]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  · intro hd
    apply hn
    have hq1 : 1 ≤ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact Nat.one_le_pow _ _ q.prime_p.pos
    have : q.card ^ 2 - 1 = (q.card - 1) * (q.card + 1) := by
      zify [hq1, Nat.one_le_pow 2 q.card hq1]
      ring
    rw [this]
    exact Dvd.dvd.mul_left hd _

theorem outPChain_twistedA {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : IsLieOfTorusFree IdxTwistedA p X) : OutPChain p X := by
  obtain ⟨⟨d, hv⟩, hPd, ht, ⟨e⟩⟩ := hX
  cases d with
  | twistedA r q =>
    have hq2 : q.p = 2 := hPd
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hq2] at hm
    have hc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
    exact (outPNice_PSU hp hm fun hd => not_dvd_add_one_of_torusFree hp5 ht
      (by rw [hc]; exact hd.trans (Nat.gcd_dvd_right _ _))).toChain
  | _ => exact hPd.elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
