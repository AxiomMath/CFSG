module

public import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316.LinTwo
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34
public import CFSG.RankThree.PartTwo.KFacts.KS18L34GenProof

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316

open CFSG.AGLEmbedding CFSG.Open

theorem planesGenerate_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n) (hq : 3 < p ^ n) :
    PlanesGenerate p (PSL2GF p n) := by
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p n)) :=
    ⟨p, n, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, hn, hcard⟩
  exact planesGenerate_psl2 (F := GaloisField p n) hp2 hodd (by rw [hcard]; exact hq)

theorem planesGenerate_of_isLinTwoIndex {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d) :
    PlanesGenerate p (CatGroup d) := by
  obtain ⟨ε⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hn : 1 ≤ n := by
    obtain ⟨q, -, -, hqn⟩ := hd
    exact hqn ▸ q.exponent_pos
  have hq : 3 < p ^ n := by
    obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
    obtain ⟨q, hq, hqp, hqn⟩ := hd
    simp only at hq
    subst hq
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff] at hv
    have h4 := hv.1.2 rfl
    rw [TauCeti.PrimePower.card_def, hqp, hqn] at h4
    omega
  exact planesGenerate_of_mulEquiv ε.symm (planesGenerate_psl2GF hp2 hn hq)

theorem planesGenerate_of_isLinThreeFour {K : Type} [Group K] [Finite K] (hK : IsLinThreeFour K) :
    PlanesGenerate 3 K := by
  intro E hE hEc hnot
  rcases CFSG.RankThree.PartTwo.KFacts.ks18L34Gen K
      (KFactProofs.UPrimeExcL34.nonempty_equiv_projSL hK) E hE (by rw [hEc]; norm_num) with h | h
  · exact h
  · exact absurd h hnot

end CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.I2316
