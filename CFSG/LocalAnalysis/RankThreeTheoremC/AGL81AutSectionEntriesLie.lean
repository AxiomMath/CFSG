module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionEntriesCriteria
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
import CFSG.RankThree.PartOne.CTP.StrongPCharPFinal
import CFSG.RankThree.PartOne.K159.AutL2
import CFSG.RankThree.PartOne.K159.AutA10

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

theorem not_smallAutomizer_linTwo {p : ℕ} (hp5 : 5 ≤ p) {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.p = p) (h2 : 2 ≤ q.exponent) (hd : d.1 = .A 1 q)
    {K : Type} [Group K] [Finite K] (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ¬ SmallAutomizer p K := by
  subst hq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨b⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (p := q.p) (n := q.exponent) ⟨q, hd, rfl, rfl⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hle : q.p ^ 2 ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos h2
  have h25 : 5 ^ 2 ≤ q.p ^ 2 := Nat.pow_le_pow_left hp5 2
  have hW := CFSG.RankThree.PartOne.K159.autWitness_psl_two (K := GaloisField q.p q.exponent)
    (p := q.p) (by rw [hcard]; exact hle) (by rw [hcard]; omega)
  exact not_smallAutomizer_of_autWitness (hW.of_mulEquiv (e.trans b).symm)

theorem not_smallAutomizer_unitary {p : ℕ} (hp5 : 5 ≤ p) {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.p = p) (hd : d.1 = .twistedA 2 q) {K : Type} [Group K]
    [Finite K] (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : ¬ SmallAutomizer p K := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .twistedA 2 q := hd
  exact not_smallAutomizer_of_hasNoncommPair
    (CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_isoLie_twistedA hp5 (Or.inl rfl) hq
      ⟨hv, ⟨e⟩⟩)

theorem not_smallAutomizer_spFour {p : ℕ} (hp5 : 5 ≤ p) {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsSpFourIndex p d) {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : ¬ SmallAutomizer p K := by
  obtain ⟨x, hv⟩ := d
  obtain ⟨q, ⟨hq, -, hdq⟩ | ⟨rfl, -⟩⟩ := hd
  · simp only at hdq
    subst hdq
    exact not_smallAutomizer_of_hasNoncommPair
      (CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_isoLie_B2 hp5 hq ⟨hv, ⟨e⟩⟩)
  · omega

theorem not_smallAutomizer_linThree {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = p)
    (hd : d.1 = .A 2 q) {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : ¬ SmallAutomizer p K := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .A 2 q := hd
  exact not_smallAutomizer_of_hasNoncommPair
    (CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_isoLie_A hp5 le_rfl hq ⟨hv, ⟨e⟩⟩)

theorem not_smallAutomizer_altTen {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 10)) : ¬ SmallAutomizer 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact not_smallAutomizer_of_autWitness
    (CFSG.RankThree.PartOne.K159.autWitness_alternating_ten.of_mulEquiv e.symm)

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
