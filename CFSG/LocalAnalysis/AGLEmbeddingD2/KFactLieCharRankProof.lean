module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieChar
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.Adapters.TauCetiExceptional.B1Exceptional
import CFSG.Adapters.LinearCatalogStated
public import CFSG.Blueprint.Chevalley
import CFSG.Adapters.TauCetiExceptional.ReeBridge

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Assembly.LowTwoRank TauCeti CFSG.SectionRank

private theorem three_le_pRank_of_classicalModel {K : Type} [Group K] [Finite K]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (h : StatedClassicalModel K t n p f)
    (hL2 : t = .PSL → n = 2 → 3 ≤ f) (hL3 : t = .PSL → n = 3 → 2 ≤ f)
    (hU3 : t = .PSU → n = 3 → 2 ≤ f) : 3 ≤ Open.pRank p (⊤ : Subgroup K) := by
  obtain ⟨-, hf, h⟩ := classical_model_rank hp2 h
  rcases h with ⟨ht, ⟨hn, hr⟩ | ⟨hn, hr⟩ | hr⟩ | ⟨ht, ⟨hn, hr⟩ | hr⟩ | ⟨ht, ⟨hn, hr⟩ | hr⟩ | hr
  · have := hL2 ht hn; omega
  · have := hL3 ht hn; omega
  · omega
  · have := hU3 ht hn; omega
  · omega
  · omega
  · omega
  · omega

private theorem statedClassicalModel_typeA {K : Type} [Group K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    StatedClassicalModel K .PSL (r + 1) q.p q.exponent :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e

private theorem three_le_pRank_typeA {K : Type} [Group K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩)
    (hp2 : q.p ≠ 2) (hsmall : ¬ IsD2LieCharSmall q.p (.A r q)) :
    3 ≤ Open.pRank q.p (⊤ : Subgroup K) :=
  three_le_pRank_of_classicalModel hp2 (statedClassicalModel_typeA hv e)
    (fun _ hn => by
      obtain rfl : r = 1 := by omega
      by_contra h
      exact hsmall ⟨q, rfl, Or.inl ⟨by omega, rfl⟩⟩)
    (fun _ hn => by
      obtain rfl : r = 2 := by omega
      by_contra h
      exact hsmall ⟨q, rfl, Or.inr ⟨by have := q.exponent_pos; omega, Or.inl rfl⟩⟩)
    (fun h _ => nomatch h)

private theorem three_le_pRank_typeTwistedA {K : Type} [Group K] [Finite K] {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : K ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) (hp2 : q.p ≠ 2)
    (hsmall : ¬ IsD2LieCharSmall q.p (.twistedA r q)) :
    3 ≤ Open.pRank q.p (⊤ : Subgroup K) :=
  three_le_pRank_of_classicalModel hp2
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
    (fun h _ => nomatch h) (fun h _ => nomatch h)
    (fun _ hn => by
      obtain rfl : r = 2 := by omega
      by_contra h
      exact hsmall ⟨q, rfl, Or.inr ⟨by have := q.exponent_pos; omega, Or.inr rfl⟩⟩)

private theorem three_le_pRank_typeB {K : Type} [Group K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.B r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩)
    (hp2 : q.p ≠ 2) : 3 ≤ Open.pRank q.p (⊤ : Subgroup K) := by
  have hr : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  rcases Nat.lt_or_ge r 3 with h2 | h3
  · obtain rfl : r = 2 := by omega
    exact three_le_pRank_of_classicalModel hp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
      (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h)
  · exact three_le_pRank_of_classicalModel hp2
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 h3 e)
      (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h)

private theorem three_le_pRank_typeC {K : Type} [Group K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.C r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩)
    (hp2 : q.p ≠ 2) : 3 ≤ Open.pRank q.p (⊤ : Subgroup K) :=
  three_le_pRank_of_classicalModel hp2
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)
    (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h)

private theorem three_le_pRank_typeD {K : Type} [Group K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.D r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩)
    (hp2 : q.p ≠ 2) : 3 ≤ Open.pRank q.p (⊤ : Subgroup K) :=
  three_le_pRank_of_classicalModel hp2
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
    (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h)

private theorem three_le_pRank_typeTwistedD {K : Type} [Group K] [Finite K] {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.twistedD r q).Valid)
    (e : K ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) (hp2 : q.p ≠ 2) :
    3 ≤ Open.pRank q.p (⊤ : Subgroup K) :=
  three_le_pRank_of_classicalModel hp2
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
    (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h)

section Exceptional


private theorem three_le_pRank_untwisted {K : Type} [Group K] [Finite K]
    {τ : CFSG.Blueprint.Chevalley.Tag} {c : PrimePower → LieTypeIndex}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hB : CFSG.TauCetiBridge.UntwistedBridge τ c)
    {q : PrimePower} (hv : (c q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩)
    (hp2 : q.p ≠ 2) : 3 ≤ Open.pRank q.p (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have h := four_mul_le_pRank_of_untwistedModel hτ (p := q.p) (f := q.exponent)
    (CFSG.TauCetiBridge.untwistedModel_of_bridge hB q hv hp2 e)
  have := q.exponent_pos
  omega

private theorem three_le_pRank_G2 {K : Type} [Group K] [Finite K] {q : PrimePower}
    (hv : (LieTypeIndex.G2 q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩)
    (hp2 : q.p ≠ 2) : 3 ≤ Open.pRank q.p (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have h := three_mul_le_pRank_of_G2Model (p := q.p) (f := q.exponent)
    (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hp2 e)
  have := q.exponent_pos
  omega

private theorem three_le_pRank_twistedE6 {K : Type} [Group K] [Finite K] {q : PrimePower}
    (hv : (LieTypeIndex.twistedE6 q).Valid)
    (e : K ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) (hp2 : q.p ≠ 2) :
    3 ≤ Open.pRank q.p (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have h := four_le_pRank_of_twistedE6Model (p := q.p) (f := q.exponent) q.exponent_pos
    (CFSG.TauCetiBridge.twistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.twistedE6 q hv
      hp2 (by decide) e)
  omega

private theorem three_le_pRank_trialityD4 {K : Type} [Group K] [Finite K] {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid)
    (e : K ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hp2 : q.p ≠ 2) :
    3 ≤ Open.pRank q.p (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have h := four_le_pRank_of_trialityD4Model (p := q.p) (f := q.exponent) q.exponent_pos
    (CFSG.TauCetiBridge.twistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv
      hp2 (by decide) e)
  omega

private theorem three_le_pRank_reeG2 {K : Type} [Group K] [Finite K] {m : ℕ}
    (hv : (LieTypeIndex.reeG2 m).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.reeG2 m, hv⟩) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have ha : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa [LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have hmod : CFSG.Blueprint.ReeTitsModel K .twistedG2 3 (2 * m + 1) :=
    ⟨⟨Nat.prime_three, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
      ⟨GaloisField 3 (2 * m + 1), inferInstance, inferInstance, hK, ⟨e.trans φ.symm⟩⟩⟩
  have h := (smallReeModel_rank hmod).2.2
  omega

theorem kFactLieCharRank : KFactLieCharRank := by
  intro K _ _ d ⟨e⟩ p hp hp2 hpc hsmall
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_typeA hv e hp2 hsmall
  | twistedA r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_typeTwistedA hv e hp2 hsmall
  | B r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_typeB hv e hp2
  | C r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_typeC hv e hp2
  | D r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_typeD hv e hp2
  | twistedD r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_typeTwistedD hv e hp2
  | E6 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_untwisted (by simp) CFSG.TauCetiBridge.chevalleyBridges.e6 hv e hp2
  | E7 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_untwisted (by simp) CFSG.TauCetiBridge.chevalleyBridges.e7 hv e hp2
  | E8 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_untwisted (by simp) CFSG.TauCetiBridge.chevalleyBridges.e8 hv e hp2
  | F4 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_untwisted (by simp) CFSG.TauCetiBridge.chevalleyBridges.f4 hv e hp2
  | G2 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_G2 hv e hp2
  | twistedE6 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_twistedE6 hv e hp2
  | trialityD4 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact three_le_pRank_trialityD4 hv e hp2
  | reeG2 m =>
    obtain rfl : p = 3 := by simpa using hpc
    exact three_le_pRank_reeG2 hv e
  | suzuki m => exact absurd (by simpa using hpc) hp2
  | reeF4 m => exact absurd (by simpa using hpc) hp2
  | tits => exact absurd (by simpa using hpc) hp2

end Exceptional

end CFSG.AGLEmbeddingD2
