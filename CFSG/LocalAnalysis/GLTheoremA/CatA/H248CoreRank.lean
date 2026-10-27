module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248CoreDefs
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.Adapters.LinearCatalogStated
import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.AGLEmbedding CFSG.Open CFSG.SectionRank TauCeti

private theorem four_le_pRank_of_classicalModel {K : Type} [Group K] [Finite K]
    {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (h : StatedClassicalModel K t n p f)
    (hL2 : t = .PSL → n = 2 → 4 ≤ f) (hL3 : t = .PSL → n = 3 → 2 ≤ f)
    (hU3 : t = .PSU → n = 3 → 2 ≤ f) (hSp : t = .PSp → n = 2 → 2 ≤ f) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  obtain ⟨-, -, h⟩ := classical_model_rank hp2 h
  rcases h with ⟨ht, ⟨hn, hr⟩ | ⟨hn, hr⟩ | hr⟩ | ⟨ht, ⟨hn, hr⟩ | hr⟩ |
    ⟨ht, ⟨hn, hr⟩ | hr⟩ | hr
  · have := hL2 ht hn; omega
  · have := hL3 ht hn; omega
  · exact hr
  · have := hU3 ht hn; omega
  · exact hr
  · have := hSp ht hn; omega
  · exact hr
  · exact hr

private theorem four_le_pRank_typeA {K : Type} [Group K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.A r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩)
    (hp2 : q.p ≠ 2) (h1 : ¬ IsRankOneLieIndex (.A r q))
    (hcore : ¬ IsCorePrimeIndex q.p (.A r q)) :
    4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) :=
  four_le_pRank_of_classicalModel hp2
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e)
    (fun _ hn => by
      obtain rfl : r = 1 := by omega
      exact absurd (Or.inl ⟨q, rfl⟩) h1)
    (fun _ hn => by
      obtain rfl : r = 2 := by omega
      by_contra h
      exact hcore ⟨q, rfl, by have := q.exponent_pos; omega, Or.inl rfl⟩)
    (fun h _ => nomatch h) (fun h _ => nomatch h)

private theorem four_le_pRank_typeTwistedA {K : Type} [Group K] [Finite K] {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : K ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) (hp2 : q.p ≠ 2)
    (h1 : ¬ IsRankOneLieIndex (.twistedA r q)) :
    4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) :=
  four_le_pRank_of_classicalModel hp2
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
    (fun h _ => nomatch h) (fun h _ => nomatch h)
    (fun _ hn => by
      obtain rfl : r = 2 := by omega
      exact absurd (Or.inr (Or.inl ⟨q, rfl⟩)) h1)
    (fun h _ => nomatch h)

private theorem four_le_pRank_typeB {K : Type} [Group K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.B r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩)
    (hp2 : q.p ≠ 2) (hcore : ¬ IsCorePrimeIndex q.p (.B r q)) :
    4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) := by
  rcases Nat.lt_or_ge r 3 with h2 | h3
  · obtain rfl : r = 2 := by
      have hr : 2 ≤ r :=
        ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
      omega
    refine four_le_pRank_of_classicalModel hp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
      (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h) ?_
    intro _ _
    by_contra h
    exact hcore ⟨q, rfl, by have := q.exponent_pos; omega, Or.inr (Or.inl rfl)⟩
  · exact four_le_pRank_of_classicalModel hp2
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 h3 e)
      (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h)
      (fun h _ => nomatch h)

private theorem four_le_pRank_typeC {K : Type} [Group K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.C r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩)
    (hp2 : q.p ≠ 2) : 4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) := by
  have h3 : 3 ≤ r :=
    ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  exact four_le_pRank_of_classicalModel hp2
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)
    (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h)
    (fun _ hn => by omega)

private theorem four_le_pRank_typeD {K : Type} [Group K] [Finite K] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.D r q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩)
    (hp2 : q.p ≠ 2) : 4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) :=
  four_le_pRank_of_classicalModel hp2
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)
    (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h)
    (fun h _ => nomatch h)

private theorem four_le_pRank_typeTwistedD {K : Type} [Group K] [Finite K] {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.twistedD r q).Valid)
    (e : K ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) (hp2 : q.p ≠ 2) :
    4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) :=
  four_le_pRank_of_classicalModel hp2
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)
    (fun h _ => nomatch h) (fun h _ => nomatch h) (fun h _ => nomatch h)
    (fun h _ => nomatch h)

section Exceptional


private theorem four_le_pRank_untwisted {K : Type} [Group K] [Finite K]
    {τ : CFSG.Blueprint.Chevalley.Tag} {c : PrimePower → LieTypeIndex}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hB : CFSG.TauCetiBridge.UntwistedBridge τ c) {q : PrimePower}
    (hv : (c q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) (hp2 : q.p ≠ 2) :
    4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have h := four_mul_le_pRank_of_untwistedModel hτ (p := q.p) (f := q.exponent)
    (CFSG.TauCetiBridge.untwistedModel_of_bridge hB q hv hp2 e)
  have := q.exponent_pos
  omega

private theorem four_le_pRank_G2 {K : Type} [Group K] [Finite K] {q : PrimePower}
    (hB : CFSG.TauCetiBridge.UntwistedBridge .G2 LieTypeIndex.G2)
    (hv : (LieTypeIndex.G2 q).Valid) (e : K ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩)
    (hp2 : q.p ≠ 2) (hf : 2 ≤ q.exponent) :
    4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have h := three_mul_le_pRank_of_G2Model (p := q.p) (f := q.exponent)
    (CFSG.TauCetiBridge.untwistedModel_of_bridge hB q hv hp2 e)
  omega

private theorem four_le_pRank_twistedE6 {K : Type} [Group K] [Finite K] {q : PrimePower}
    (hB : CFSG.TauCetiBridge.TwistedBridge .E6 LieTypeIndex.twistedE6)
    (hv : (LieTypeIndex.twistedE6 q).Valid)
    (e : K ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) (hp2 : q.p ≠ 2) :
    4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  exact four_le_pRank_of_twistedE6Model (p := q.p) (f := q.exponent) q.exponent_pos
    (CFSG.TauCetiBridge.twistedModel_of_bridge hB q hv hp2 (by decide) e)

private theorem four_le_pRank_trialityD4 {K : Type} [Group K] [Finite K] {q : PrimePower}
    (hB : CFSG.TauCetiBridge.TwistedBridge .D4 LieTypeIndex.trialityD4)
    (hv : (LieTypeIndex.trialityD4 q).Valid)
    (e : K ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hp2 : q.p ≠ 2) :
    4 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  exact four_le_pRank_of_trialityD4Model (p := q.p) (f := q.exponent) q.exponent_pos
    (CFSG.TauCetiBridge.twistedModel_of_bridge hB q hv hp2 (by decide) e)

theorem coreRankFour_holds : CoreRankFour := by
  intro K _ _ d ⟨e⟩ p hp2 hpc hrank1 hcore
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_typeA hv e hp2 hrank1 hcore
  | twistedA r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_typeTwistedA hv e hp2 hrank1
  | B r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_typeB hv e hp2 hcore
  | C r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_typeC hv e hp2
  | D r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_typeD hv e hp2
  | twistedD r q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_typeTwistedD hv e hp2
  | G2 q =>
    obtain rfl : p = q.p := by simpa using hpc
    refine four_le_pRank_G2 CFSG.TauCetiBridge.chevalleyBridges.g2 hv e hp2 ?_
    by_contra h
    exact hcore ⟨q, rfl, by have := q.exponent_pos; omega, Or.inr (Or.inr rfl)⟩
  | F4 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_untwisted (τ := .F4) (c := LieTypeIndex.F4) (by simp)
      CFSG.TauCetiBridge.chevalleyBridges.f4 hv e hp2
  | E6 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_untwisted (τ := .E6) (c := LieTypeIndex.E6) (by simp)
      CFSG.TauCetiBridge.chevalleyBridges.e6 hv e hp2
  | E7 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_untwisted (τ := .E7) (c := LieTypeIndex.E7) (by simp)
      CFSG.TauCetiBridge.chevalleyBridges.e7 hv e hp2
  | E8 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_untwisted (τ := .E8) (c := LieTypeIndex.E8) (by simp)
      CFSG.TauCetiBridge.chevalleyBridges.e8 hv e hp2
  | twistedE6 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_twistedE6 CFSG.TauCetiBridge.chevalleyBridges.twistedE6 hv e hp2
  | trialityD4 q =>
    obtain rfl : p = q.p := by simpa using hpc
    exact four_le_pRank_trialityD4 CFSG.TauCetiBridge.chevalleyBridges.trialityD4 hv e hp2
  | reeG2 m =>
    exact absurd (Or.inr (Or.inr ⟨m, rfl⟩)) hrank1
  | suzuki m => exact absurd (by simpa using hpc) hp2
  | reeF4 m => exact absurd (by simpa using hpc) hp2
  | tits => exact absurd (by simpa using hpc) hp2

end Exceptional

end CFSG.LocalAnalysis.GLTheoremA.H248
