module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakRes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieChar
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporCore
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanAlphaThreeWeakSpor
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0ThreeKill
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeData
import CFSG.RankThree.PartOne.KFOUT3.SLCard
import CFSG.RankThree.PartOne.K133B.NC5Cover
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbedding.KFactProofs.ThreeWeak (WeakGenU43 WeakGenO73 WeakGenG23)
open CFSG.RankThree.PartTwo.Sec4.Census (tripleCoverLie_of_griess)
open CFSG.RankThree.PartOne.N143 (PrimeCoverLieIndex primeCoverLie_of_griess)

private theorem not_dvd_pow_sub_one {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : ¬ p ∣ p ^ n - 1 := by
  intro h
  have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.pos
  have hq : p ∣ (p ^ n - 1) + 1 := by rw [Nat.sub_add_cancel h1]; exact dvd_pow_self p hn
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp hq))

private theorem not_dvd_pow_add_one {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : ¬ p ∣ p ^ n + 1 := by
  intro h
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_pow_self p hn)).mp h))

private theorem not_dvd_card_sub_one {q : TauCeti.PrimePower} {p : ℕ} (hqp : q.p = p) :
    ¬ p ∣ q.card - 1 := by
  rw [TauCeti.PrimePower.card_def, hqp]
  exact not_dvd_pow_sub_one (hqp ▸ q.prime_p) q.exponent_pos.ne'

private theorem not_dvd_card_add_one {q : TauCeti.PrimePower} {p : ℕ} (hqp : q.p = p) :
    ¬ p ∣ q.card + 1 := by
  rw [TauCeti.PrimePower.card_def, hqp]
  exact not_dvd_pow_add_one (hqp ▸ q.prime_p) q.exponent_pos.ne'

theorem p1ThreeLieList_of_rankOne {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hchar : p = d.1.characteristic) (hr : IsRankOneLieIndex d.1) : P1ThreeLieList p d := by
  rcases hr with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨m, hm⟩
  · have hqp : q.p = p := by
      rw [hq] at hchar
      simpa using hchar.symm
    exact Or.inl ⟨q.exponent, q, hq, hqp, rfl⟩
  · have hqp : q.p = p := by
      rw [hq] at hchar
      simpa using hchar.symm
    exact Or.inr (Or.inl ⟨q, hqp, hq⟩)
  · have hp3 : p = 3 := by
      rw [hm] at hchar
      simpa using hchar
    exact Or.inr (Or.inr (Or.inl ⟨hp3, m, hm⟩))

theorem exceptional_of_center_ne_bot {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hGA : GriessMultipliersAllModels) {K : Type} [Group K] [Finite K]
    (hq : Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup p (Subgroup.center K)) {d : TauCeti.ValidLieTypeIndex}
    (hchar : p = d.1.characteristic)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    p = 3 ∧ ((∃ q : TauCeti.PrimePower, d.1 = .twistedA 3 q ∧ q.card = 3) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .B 3 q ∧ q.card = 3) ∨
      ∃ q : TauCeti.PrimePower, d.1 = .G2 q ∧ q.card = 3) := by
  have hp : p.Prime := Fact.out
  have hq' : CFSG.IsQuasisimple K := KFactProofs.CoverFive.isQuasisimple_of_open hq
  have hpZ : p ∣ Nat.card (Subgroup.center K) :=
    KFactProofs.CoverFive.dvd_card_center_of_isPGroup hp hZ hZp
  obtain ⟨dd, hv⟩ := d
  by_cases h3 : p = 3
  · subst h3
    refine ⟨rfl, ?_⟩
    have hidx := tripleCoverLie_of_griess hGA ⟨dd, hv⟩ K ⟨hq', hpZ, ⟨e⟩⟩
    cases dd with
    | A r q =>
      exact absurd hidx.2 (not_dvd_card_sub_one (by simpa using hchar.symm))
    | twistedA r q =>
      rcases hidx with hid | ⟨rfl, hq3⟩
      · exact absurd hid.2 (not_dvd_card_add_one (by simpa using hchar.symm))
      · exact Or.inl ⟨q, rfl, hq3⟩
    | B r q =>
      obtain ⟨rfl, hq3⟩ := hidx
      exact Or.inr (Or.inl ⟨q, rfl, hq3⟩)
    | G2 q => exact Or.inr (Or.inr ⟨q, rfl, hidx⟩)
    | E6 q => exact absurd hidx (not_dvd_card_sub_one (by simpa using hchar.symm))
    | twistedE6 q => exact absurd hidx (not_dvd_card_add_one (by simpa using hchar.symm))
    | C r q => exact hidx.elim
    | D r q => exact hidx.elim
    | twistedD r q => exact hidx.elim
    | E7 q => exact hidx.elim
    | E8 q => exact hidx.elim
    | F4 q => exact hidx.elim
    | trialityD4 q => exact hidx.elim
    | suzuki m => exact hidx.elim
    | reeG2 m => exact hidx.elim
    | reeF4 m => exact hidx.elim
    | tits => exact hidx.elim
  · exfalso
    have hidx : PrimeCoverLieIndex p dd := by
      by_cases h5 : p = 5
      · subst h5
        exact CFSG.RankThree.PartOne.K133B.primeCoverLie_five hGA ⟨dd, hv⟩ hq' e hpZ
      · have h7 : 7 ≤ p := by
          have h2 := hp.two_le
          by_contra hlt
          have h4 : p ≠ 4 := by
            rintro rfl
            exact absurd hp (by norm_num)
          have h6 : p ≠ 6 := by
            rintro rfl
            exact absurd hp (by norm_num)
          omega
        exact primeCoverLie_of_griess hGA hp h7 ⟨dd, hv⟩ hq' e hpZ
    cases dd with
    | A r q => exact not_dvd_card_sub_one (by simpa using hchar.symm) hidx.2
    | twistedA r q => exact not_dvd_card_add_one (by simpa using hchar.symm) hidx.2
    | B r q => exact hidx.elim
    | C r q => exact hidx.elim
    | D r q => exact hidx.elim
    | twistedD r q => exact hidx.elim
    | E6 q => exact hidx.elim
    | E7 q => exact hidx.elim
    | E8 q => exact hidx.elim
    | F4 q => exact hidx.elim
    | G2 q => exact hidx.elim
    | twistedE6 q => exact hidx.elim
    | trialityD4 q => exact hidx.elim
    | suzuki m => exact hidx.elim
    | reeG2 m => exact hidx.elim
    | reeF4 m => exact hidx.elim
    | tits => exact hidx.elim

theorem weakCore_eq_top_of_center_ne_bot {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hGA : GriessMultipliersAllModels) (hU43 : WeakGenU43) (hO73 : WeakGenO73)
    (hG23 : WeakGenG23) {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥) (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) {d : TauCeti.ValidLieTypeIndex}
    (hchar : p = d.1.characteristic)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) (T : Sylow p K) :
    GLBWeakCore p (T : Subgroup K) = ⊤ := by
  obtain ⟨hp3, hshape⟩ := exceptional_of_center_ne_bot hp2 hGA hq hZ hZp hchar e
  subst hp3
  obtain ⟨dd, hv⟩ := d
  rcases hshape with ⟨q, hdq, hq3⟩ | ⟨q, hdq, hq3⟩ | ⟨q, hdq, hq3⟩
  · simp only at hdq
    subst hdq
    exact (KFactProofs.ThreeWeak.weakCore_rank_of_coverWeakGen hq hZ hZp hZc e
      (hU43 q hv hq3) T).1
  · simp only at hdq
    subst hdq
    exact (KFactProofs.ThreeWeak.weakCore_rank_of_coverWeakGen hq hZ hZp hZc e
      (hO73 q hv hq3) T).1
  · simp only at hdq
    subst hdq
    exact (KFactProofs.ThreeWeak.weakCore_rank_of_coverWeakGen hq hZ hZp hZc e
      (hG23 q hv hq3) T).1

theorem weakCore_eq_top_of_charP {p : ℕ} [Fact p.Prime] {Fam : TauCeti.ValidLieTypeIndex → Prop}
    (hweak : WeakCharPGenAt Fam) (hGA : GriessMultipliersAllModels) (hU43 : WeakGenU43)
    (hO73 : WeakGenO73) (hG23 : WeakGenG23) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hq : Open.IsQuasisimple K) (hZp : IsPGroup p (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K)) {d : TauCeti.ValidLieTypeIndex} (hFam : Fam d)
    (hchar : p = d.1.characteristic) (hrank : ¬ IsRankOneLieIndex d.1)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) (T : Sylow p K) :
    GLBWeakCore p (T : Subgroup K) = ⊤ := by
  by_cases hZ : Subgroup.center K = ⊥
  · have e₀ : K ⧸ Subgroup.center K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
    have hsimple : IsSimpleGroup K := e₀.symm.isSimpleGroup
    have hnab : ∃ a b : K, a * b ≠ b * a := by
      by_contra hcomm
      push Not at hcomm
      obtain ⟨a, b, hab⟩ :=
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm a' b'])
    exact hweak K hsimple hnab d hFam ⟨e₀.symm.trans e⟩ p Fact.out hp2 hchar hrank T
  · exact weakCore_eq_top_of_center_ne_bot hp2 hGA hU43 hO73 hG23 hq hZ hZp hZc hchar e T

theorem nonempty_mulEquiv_psl_three {p : ℕ} [Fact p.Prime] {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q) :
    Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p 1)) := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hqp, hq1, hdq⟩ := hd
  obtain ⟨qp, qe, hqprime, hqpos⟩ := q
  simp only at hqp hq1 hdq
  subst hqp hq1
  subst hdq
  exact ⟨CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 ⟨qp, 1, hqprime, hqpos⟩ hv⟩

theorem not_pow_four_dvd_card_psl_three {p : ℕ} [Fact p.Prime] :
    ¬ p ^ 4 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p 1)) := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card (GaloisField p 1) = p := by
    simpa using GaloisField.card p 1 one_ne_zero
  have h1 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField p 1)) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField p 1)) :=
    Subgroup.card_quotient_dvd_card _
  rw [CFSG.RankThree.PartOne.KFOUT3.card_SL3_eq, hcard] at h1
  intro h4
  have h2 : p ^ 3 * p ∣ p ^ 3 * ((p ^ 3 - 1) * (p ^ 2 - 1)) := by
    have e : p ^ 3 * ((p ^ 3 - 1) * (p ^ 2 - 1)) = (p ^ 3 - 1) * p ^ 3 * (p ^ 2 - 1) := by ring
    rw [e, ← pow_succ]
    exact h4.trans h1
  have h3 : p ∣ (p ^ 3 - 1) * (p ^ 2 - 1) :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 3) h2
  rcases hp.dvd_mul.mp h3 with h | h
  · exact not_dvd_pow_sub_one hp (by norm_num) h
  · exact not_dvd_pow_sub_one hp (by norm_num) h

theorem caseThreeMid_of_noncomm {p : ℕ} [Fact p.Prime] {K X : Type} [Group K] [Finite K] [Group X]
    [Finite X] (f : K ≃* X) (hZ : Subgroup.center K = ⊥) (h4 : ¬ p ^ 4 ∣ Nat.card X)
    (hpair : RankThree.PartOne.StrongP.HasNoncommPair p X) : CaseThreeMid p K := fun T =>
  ⟨pRank_sylow_le_two_of_mulEquiv Fact.out f (pRank_le_two_of_hasNoncommPair Fact.out h4 hpair) T,
    Or.inl hZ⟩

theorem false_of_linThree {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {Rb : Sylow p Y} {Y₀ : Subgroup Y} (h : ReducedNongeneration p Y Rb Y₀) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hOut : AGLEmbeddingD2.KFactLieCharOut) (hZ : Subgroup.center K = ⊥)
    {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ne_two
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨q, hqp, hq1, hdq⟩ := hd
  have hsmall : AGLEmbeddingD2.IsD2LieCharSmall p d.1 := ⟨q, hqp, Or.inr ⟨hq1, Or.inl hdq⟩⟩
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have : Finite (MulAut K) := MulEquiv.finite_left
  have hOutK : ¬ p ∣ Nat.card (Outer K) :=
    not_dvd_card_outer_of_quotient (hOut (K ⧸ Subgroup.center K) d ⟨e⟩ p hp hp2 hsmall)
  obtain ⟨b⟩ := nonempty_mulEquiv_psl_three (p := p) ⟨q, hqp, hq1, hdq⟩
  have e₀ : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hmid : CaseThreeMid p K :=
    caseThreeMid_of_noncomm (e₀.symm.trans (e.trans b)) hZ not_pow_four_dvd_card_psl_three
      (RankThree.PartOne.StrongP.hasNoncommPair_psl (K := GaloisField p 1) p 3 hp3 le_rfl)
  exact false_of_caseThreeMid h hK huniq hcent hOutK hmid

theorem p1ThreeLieCharP_of_weak {Fam : TauCeti.ValidLieTypeIndex → Prop}
    (hweak : WeakCharPGenAt Fam)
    (hfam : ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 →
      p = d.1.characteristic → ¬ IsRankOneLieIndex d.1 → ¬ IsSpFourIndex p d →
      ¬ (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q) → Fam d)
    (hGA : GriessMultipliersAllModels) (hU43 : WeakGenU43) (hO73 : WeakGenO73)
    (hG23 : WeakGenG23) (hOut : AGLEmbeddingD2.KFactLieCharOut) : P1ThreeLieCharP := by
  intro p _ Y _ _ Rb Y₀ h _ K hK huniq _ hcent d ⟨e⟩ hchar
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ne_two
  by_contra hlist
  have hrank : ¬ IsRankOneLieIndex d.1 := fun hr => hlist (p1ThreeLieList_of_rankOne hchar hr)
  have hB2 : ¬ IsSpFourIndex p d := fun hB => hlist (Or.inr (Or.inr (Or.inr (Or.inl hB))))
  have hZp : IsPGroup p (Subgroup.center K) :=
    isPGroup_center_of_isComponentOf hp h.core_eq_bot hK
  by_cases hL3 : ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q
  · have hZ : Subgroup.center K = ⊥ := by
      by_contra hZ
      obtain ⟨-, hshape⟩ := exceptional_of_center_ne_bot hp2 hGA hK.2.2 hZ hZp hchar e
      obtain ⟨q, -, -, hdq⟩ := hL3
      rcases hshape with ⟨q', h', -⟩ | ⟨q', h', -⟩ | ⟨q', h', -⟩ <;> rw [hdq] at h' <;>
        cases h'
    exact false_of_linThree h hK huniq hcent hOut hZ hL3 e
  · exact h.false_of_weakCore_eq_top hK huniq fun T =>
      weakCore_eq_top_of_charP hweak hGA hU43 hO73 hG23 hp2 hK.2.2 hZp
        (h.isCyclic_center_of_unique hK huniq) (hfam d p hp hp2 hchar hrank hB2 hL3) hchar hrank
        e T

end CFSG.AGLEmbedding
