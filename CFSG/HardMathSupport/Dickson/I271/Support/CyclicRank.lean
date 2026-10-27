module

public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicData
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Assembly.LowTwoRank TauCeti

section Classical

theorem classical_rankOne {G : Type} [Group G] [Finite G] {t : StatedLieTag} {n p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel G t n p f)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 1) :
    t = .PSL ∧ n = 2 ∧ 5 ≤ p ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
      Nonempty (G ≃* StatedProj (StatedSL 2 F)) := by
  obtain ⟨hp, hf, hr⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  rcases hr with ⟨ht, ⟨hn, hfr⟩ | ⟨hn, hfr⟩ | h4⟩ | ⟨ht, ⟨hn, hfr⟩ | h4⟩ | ⟨ht, ⟨hn, hfr⟩ | h4⟩ | h4
  · have hf1 : f = 1 := by omega
    subst ht hn hf1
    obtain ⟨⟨-, -, -, -, hne3⟩, K, _, _, hK, ⟨e⟩⟩ := h
    refine ⟨rfl, rfl, ?_, K, inferInstance, inferInstance, by rwa [pow_one] at hK, ⟨e⟩⟩
    have h2 := hp.two_le
    have h3 : p ≠ 3 := by
      rintro rfl
      exact hne3 (by simp)
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  all_goals omega

end Classical

section Exceptional

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge


theorem untwisted_two_le_pRank {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : UntwistedBridge τ c) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (q : PrimePower) (hv : (c q).Valid) (hq : q.p ≠ 2) {S : Type} [Group S] [Finite S]
    (e : S ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    2 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup S) := by
  have hm := untwistedModel_of_bridge hB q hv hq e
  have hf := q.exponent_pos
  rcases hτ with rfl | h
  · have := CFSG.SectionRank.three_mul_le_pRank_of_G2Model hm
    omega
  · have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel h hm
    omega

theorem twistedE6_two_le_pRank (hB : TwistedBridge .E6 LieTypeIndex.twistedE6)
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) (hq : q.p ≠ 2) {S : Type} [Group S]
    [Finite S] (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    2 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup S) := by
  have hm := twistedModel_of_bridge hB q hv hq (by decide) e
  have := CFSG.SectionRank.four_le_pRank_of_twistedE6Model q.exponent_pos hm
  omega

theorem trialityD4_two_le_pRank (hB : TwistedBridge .D4 LieTypeIndex.trialityD4)
    (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid) (hq : q.p ≠ 2) {S : Type} [Group S]
    [Finite S] (e : S ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    2 ≤ CFSG.Open.pRank q.p (⊤ : Subgroup S) := by
  have hm := twistedModel_of_bridge hB q hv hq (by decide) e
  have := CFSG.SectionRank.four_le_pRank_of_trialityD4Model q.exponent_pos hm
  omega

theorem reeG2_two_le_pRank (hB : ReeG2Bridge) (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid)
    {S : Type} [Group S] [Finite S] (e : S ≃* ValidLieTypeIndex.Group ⟨.reeG2 m, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hm1 : 1 ≤ m := hrange
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, -, hK⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 3),
      Nat.card K = 3 ^ (2 * m + 1) :=
    ⟨GaloisField 3 (2 * m + 1), inferInstance, inferInstance, inferInstance,
      GaloisField.card 3 (2 * m + 1) (by omega)⟩
  obtain ⟨b⟩ := hB m hv K hK
  have hmodel : ReeTitsModel S .twistedG2 3 (2 * m + 1) :=
    ⟨⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩, m, rfl, K, inferInstance,
      inferInstance, hK, ⟨e.trans b.symm⟩⟩
  obtain ⟨-, -, hr⟩ := CFSG.SectionRank.smallReeModel_rank hmodel
  omega

theorem kdRankOne_of_bridges (hB : ChevalleyBridges) (hR : ReeG2Bridge) : KDRankOne := by
  intro p hp hp2 S _ _ hS hnc ⟨idx, ⟨e⟩, hchar⟩ hrk
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hv⟩ := idx
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    obtain ⟨-, hc | ⟨hn, -⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA r q hv
    · obtain ⟨-, -, h5, F, hF, hFin, hFc, ⟨e'⟩⟩ :=
        classical_rankOne hp2 (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hc) hrk
      exact ⟨h5, F, hF, hFin, hFc, ⟨e'⟩⟩
    · omega
  | twistedA r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    exact absurd (classical_rankOne hp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e) hrk).1 (by decide)
  | B r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have hr2 : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact absurd (classical_rankOne hp2
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hrk).1 (by decide)
    · exact absurd (classical_rankOne hp2
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr3 e) hrk).1
        (by decide)
  | C r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    exact absurd (classical_rankOne hp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e) hrk).1 (by decide)
  | D r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    exact absurd (classical_rankOne hp2
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e) hrk).1 (by decide)
  | twistedD r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    exact absurd (classical_rankOne hp2
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e) hrk).1
      (by decide)
  | E6 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.e6 (Or.inr (Or.inr (Or.inl rfl))) q hv hp2 e
    omega
  | E7 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.e7 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) q hv hp2 e
    omega
  | E8 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.e8 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) q hv hp2 e
    omega
  | F4 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.f4 (Or.inr (Or.inl rfl)) q hv hp2 e
    omega
  | G2 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.g2 (Or.inl rfl) q hv hp2 e
    omega
  | twistedE6 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := twistedE6_two_le_pRank hB.twistedE6 q hv hp2 e
    omega
  | trialityD4 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := trialityD4_two_le_pRank hB.trialityD4 q hv hp2 e
    omega
  | reeG2 m =>
    have hp3 : p = 3 := by simpa using hchar.symm
    subst hp3
    have := reeG2_two_le_pRank hR m hv e
    omega
  | suzuki m => exact (hp2 (by simpa using hchar.symm)).elim
  | reeF4 m => exact (hp2 (by simpa using hchar.symm)).elim
  | tits => exact (hp2 (by simpa using hchar.symm)).elim

end Exceptional

theorem kdRankOne_holds :
    KDRankOne :=
  kdRankOne_of_bridges CFSG.TauCetiBridge.chevalleyBridges CFSG.TauCetiBridge.reeG2Bridge

end CFSG.HardMathSupport.Dickson.I271
