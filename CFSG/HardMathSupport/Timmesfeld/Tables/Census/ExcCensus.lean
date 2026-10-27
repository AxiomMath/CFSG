module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Lie
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcUntwisted
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcTwisted
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcTits
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcLargeRee
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.LocalAnalysis.SectionRank.SmallRee
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LargeExtraspecial.Types
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.RankThree.PartTwo.Census.Exceptional.TrialityD4
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Timmesfeld.Outcome
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Chevalley CFSG.TauCetiBridge TauCeti

@[expose] def ExceptionalCovered (t : StatedLieTag) : Prop :=
  t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedG2 ∨ t = .twistedB2 ∨
    t = .twistedE6 ∨ t = .trialityD4 ∨ t = .Tits ∨ t = .twistedF4

@[expose] def ExceptionalLieCensusRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (p f : ℕ), LieModel X t 0 p f →
    ¬ ExceptionalCovered t → 3 ∣ Nat.card X →
      ThreeTwoWitness X ∨ 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)

theorem not_three_dvd_suzuki_order' (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  generalize q ^ 2 = q2 at hq2 ⊢
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h <;> omega
  · omega

section Helpers

theorem exists_field_card (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p), Nat.card K = p ^ f := by
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨GaloisField p f, inferInstance, inferInstance, inferInstance,
    GaloisField.card p f (by omega)⟩

end Helpers

theorem twistedChevalleyModel_of_bridge {t : TwistTag} {c : PrimePower → LieTypeIndex}
    (hB : Even.TwistedBridgeAll t c) {X : Type} [Group X] {q : PrimePower}
    {hv : (c q).Valid} (e : X ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    CFSG.Blueprint.TwistedChevalleyModel X t (q.p ^ q.exponent) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p (q.exponent * t.order)) = (q.p ^ q.exponent) ^ t.order := by
    rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos t.order_pos).ne', pow_mul]
  let σ : GaloisField q.p (q.exponent * t.order) →+* GaloisField q.p (q.exponent * t.order) :=
    iterateFrobenius _ q.p q.exponent
  have hσ : ∀ x, σ x = x ^ (q.p ^ q.exponent) := fun x => iterateFrobenius_def _ _ x
  obtain ⟨b⟩ := hB q hv _ (by rw [TauCeti.PrimePower.card_def]; exact hK) σ
    (by intro x; rw [TauCeti.PrimePower.card_def]; exact hσ x)
  exact ⟨_, inferInstance, inferInstance, hK, σ, hσ, ⟨e.trans b.symm⟩⟩

theorem threeTwoWitness_of_untwistedBridge
    {τ : Tag} {c : PrimePower → LieTypeIndex} (hB : Even.UntwistedBridgeAll τ c)
    (hr : 2 ≤ τ.rank) {X : Type} [Group X] {q : PrimePower} {hv : (c q).Valid}
    (e : X ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) : ThreeTwoWitness X := by
  obtain ⟨K, _, _, hchar, hK⟩ := exists_field_card q.p q.exponent q.prime_p q.exponent_pos
  obtain ⟨b⟩ := hB q hv K (by rw [hK, PrimePower.card_def])
  refine ThreeTwoWitness.of_mulEquiv (b.trans e.symm) ?_
  by_cases h2 : q.p = 2
  · have : CharP K 2 := h2 ▸ hchar
    exact threeTwoWitness_adjointQuotient_even hr
  · refine threeTwoWitness_adjointQuotient_odd ?_ (by omega)
    rw [ringChar.eq K q.p]
    exact h2

theorem exceptionalLieCensus_of_rest
    (hR : ExceptionalLieCensusRest) : ExceptionalLieCensus := by
  intro X _ _ t p f hm h3
  by_cases hcov : ExceptionalCovered t
  swap
  · exact hR X t p f hm hcov h3
  obtain ⟨hadm, hc | ⟨-, d, hnames, ⟨e⟩⟩⟩ := hm
  · exfalso
    rcases hcov with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hc.2.elim
  obtain ⟨idx, hv⟩ := d
  rcases hcov with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    cases idx <;> simp only [NamesTag] at hnames <;>
    exact Or.inl (threeTwoWitness_of_untwistedBridge (c := LieTypeIndex.G2)
      Even.chevalleyBridgesAll.g2 (by decide) e)
  ·
    cases idx <;> simp only [NamesTag] at hnames <;>
    exact Or.inl (threeTwoWitness_of_untwistedBridge (c := LieTypeIndex.F4)
      Even.chevalleyBridgesAll.f4 (by decide) e)
  ·
    cases idx <;> simp only [NamesTag] at hnames <;>
    exact Or.inl (threeTwoWitness_of_untwistedBridge (c := LieTypeIndex.E6)
      Even.chevalleyBridgesAll.e6 (by decide) e)
  ·
    cases idx <;> simp only [NamesTag] at hnames <;>
    exact Or.inl (threeTwoWitness_of_untwistedBridge (c := LieTypeIndex.E7)
      Even.chevalleyBridgesAll.e7 (by decide) e)
  ·
    cases idx <;> simp only [NamesTag] at hnames <;>
    exact Or.inl (threeTwoWitness_of_untwistedBridge (c := LieTypeIndex.E8)
      Even.chevalleyBridgesAll.e8 (by decide) e)
  ·
    cases idx <;> simp only [NamesTag] at hnames
    rename_i m
    obtain ⟨rfl, rfl⟩ := hnames
    obtain ⟨K, _, _, hchar, hK⟩ := exists_field_card 3 (2 * m + 1) Nat.prime_three (by omega)
    obtain ⟨b⟩ := reeG2Bridge m hv K hK
    have hmodel : CFSG.Blueprint.ReeTitsModel X .twistedG2 3 (2 * m + 1) :=
      ⟨hadm, m, rfl, K, inferInstance, inferInstance, hK, ⟨e.trans b.symm⟩⟩
    obtain ⟨-, h3f, hr⟩ := CFSG.SectionRank.smallReeModel_rank hmodel
    exact Or.inr (by omega)
  ·
    exfalso
    cases idx <;> simp only [NamesTag] at hnames
    rename_i m
    obtain ⟨rfl, rfl⟩ := hnames
    obtain ⟨K, _, _, hchar, hK⟩ := exists_field_card 2 (2 * m + 1) Nat.prime_two (by omega)
    have e₂ : ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩ ≃* CFSG.Blueprint.suzukiGroup m K :=
      (BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).trans
        (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).symm
    rw [Nat.card_congr (e.trans e₂).toEquiv, CFSG.LieType.Ree.suzuki_order hK] at h3
    exact not_three_dvd_suzuki_order' m h3
  ·
    cases idx <;> simp only [NamesTag] at hnames
    rename_i q
    obtain ⟨rfl, rfl⟩ := hnames
    by_cases hp2 : q.p = 2
    · have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hm := twistedChevalleyModel_of_bridge (t := .E6) (c := LieTypeIndex.twistedE6)
        Even.chevalleyBridgesAll.twistedE6 e
      rw [hp2] at hm
      exact Or.inr (le_trans (by norm_num)
        (CFSG.SectionRank.four_le_pRank_three_of_twistedE6Model_two q.exponent_pos hm))
    · exact Or.inl (threeTwoWitness_twistedE6_odd e hp2)
  ·
    cases idx <;> simp only [NamesTag] at hnames
    rename_i q
    obtain ⟨rfl, rfl⟩ := hnames
    by_cases hp2 : q.p = 2
    · exact Or.inl (threeTwoWitness_trialityD4_char2 e hp2)
    · exact Or.inl (threeTwoWitness_trialityD4 e (Or.inl hp2))
  ·
    cases idx <;> simp only [NamesTag] at hnames
    obtain ⟨e'⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1
      (reeTitsModel_tits_of_equiv e)
    exact Or.inl (ThreeTwoWitness.of_mulEquiv e'.symm threeTwoWitness_titsD)
  ·
    cases idx <;> simp only [NamesTag] at hnames
    rename_i m
    obtain ⟨rfl, rfl⟩ := hnames
    exact Or.inl (threeTwoWitness_largeRee_model (reeTitsModel_reeF4_of_equiv hadm e))

theorem exceptionalLieCensusRest_holds : ExceptionalLieCensusRest := by
  intro X _ _ t p f hm hcov
  exfalso
  obtain ⟨⟨-, -, hadm⟩, -⟩ := hm
  cases t
  iterate 4 exact absurd hadm.1 (by omega)
  iterate 2 exact absurd hadm (by omega)
  all_goals exact hcov (by simp [ExceptionalCovered])

theorem exceptionalLieCensus_holds
    : ExceptionalLieCensus :=
  exceptionalLieCensus_of_rest exceptionalLieCensusRest_holds

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
