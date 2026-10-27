module

public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Blueprint TauCeti CFSG.Assembly.LowTwoRank CFSG.StandardType.ChevTwo

@[expose] def tagOf : LieTypeIndex → StatedLieTag
  | .A _ _ => .PSL
  | .twistedA _ _ => .PSU
  | .B _ _ => .PSp
  | .C _ _ => .PSp
  | .D _ _ => .POmegaPlus
  | .twistedD _ _ => .POmegaMinus
  | .E6 _ => .E6
  | .E7 _ => .E7
  | .E8 _ => .E8
  | .F4 _ => .F4
  | .G2 _ => .G2
  | .twistedE6 _ => .twistedE6
  | .trialityD4 _ => .trialityD4
  | .suzuki _ => .twistedB2
  | .reeG2 _ => .twistedG2
  | .reeF4 _ => .twistedF4
  | .tits => .Tits

@[expose] def dimOf : LieTypeIndex → ℕ
  | .A r _ => r + 1
  | .twistedA r _ => r + 1
  | .B r _ => r
  | .C r _ => r
  | .D r _ => r
  | .twistedD r _ => r
  | _ => 0

@[expose] def TupleLemma : Prop :=
  ∀ (S : Type) [Group S] (d : ValidLieTypeIndex), d.1.characteristic = 2 → (S ≃* d.Group) →
    LieModel S (tagOf d.1) (dimOf d.1) 2 d.1.fieldExponent

@[expose] def ValT (t : StatedLieTag) (n f : ℕ) : Prop :=
  (t = .PSL → n = 2 → 3 ≤ f) ∧ (t = .PSL → n = 3 → 2 ≤ f) ∧ (t = .PSL → n = 4 → 2 ≤ f)

section Certs


theorem tupleLemma_holds : TupleLemma := by
  intro S _ d hd e
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  obtain ⟨d, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_A r q hv e
    rw [hp] at h
    have h' := blueprintLieModel_of_modelsLieModel (t := .PSL) (by simp [classicalTags]) h
    simpa [tagOf, dimOf] using h'
  | twistedA r q =>
    have h := CFSG.Models.lieModel_twistedA r q hv e
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := hd
    rw [hc] at h
    have h' := blueprintLieModel_of_modelsLieModel (t := .PSU) (by simp [classicalTags]) h
    simpa [tagOf, dimOf, ValidLieTypeIndex.fieldExponent] using h'
  | B r q =>
    have hp : q.p = 2 := by simpa using hd
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · rw [hp] at h
      have h' := blueprintLieModel_of_modelsLieModel (t := .PSp) (by simp [classicalTags]) h
      simpa [tagOf, dimOf] using h'
    · rw [hp] at h
      exact absurd h.1.2.2.2 (by simp)
  | C r q =>
    have hp : q.p = 2 := by simpa using hd
    exact absurd hp hr.2
  | D r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_D r q hv e
    rw [hp] at h
    have h' := blueprintLieModel_of_modelsLieModel (t := .POmegaPlus) (by simp [classicalTags]) h
    simpa [tagOf, dimOf] using h'
  | twistedD r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_twistedD r q hv e
    rw [hp] at h
    have h' := blueprintLieModel_of_modelsLieModel (t := .POmegaMinus) (by simp [classicalTags]) h
    simpa [tagOf, dimOf] using h'
  | E6 q =>
    have hp : q.p = 2 := by simpa using hd
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_E6]
    exact .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.e6 q hv hp e⟩)
  | E7 q =>
    have hp : q.p = 2 := by simpa using hd
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_E7]
    exact .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.e7 q hv hp e⟩)
  | E8 q =>
    have hp : q.p = 2 := by simpa using hd
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_E8]
    exact .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.e8 q hv hp e⟩)
  | F4 q =>
    have hp : q.p = 2 := by simpa using hd
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_F4]
    exact .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩, untwistedChevalleyModel_of_bridge hB.f4 q hv hp e⟩)
  | G2 q =>
    have hp : q.p = 2 := by simpa using hd
    have h3 : 3 ≤ 2 ^ q.exponent := by
      have h3 : 3 ≤ q.card := hr
      rwa [PrimePower.card_def, hp] at h3
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_G2]
    exact .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩, untwistedChevalleyModel_of_bridge hB.g2 q hv hp e⟩)
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hd
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_twistedE6]
    exact .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      twistedChevalleyModel_of_bridge hB.twistedE6 q hv hp e⟩)
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hd
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_trialityD4]
    exact .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp e⟩)
  | suzuki m =>
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_suzuki]
    exact .inr (.inr (.inr ⟨rfl, rfl, suzukiModel_of_valid m hv e⟩))
  | reeG2 m =>
    exact absurd hd (by simp)
  | reeF4 a =>
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_reeF4]
    exact .inr (.inr (.inl ⟨rfl, by simp [reeTitsTags], reeTitsModel_of_reeF4 a hv e⟩))
  | tits =>
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_tits]
    exact .inr (.inr (.inl ⟨rfl, by simp [reeTitsTags], reeTitsModel_of_tits hv e⟩))

end Certs

theorem valT_of_valid {d : LieTypeIndex} (hv : d.Valid) (hd : d.characteristic = 2) :
    ValT (tagOf d) (dimOf d) d.fieldExponent := by
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff] at hv
  obtain ⟨hr, hdup⟩ := hv
  cases d with
  | A r q =>
    have hp : q.p = 2 := by simpa using hd
    have hc : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have hf := q.exponent_pos
    simp only [tagOf, dimOf, LieTypeIndex.fieldExponent_A]
    refine ⟨fun _ hn => ?_, fun _ hn => ?_, fun _ hn => ?_⟩
    · obtain rfl : r = 1 := by omega
      by_contra hlt
      have : q.exponent = 1 ∨ q.exponent = 2 := by omega
      rcases this with h | h
      · have : 4 ≤ q.card := hr.2 rfl
        rw [hc, h] at this
        omega
      · apply hdup
        left
        refine ⟨rfl, Or.inl ?_⟩
        rw [hc, h]
        norm_num
    · obtain rfl : r = 2 := by omega
      by_contra hlt
      have h : q.exponent = 1 := by omega
      apply hdup
      right
      left
      refine ⟨rfl, ?_⟩
      rw [hc, h]
      norm_num
    · obtain rfl : r = 3 := by omega
      by_contra hlt
      have h : q.exponent = 1 := by omega
      apply hdup
      right
      right
      refine ⟨rfl, ?_⟩
      rw [hc, h]
      norm_num
  | twistedA r q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | B r q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | C r q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | D r q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | twistedD r q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | E6 q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | E7 q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | E8 q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | F4 q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | G2 q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | twistedE6 q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | trialityD4 q => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | suzuki m => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | reeG2 m => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | reeF4 m => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩
  | tits => exact ⟨by simp [tagOf], by simp [tagOf], by simp [tagOf]⟩

end CFSG.LocalAnalysis.GLTheoremA.HDesc
