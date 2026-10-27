module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsSpecialQClassical
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsSpecialQExc
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsSpecialQTwisted
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

section Holds


private theorem exists_field_card (Q : PrimePower) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Q.card ∧ CharP K Q.p := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  exact ⟨GaloisField Q.p Q.exponent, inferInstance, inferInstance, by
    rw [GaloisField.card _ _ Q.exponent_pos.ne', PrimePower.card_def], inferInstance⟩

private theorem exists_field_pow (Q : PrimePower) (m : ℕ) (hm : m ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Q.card ^ m ∧
      ∃ σ : K →+* K, ∀ c, σ c = c ^ Q.card := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  refine ⟨GaloisField Q.p (Q.exponent * m), inferInstance, inferInstance, ?_,
    iterateFrobenius _ Q.p Q.exponent, fun c => ?_⟩
  · rw [GaloisField.card _ _ (Nat.mul_ne_zero Q.exponent_pos.ne' hm), pow_mul,
      PrimePower.card_def]
  · rw [iterateFrobenius_def, PrimePower.card_def]

theorem s2019ChevSpecialQ_holds : S2019ChevSpecialQ := by
  intro q hq hq2 Y _ _ d hcat hchar hA1 hree
  suffices h : HasS2019SpecialQ q d.fieldOrder Y from h.exists_subgroup
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d', hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d' = d at hi
  subst hi
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d' with
  | A r Q =>
    simp only [LieTypeIndex.characteristic_A, LieTypeIndex.fieldOrder_A] at hchar ⊢
    subst hchar
    have hr2 : 2 ≤ r := by
      by_contra h
      obtain rfl : r = 1 := by have := hrange.1; omega
      exact hA1 Q rfl
    have hT := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA r Q hv
    have hcl : StatedClassicalModel Y .PSL (r + 1) Q.p Q.exponent := by
      rcases hT.2 with h | ⟨h0, -⟩
      · exact CFSG.QuasithinUnique.Setup.Family.statedClassicalModel_of_mulEquiv e.symm h
      · omega
    rw [PrimePower.card_def]
    exact hasS2019SpecialQ_of_statedClassicalModel hcl hq2 fun _ => by omega
  | twistedA r Q =>
    simp only [LieTypeIndex.characteristic_twistedA, LieTypeIndex.fieldOrder_twistedA]
      at hchar ⊢
    subst hchar
    rw [PrimePower.card_def]
    exact hasS2019SpecialQ_of_statedClassicalModel
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r Q hv e) hq2 fun h => by cases h
  | B r Q =>
    simp only [LieTypeIndex.characteristic_B, LieTypeIndex.fieldOrder_B] at hchar ⊢
    subst hchar
    rw [PrimePower.card_def]
    rcases Nat.lt_or_ge r 3 with hr | hr
    · obtain rfl : r = 2 := by have := hrange.1; omega
      exact hasS2019SpecialQ_of_statedClassicalModel
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 Q hv e) hq2 fun h => by cases h
    · exact hasS2019SpecialQ_of_statedClassicalModel
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r Q hv hq2 hr e) hq2
        fun h => by cases h
  | C r Q =>
    simp only [LieTypeIndex.characteristic_C, LieTypeIndex.fieldOrder_C] at hchar ⊢
    subst hchar
    rw [PrimePower.card_def]
    exact hasS2019SpecialQ_of_statedClassicalModel
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r Q hv e) hq2 fun h => by cases h
  | D r Q =>
    simp only [LieTypeIndex.characteristic_D, LieTypeIndex.fieldOrder_D] at hchar ⊢
    subst hchar
    rw [PrimePower.card_def]
    exact hasS2019SpecialQ_of_statedClassicalModel
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r Q hv e) hq2 fun h => by cases h
  | twistedD r Q =>
    simp only [LieTypeIndex.characteristic_twistedD, LieTypeIndex.fieldOrder_twistedD]
      at hchar ⊢
    subst hchar
    rw [PrimePower.card_def]
    exact hasS2019SpecialQ_of_statedClassicalModel
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r Q hv e) hq2
      fun h => by cases h
  | G2 Q =>
    simp only [LieTypeIndex.characteristic_G2, LieTypeIndex.fieldOrder_G2] at hchar ⊢
    subst hchar
    obtain ⟨K, _, _, hK, _⟩ := exists_field_card Q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.g2 Q hv hq2 K hK
    rw [← hK]
    exact (hasS2019SpecialQ_adjointQuotient (Or.inl rfl) hq hq2).of_mulEquiv (b.trans e.symm)
  | F4 Q =>
    simp only [LieTypeIndex.characteristic_F4, LieTypeIndex.fieldOrder_F4] at hchar ⊢
    subst hchar
    obtain ⟨K, _, _, hK, _⟩ := exists_field_card Q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.f4 Q hv hq2 K hK
    rw [← hK]
    exact (hasS2019SpecialQ_adjointQuotient (Or.inr (Or.inl rfl)) hq hq2).of_mulEquiv
      (b.trans e.symm)
  | E6 Q =>
    simp only [LieTypeIndex.characteristic_E6, LieTypeIndex.fieldOrder_E6] at hchar ⊢
    subst hchar
    obtain ⟨K, _, _, hK, _⟩ := exists_field_card Q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.e6 Q hv hq2 K hK
    rw [← hK]
    exact (hasS2019SpecialQ_adjointQuotient (Or.inr (Or.inr (Or.inl rfl))) hq hq2).of_mulEquiv
      (b.trans e.symm)
  | E7 Q =>
    simp only [LieTypeIndex.characteristic_E7, LieTypeIndex.fieldOrder_E7] at hchar ⊢
    subst hchar
    obtain ⟨K, _, _, hK, _⟩ := exists_field_card Q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.e7 Q hv hq2 K hK
    rw [← hK]
    exact (hasS2019SpecialQ_adjointQuotient (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hq
      hq2).of_mulEquiv (b.trans e.symm)
  | E8 Q =>
    simp only [LieTypeIndex.characteristic_E8, LieTypeIndex.fieldOrder_E8] at hchar ⊢
    subst hchar
    obtain ⟨K, _, _, hK, _⟩ := exists_field_card Q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.e8 Q hv hq2 K hK
    rw [← hK]
    exact (hasS2019SpecialQ_adjointQuotient (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hq
      hq2).of_mulEquiv (b.trans e.symm)
  | twistedE6 Q =>
    simp only [LieTypeIndex.characteristic_twistedE6, LieTypeIndex.fieldOrder_twistedE6]
      at hchar ⊢
    subst hchar
    obtain ⟨K, _, _, hK, σ, hσ⟩ := exists_field_pow Q TwistTag.E6.order (by decide)
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.twistedE6 Q hv hq2 K hK σ hσ
    rw [PrimePower.card_def] at hK hσ ⊢
    exact (hasS2019SpecialQ_twistedE6 hq hq2 Q.exponent_pos hK σ hσ).of_mulEquiv (b.trans e.symm)
  | trialityD4 Q =>
    simp only [LieTypeIndex.characteristic_trialityD4, LieTypeIndex.fieldOrder_trialityD4]
      at hchar ⊢
    subst hchar
    obtain ⟨K, _, _, hK, σ, hσ⟩ := exists_field_pow Q TwistTag.D4.order (by decide)
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.trialityD4 Q hv hq2 K hK σ hσ
    rw [PrimePower.card_def] at hK hσ ⊢
    exact (hasS2019SpecialQ_trialityD4 hq hq2 Q.exponent_pos hK σ hσ).of_mulEquiv
      (b.trans e.symm)
  | suzuki m =>
    have := hchar
    simp only [LieTypeIndex.characteristic_suzuki] at this
    omega
  | reeG2 m => exact absurd rfl (hree m)
  | reeF4 m =>
    have := hchar
    simp only [LieTypeIndex.characteristic_reeF4] at this
    omega
  | tits =>
    have := hchar
    simp only [LieTypeIndex.characteristic_tits] at this
    omega

end Holds

end CFSG.LocalAnalysis.GLTheoremA.S2019
