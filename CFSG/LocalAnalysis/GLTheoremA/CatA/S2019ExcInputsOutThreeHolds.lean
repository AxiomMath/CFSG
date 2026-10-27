module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsOutThree
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
open CFSG.ComponentClassification.CatLeaf (lieSylowExponent)
open CFSG.ComponentClassification.CatLeafProof (lieOrderFormulasInput)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

section Holds


private theorem false_of_lieModel_three {Y : Type} [Group Y] {t : StatedLieTag} {n : ℕ}
    (hadm : StatedLieAdmissible t n 3 1) (hY : Blueprint.LieModel Y t n 3 1)
    (h3 : (Nat.card Y).factorization 3 ≤ 10) (hN : 10 < lieSylowExponent t n) : False := by
  obtain ⟨-, -, hfac⟩ := lieOrderFormulasInput Y t n 3 1 hadm hY
  rw [hfac, mul_one] at h3
  omega

private theorem false_of_classical_three {Y : Type} [Group Y] {t : StatedLieTag} {n : ℕ}
    (ht : t ∈ classicalTags) (hY : StatedClassicalModel Y t n 3 1)
    (h3 : (Nat.card Y).factorization 3 ≤ 10) (hN : 10 < lieSylowExponent t n) : False :=
  false_of_lieModel_three hY.1 (Or.inl ⟨ht, hY⟩) h3 hN

private theorem false_of_exceptional_three {Y : Type} [Group Y] {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) (hY : ChevalleyExceptionalModel Y t 3 1)
    (h3 : (Nat.card Y).factorization 3 ≤ 10) (hN : 10 < lieSylowExponent t 0) : False :=
  false_of_lieModel_three hY.1 (Or.inr (Or.inl ⟨rfl, ht, hY⟩)) h3 hN

private theorem exists_field_three :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨GaloisField 3 1, inferInstance, inferInstance, by
    rw [GaloisField.card 3 1 one_ne_zero, pow_one]⟩

private theorem exists_field_three_pow (m : ℕ) (hm : m ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 3 ^ m ∧
      ∃ σ : K →+* K, ∀ c, σ c = c ^ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨GaloisField 3 m, inferInstance, inferInstance, GaloisField.card 3 m hm,
    frobenius _ 3, fun c => frobenius_def 3 c⟩

theorem s2019ChevOutThree_holds : S2019ChevOutThree := by
  intro Y _ _ d hcat hchar hfield h3 p hp hp5 α hα
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d', hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d' = d at hi
  subst hi
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((LieTypeIndex.valid_iff _).1 hv).2
  have hQ : ∀ Q : PrimePower, Q.p = 3 → Q.card = 3 → Q.exponent = 1 := by
    intro Q hp3 hc3
    rw [PrimePower.card_def, hp3] at hc3
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simp only [hc3, pow_one])
  cases d' with
  | A r Q =>
    simp only [LieTypeIndex.characteristic_A, LieTypeIndex.fieldOrder_A] at hchar hfield
    have hQe := hQ Q hchar hfield
    obtain ⟨hr1, hr4⟩ := hrange
    have hr2 : 2 ≤ r := by
      by_contra hr
      have := hr4 (by omega)
      omega
    have hT := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA r Q hv
    have hcl : StatedClassicalModel Y .PSL (r + 1) 3 1 := by
      rcases hT.2 with h | ⟨h0, -⟩
      · rw [hchar, hQe] at h
        exact CFSG.QuasithinUnique.Setup.Family.statedClassicalModel_of_mulEquiv e.symm h
      · omega
    by_cases hr5 : 5 ≤ r
    · exact (false_of_classical_three (by decide) hcl h3 (by
        simp only [lieSylowExponent]
        have : 30 ≤ (r + 1) * (r + 1 - 1) := by
          rw [Nat.add_sub_cancel]
          nlinarith
        omega)).elim
    · obtain ⟨K, _, _, hK, ⟨e₂⟩⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
          (Or.inl ⟨by decide, hcl⟩)
      exact exists_conj_of_congr e₂ α (exists_conj_of_pow_prime_projectiveSL_three (by omega)
        (by rw [hK, pow_one]) hp hp5 _ (by rw [← map_pow, hα, map_one]))
  | twistedA r Q =>
    simp only [LieTypeIndex.characteristic_twistedA, LieTypeIndex.fieldOrder_twistedA]
      at hchar hfield
    have hQe := hQ Q hchar hfield
    have hr2 : 2 ≤ r := hrange.1
    have hcl := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r Q hv e
    rw [hchar, hQe] at hcl
    by_cases hr5 : 5 ≤ r
    · exact (false_of_classical_three (by decide) hcl h3 (by
        simp only [lieSylowExponent]
        have : 30 ≤ (r + 1) * (r + 1 - 1) := by
          rw [Nat.add_sub_cancel]
          nlinarith
        omega)).elim
    · obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ := hcl
      have h : UnitaryFieldData 3 1 K := ⟨Nat.prime_three, le_rfl, by rw [hK]; norm_num⟩
      obtain ⟨e₂⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (K := K) (n := r + 1))
      let e' : Y ≃* primeFormP h (idGram K (r + 1)) :=
        e₁.trans ((CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm.trans
          e₂.symm)
      exact exists_conj_of_congr e' α (exists_conj_of_pow_prime_primeFormP_three h (by omega) hp
        hp5 _ (by rw [← map_pow, hα, map_one]))
  | B r Q =>
    simp only [LieTypeIndex.characteristic_B, LieTypeIndex.fieldOrder_B] at hchar hfield
    have hQe := hQ Q hchar hfield
    have hr3 : 3 ≤ r := by
      rcases hrange with ⟨hr2, -⟩
      by_contra hr
      apply hdup
      rw [LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨by omega, hfield⟩
    have hcl := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r Q hv
      (by rw [hchar]; norm_num) hr3 e
    rw [hchar, hQe] at hcl
    by_cases hr4 : 4 ≤ r
    · exact (false_of_classical_three (by decide) hcl h3 (by
        simp only [lieSylowExponent]
        nlinarith)).elim
    · obtain rfl : r = 3 := by omega
      exact exists_conj_of_pow_prime_omegaOdd_three hcl hp hp5 α hα
  | C r Q =>
    simp only [LieTypeIndex.characteristic_C, LieTypeIndex.fieldOrder_C] at hchar hfield
    have hQe := hQ Q hchar hfield
    have hr3 : 3 ≤ r := hrange.1
    have hcl := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r Q hv e
    rw [hchar, hQe] at hcl
    by_cases hr4 : 4 ≤ r
    · exact (false_of_classical_three (by decide) hcl h3 (by
        simp only [lieSylowExponent]
        nlinarith)).elim
    · obtain ⟨-, K, _, _, hK, ⟨e₁⟩⟩ := hcl
      exact exists_conj_of_congr e₁ α (exists_conj_of_pow_prime_psp_three (by omega)
        (by rw [hK, pow_one]) hp hp5 _ (by rw [← map_pow, hα, map_one]))
  | D r Q =>
    simp only [LieTypeIndex.characteristic_D, LieTypeIndex.fieldOrder_D] at hchar hfield
    have hQe := hQ Q hchar hfield
    have hr4 : 4 ≤ r := hrange
    have hcl := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r Q hv e
    rw [hchar, hQe] at hcl
    exact (false_of_classical_three (by decide) hcl h3 (by
      simp only [lieSylowExponent]
      have : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul hr4 (by omega)
      omega)).elim
  | twistedD r Q =>
    simp only [LieTypeIndex.characteristic_twistedD, LieTypeIndex.fieldOrder_twistedD]
      at hchar hfield
    have hQe := hQ Q hchar hfield
    have hr4 : 4 ≤ r := hrange
    have hcl := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r Q hv e
    rw [hchar, hQe] at hcl
    exact (false_of_classical_three (by decide) hcl h3 (by
      simp only [lieSylowExponent]
      have : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul hr4 (by omega)
      omega)).elim
  | G2 Q =>
    simp only [LieTypeIndex.characteristic_G2, LieTypeIndex.fieldOrder_G2] at hchar hfield
    obtain ⟨K, _, _, hK⟩ := exists_field_three
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.g2 Q hv (by rw [hchar]; norm_num) K
      (by rw [hK, hfield])
    have hZ : Subgroup.center ↥(adjointGroup Tag.G2 K) = ⊥ :=
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    let e' : Y ≃* ↥(adjointGroup Tag.G2 K) :=
      (e.trans b.symm).trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
        QuotientGroup.quotientBot)
    exact exists_conj_of_congr e' α (exists_conj_of_pow_prime_g2_three hK hp hp5 _
      (by rw [← map_pow, hα, map_one]))
  | F4 Q =>
    simp only [LieTypeIndex.characteristic_F4, LieTypeIndex.fieldOrder_F4] at hchar hfield
    obtain ⟨K, _, _, hK⟩ := exists_field_three
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.f4 Q hv (by rw [hchar]; norm_num) K
      (by rw [hK, hfield])
    exact (false_of_exceptional_three (t := .F4) (by decide)
      ⟨⟨Nat.prime_three, le_rfl, rfl⟩, K, inferInstance, inferInstance, by rw [hK, pow_one],
        ⟨e.trans b.symm⟩⟩ h3 (by decide)).elim
  | E6 Q =>
    simp only [LieTypeIndex.characteristic_E6, LieTypeIndex.fieldOrder_E6] at hchar hfield
    obtain ⟨K, _, _, hK⟩ := exists_field_three
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.e6 Q hv (by rw [hchar]; norm_num) K
      (by rw [hK, hfield])
    exact (false_of_exceptional_three (t := .E6) (by decide)
      ⟨⟨Nat.prime_three, le_rfl, rfl⟩, K, inferInstance, inferInstance, by rw [hK, pow_one],
        ⟨e.trans b.symm⟩⟩ h3 (by decide)).elim
  | E7 Q =>
    simp only [LieTypeIndex.characteristic_E7, LieTypeIndex.fieldOrder_E7] at hchar hfield
    obtain ⟨K, _, _, hK⟩ := exists_field_three
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.e7 Q hv (by rw [hchar]; norm_num) K
      (by rw [hK, hfield])
    exact (false_of_exceptional_three (t := .E7) (by decide)
      ⟨⟨Nat.prime_three, le_rfl, rfl⟩, K, inferInstance, inferInstance, by rw [hK, pow_one],
        ⟨e.trans b.symm⟩⟩ h3 (by decide)).elim
  | E8 Q =>
    simp only [LieTypeIndex.characteristic_E8, LieTypeIndex.fieldOrder_E8] at hchar hfield
    obtain ⟨K, _, _, hK⟩ := exists_field_three
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.e8 Q hv (by rw [hchar]; norm_num) K
      (by rw [hK, hfield])
    exact (false_of_exceptional_three (t := .E8) (by decide)
      ⟨⟨Nat.prime_three, le_rfl, rfl⟩, K, inferInstance, inferInstance, by rw [hK, pow_one],
        ⟨e.trans b.symm⟩⟩ h3 (by decide)).elim
  | twistedE6 Q =>
    simp only [LieTypeIndex.characteristic_twistedE6, LieTypeIndex.fieldOrder_twistedE6]
      at hchar hfield
    obtain ⟨K, _, _, hK, σ, hσ⟩ := exists_field_three_pow 2 (by norm_num)
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.twistedE6 Q hv (by rw [hchar]; norm_num) K
      (by rw [hK, hfield]; rfl) σ (by rw [hfield]; exact hσ)
    exact (false_of_exceptional_three (t := .twistedE6) (by decide)
      ⟨⟨Nat.prime_three, le_rfl, rfl⟩, K, inferInstance, inferInstance, by rw [hK]; rfl, σ,
        hσ, ⟨e.trans b.symm⟩⟩ h3 (by decide)).elim
  | trialityD4 Q =>
    simp only [LieTypeIndex.characteristic_trialityD4, LieTypeIndex.fieldOrder_trialityD4]
      at hchar hfield
    obtain ⟨K, _, _, hK, σ, hσ⟩ := exists_field_three_pow 3 (by norm_num)
    obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.trialityD4 Q hv (by rw [hchar]; norm_num) K
      (by rw [hK, hfield]; rfl) σ (by rw [hfield]; exact hσ)
    exact (false_of_exceptional_three (t := .trialityD4) (by decide)
      ⟨⟨Nat.prime_three, le_rfl, rfl⟩, K, inferInstance, inferInstance, by rw [hK]; rfl, σ,
        hσ, ⟨e.trans b.symm⟩⟩ h3 (by decide)).elim
  | suzuki m => simp at hchar
  | reeG2 m =>
    simp only [LieTypeIndex.fieldOrder_reeG2] at hfield
    have hm : 1 ≤ m := hrange
    have : 3 ^ 3 ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  | reeF4 m => simp at hchar
  | tits => simp at hchar

end Holds

end CFSG.LocalAnalysis.GLTheoremA.S2019
