module

public import CFSG.HardMathSupport.Dickson.Bal207.SpFC
import CFSG.Adapters.TauCetiLieModels
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.GH74.Generic.S3.L3FRankDvd
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFC

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

@[expose] def FixedIdx : TauCeti.LieTypeIndex → Prop
  | .D s q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ Even s ∧ 4 ≤ s
  | .twistedD s q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ Odd s ∧ 5 ≤ s
  | .twistedA r q => r = 3 ∧ (IsTwoPow q 1 ∨ IsTwoPow q 3)
  | .A r q => r = 1 ∧ IsTwoPow q 3
  | _ => False

theorem eleven_dvd_ordTwistedA {r q : ℕ} (hr : 5 ≤ r) (hq : q = 2 ∨ q = 8) :
    11 ∣ ordTwistedA r q := by
  have hg : Nat.gcd (r + 1) (q + 1) ∣
      q ^ (r * (r + 1) / 2) * ∏ i ∈ Finset.Icc 2 (r + 1), (q ^ i - (-1 : ℤ) ^ i).toNat := by
    refine Dvd.dvd.mul_left ?_ _
    refine (Nat.gcd_dvd_right _ _).trans ?_
    have h2 : q + 1 ∣ (q ^ 2 - (-1 : ℤ) ^ 2).toNat := by
      rw [CFSG.GH74.Generic.S3.L3Ord.toNat_sq]
      exact CFSG.GH74.Generic.S3.L3Ord.add_one_dvd_sq_sub_one q
    exact h2.trans (Finset.dvd_prod_of_mem (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
      (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩))
  have hmul : ordTwistedA r q * Nat.gcd (r + 1) (q + 1) =
      q ^ (r * (r + 1) / 2) * ∏ i ∈ Finset.Icc 2 (r + 1), (q ^ i - (-1 : ℤ) ^ i).toNat := by
    unfold ordTwistedA
    exact Nat.div_mul_cancel hg
  have h11 : 11 ∣ q ^ (r * (r + 1) / 2) *
      ∏ i ∈ Finset.Icc 2 (r + 1), (q ^ i - (-1 : ℤ) ^ i).toNat := by
    refine Dvd.dvd.mul_left ?_ _
    refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem
      (fun i => ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat)
      (Finset.mem_Icc.2 ⟨by norm_num, by omega⟩ : 5 ∈ Finset.Icc 2 (r + 1)))
    rcases hq with rfl | rfl <;> decide
  have hcop : Nat.Coprime 11 (Nat.gcd (r + 1) (q + 1)) := by
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) ?_
    rcases hq with rfl | rfl <;> decide
  have h11' : 11 ∣ ordTwistedA r q * Nat.gcd (r + 1) (q + 1) := hmul ▸ h11
  exact hcop.dvd_of_dvd_mul_right h11'

theorem exists_card_ordTwistedA (d : TauCeti.ValidLieTypeIndex) (hd : IsSpFirstClaimIdx d.1) :
    ∃ r q : ℕ, 5 ≤ r ∧ (q = 2 ∨ q = 8) ∧
      Nat.card (TauCeti.CFSGIndex.lie d).Group = ordTwistedA r q := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r q =>
    obtain ⟨hq, -, hr5, -⟩ := hd
    have hp : q.p = 2 := by rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
    have hL := CFSG.Models.lieModel_twistedA r q hv (MulEquiv.refl _)
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := by
      rw [← hp]
      exact TauCeti.LieTypeIndex.characteristic_twistedA r q
    rw [hc] at hL
    have hB := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [CFSG.Blueprint.classicalTags]) hL
    have hcard := CFSG.SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow hB
    rw [Nat.add_sub_cancel] at hcard
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA r q
    rw [hf] at hcard
    refine ⟨r, 2 ^ q.exponent, hr5, ?_, hcard⟩
    rcases hq with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> norm_num
  | _ => exact hd.elim

theorem eleven_dvd_card_of_isSpFirstClaimIdx (d : TauCeti.ValidLieTypeIndex)
    (hd : IsSpFirstClaimIdx d.1) : 11 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨r, q, hr, hq, h⟩ := exists_card_ordTwistedA d hd
  rw [h]
  exact eleven_dvd_ordTwistedA hr hq

theorem card_eq_ordD_of_isD4EightIdx (d : TauCeti.ValidLieTypeIndex) (hd : IsD4EightIdx d.1) :
    Nat.card (TauCeti.CFSGIndex.lie d).Group = ordD 4 8 := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | D r q =>
    obtain ⟨rfl, hp, he⟩ := hd
    have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv (MulEquiv.refl _)
    rw [hp, he] at hM
    have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.2.1 rfl
    rw [h]
    norm_num
  | _ => exact hd.elim

theorem not_eleven_dvd_ordD_four_eight : ¬ 11 ∣ ordD 4 8 := by
  unfold ordD
  decide

theorem card_eq_of_isL2EightIndex (d : TauCeti.ValidLieTypeIndex) (hd : IsL2EightIndex d.1) :
    Nat.card (TauCeti.CFSGIndex.lie d).Group = 504 := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    obtain ⟨rfl, hp, he⟩ := hd
    have hL := CFSG.Models.lieModel_A 1 q hv (MulEquiv.refl _)
    have hB := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [CFSG.Blueprint.classicalTags]) hL
    rw [hp, he] at hB
    rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hB]
    decide
  | _ => exact hd.elim

theorem isLieQuot_bal207_of_fixed {Y : Type} [Group Y] {J : Subgroup Y}
    (hF : IsLieQuot ↥J FixedIdx) (hU : IsLieQuot ↥J IsSpFirstClaimIdx) :
    IsLieQuot ↥J (fun d => Bal207Index 3 d ∧ ¬ IsG2EightIndex d) := by
  obtain ⟨d₁, hd₁, ⟨e₁⟩⟩ := hF
  obtain ⟨d₂, hd₂, ⟨e₂⟩⟩ := hU
  have hcard : Nat.card (TauCeti.CFSGIndex.lie d₁).Group =
      Nat.card (TauCeti.CFSGIndex.lie d₂).Group := Nat.card_congr (e₁.symm.trans e₂).toEquiv
  have h11 := eleven_dvd_card_of_isSpFirstClaimIdx d₂ hd₂
  have h15 := FirstClaim.two_pow_dvd_card_of_isSpFirstClaimIdx d₂ hd₂
  rw [← hcard] at h11 h15
  obtain ⟨d, hv⟩ := d₁
  cases d with
  | D s q =>
    obtain ⟨hq, hs, h4⟩ := hd₁
    by_cases h6 : 6 ≤ s
    · exact ⟨⟨.D s q, hv⟩, ⟨⟨rfl, Or.inl ⟨hq, hs, h6⟩⟩, fun h => h⟩, ⟨e₁⟩⟩
    · have hs4 : s = 4 := by obtain ⟨k, hk⟩ := hs; omega
      subst hs4
      rcases hq with hq | hq
      · exact ⟨⟨.D 4 q, hv⟩, ⟨⟨rfl, Or.inr ⟨hq, rfl⟩⟩, fun h => h⟩, ⟨e₁⟩⟩
      · exfalso
        rw [card_eq_ordD_of_isD4EightIdx ⟨.D 4 q, hv⟩ ⟨rfl, hq⟩] at h11
        exact not_eleven_dvd_ordD_four_eight h11
  | twistedD s q =>
    exact ⟨⟨.twistedD s q, hv⟩, ⟨⟨rfl, hd₁⟩, fun h => h⟩, ⟨e₁⟩⟩
  | twistedA r q =>
    obtain ⟨rfl, hq⟩ := hd₁
    exact ⟨⟨.twistedA 3 q, hv⟩, ⟨⟨rfl, Or.inl ⟨hq, by decide⟩⟩, fun h => h⟩, ⟨e₁⟩⟩
  | A r q =>
    exfalso
    rw [card_eq_of_isL2EightIndex ⟨.A r q, hv⟩ hd₁] at h15
    exact absurd h15 (by decide)
  | _ => exact hd₁.elim

theorem bal207Index_of_model_plus {G : Type} [Group G] {s : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus s 2 1) (hs : Even s) (h6 : 6 ≤ s) :
    ∃ d : TauCeti.ValidLieTypeIndex, (Bal207Index 3 d.1 ∧ ¬ IsG2EightIndex d.1) ∧
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have h4 : 4 ≤ s := by omega
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hv : (TauCeti.LieTypeIndex.D s q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨h4, fun h => h⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hG
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD s q hv (MulEquiv.refl _))
  exact ⟨⟨.D s q, hv⟩, ⟨⟨rfl, Or.inl ⟨Or.inl ⟨rfl, rfl⟩, hs, h6⟩⟩, fun h => h⟩, ⟨e⟩⟩

theorem bal207Index_of_model_minus {G : Type} [Group G] {s : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus s 2 1) (hs : Odd s) (h5 : 5 ≤ s) :
    ∃ d : TauCeti.ValidLieTypeIndex, (Bal207Index 3 d.1 ∧ ¬ IsG2EightIndex d.1) ∧
      Nonempty (G ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have h4 : 4 ≤ s := by omega
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hv : (TauCeti.LieTypeIndex.twistedD s q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨h4, fun h => h⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hG
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD s q hv (MulEquiv.refl _))
  exact ⟨⟨.twistedD s q, hv⟩, ⟨⟨rfl, Or.inl ⟨rfl, rfl⟩, hs, h5⟩, fun h => h⟩, ⟨e⟩⟩

end CFSG.HardMathSupport.Dickson.Bal207.OrthFC

end
