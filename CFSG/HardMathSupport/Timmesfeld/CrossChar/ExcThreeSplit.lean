module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousReeF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldD4Family
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldTwE6Family
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcField
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

section ReeF4


theorem rankLE2_three_cat_reeF4 {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) :
    RankLE2 3 (Cat ⟨.reeF4 m, hv⟩) := by
  obtain ⟨X, _, _, _, -, hX, -, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  refine RankLE2.of_mulEquiv e.symm fun F hF => ?_
  exact CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma m X hX F
    ⟨hF.1, hF.2⟩

theorem crossCharFamAt_reeF4_three_inner : CrossCharFamAt .reeF4 fun idx p =>
    ∃ m : ℕ, idx.1 = .reeF4 m ∧ p = 3 ∧ ¬ 3 ∣ 2 * m + 1 := by
  rintro ⟨d, hv⟩ _ p hp hp2 - ⟨m, hd, rfl, hf⟩
  change d = _ at hd
  subst hd
  obtain ⟨X, _, _, _, _, _, hS, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have : IsSimpleGroup (Cat ⟨.reeF4 m, hv⟩) := hS
  have : Finite (ModGL F4.tag X) := finite_modGL
  have : Finite (F4.reeGamma X m) := Subtype.finite
  have : Finite (Cat ⟨.reeF4 m, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨-, -, -, -, hcard, -⟩ := large_Ree_model_field_outer_group_and_inner_involutions _ 2
    (2 * m + 1) (reeTitsModel_cat_reeF4 hv)
  have hcop : Nat.Coprime 3 (Nat.card (Outer (Cat ⟨.reeF4 m, hv⟩))) := by
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hf
  exact isLocallyBalancedAbs_of_rankLE2_of_simple (MulEquiv.refl _)
    (QuotientGroup.mk' (inner (Cat ⟨.reeF4 m, hv⟩))) hp hcop
    (fun x hx _ => (QuotientGroup.eq_one_iff (N := inner (Cat ⟨.reeF4 m, hv⟩)) x).1 hx)
    (rankLE2_three_cat_reeF4 hv)

theorem crossCharFamAt_reeF4_open_of
    (h5 : CrossCharFamAt .reeF4 fun idx p => ∃ m : ℕ, idx.1 = .reeF4 m ∧ 5 ≤ p ∧
      p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 ∧ p ∣ 2 * m + 1)
    (h3 : CrossCharFamAt .reeF4 fun idx p => ∃ m : ℕ, idx.1 = .reeF4 m ∧ p = 3 ∧
      3 ∣ 2 * m + 1) :
    CrossCharFamAt .reeF4 fun idx p => ¬ regimeReeF4Vac idx p := by
  intro idx hidx p hp hp2 hch hR
  obtain ⟨m, hm⟩ := hidx
  by_cases hp3 : p = 3
  · subst hp3
    by_cases hf : 3 ∣ 2 * m + 1
    · exact h3 idx ⟨m, hm⟩ 3 hp hp2 hch ⟨m, hm, rfl, hf⟩
    · exact crossCharFamAt_reeF4_three_inner idx ⟨m, hm⟩ 3 hp hp2 hch ⟨m, hm, rfl, hf⟩
  · have hp5 : 5 ≤ p := (eq_three_or_five_le hp hp2).resolve_left hp3
    refine h5 idx ⟨m, hm⟩ p hp hp2 hch ⟨m, hm, hp5, ?_, ?_⟩
    · by_contra hnd
      exact hR (Or.inl ⟨m, hm, hnd⟩)
    · by_contra hf
      exact hR (Or.inr ⟨m, hm, hp5, hf⟩)

end ReeF4

section TrialityTwisted


theorem crossCharFamAt_trialityD4_open_of_three
    (h3 : CrossCharFamAt .trialityD4 fun _ p => p = 3) :
    CrossCharFamAt .trialityD4 fun idx p => ¬ regimeTrialityD4Vac idx p := by
  intro idx hidx p hp hp2 hch hR
  obtain ⟨q, hq⟩ := hidx
  by_cases hp3 : p = 3
  · exact h3 idx ⟨q, hq⟩ p hp hp2 hch hp3
  · have hp5 : 5 ≤ p := (eq_three_or_five_le hp hp2).resolve_left hp3
    refine crossCharFamAt_trialityD4_field idx ⟨q, hq⟩ p hp hp2 hch ⟨q, hq, hp5, ?_, ?_⟩
    · by_contra hnd
      exact hR (Or.inl ⟨q, hq, hnd⟩)
    · by_contra hf
      exact hR (Or.inr ⟨q, hq, hp5, hf⟩)

end TrialityTwisted

section TwistedE6


theorem crossCharFamAt_twistedE6_open_of_ge_three
    (h3 : CrossCharFamAt .twistedE6 fun idx p => ∃ q : TauCeti.PrimePower,
      idx.1 = .twistedE6 q ∧ 3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p))) :
    CrossCharFamAt .twistedE6 fun idx p =>
      ¬ regimeExcVac TauCeti.LieTypeIndex.twistedE6 degCountTw idx p := by
  intro idx hidx p hp hp2 hch hR
  obtain ⟨q, hq⟩ := hidx
  rcases ge_three_or_field_of_not_regimeExcVac (fun _ _ h => TauCeti.LieTypeIndex.twistedE6.inj h)
    degCountTw hq hR with h | ⟨h2, hf⟩
  · exact h3 idx ⟨q, hq⟩ p hp hp2 hch ⟨q, hq, h⟩
  · exact crossCharFamAt_twistedE6_field idx ⟨q, hq⟩ p hp hp2 hch ⟨q, hq, h2, hf⟩

end TwistedE6

end CFSG.HardMathSupport.Timmesfeld.CrossChar
