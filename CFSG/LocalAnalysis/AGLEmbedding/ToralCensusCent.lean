module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentSpMain
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthModel
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Open ToralCensus

@[expose] def IdxBCent : TauCeti.LieTypeIndex → Prop
  | .B r q => q.p = 2 ∧ ((4 ≤ q.card ∧ 3 ≤ r) ∨ (q.card = 2 ∧ 5 ≤ r))
  | _ => False

@[expose] def IdxDCent : TauCeti.LieTypeIndex → Prop
  | .D r q => q.p = 2 ∧ ((4 ≤ q.card ∧ 4 ≤ r) ∨ (q.card = 2 ∧ 6 ≤ r))
  | _ => False

@[expose] def IdxTwistedDCent : TauCeti.LieTypeIndex → Prop
  | .twistedD r q => q.p = 2 ∧ ((4 ≤ q.card ∧ 4 ≤ r) ∨ (q.card = 2 ∧ 6 ≤ r))
  | _ => False

@[expose] def IdxBResidual : TauCeti.LieTypeIndex → Prop
  | .B r q => q.p = 2 ∧ ((4 ≤ q.card ∧ r = 2) ∨ (q.card = 2 ∧ (r = 3 ∨ r = 4)))
  | _ => False

@[expose] def IdxDResidual : TauCeti.LieTypeIndex → Prop
  | .D r q => q.p = 2 ∧ q.card = 2 ∧ (r = 4 ∨ r = 5)
  | _ => False

@[expose] def IdxTwistedDResidual : TauCeti.LieTypeIndex → Prop
  | .twistedD r q => q.p = 2 ∧ q.card = 2 ∧ (r = 4 ∨ r = 5)
  | _ => False

namespace ToralCensus

theorem exponent_cases_of_p_eq_two {q : TauCeti.PrimePower} (hp : q.p = 2) :
    (q.card = 2 ↔ q.exponent = 1) ∧ (4 ≤ q.card ↔ 2 ≤ q.exponent) := by
  have hc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp]
  have he := q.exponent_pos
  rw [hc]
  refine ⟨⟨fun h => ?_, fun h => by rw [h, pow_one]⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact Nat.pow_right_injective le_rfl (h.trans (pow_one 2).symm)
  · by_contra h2
    rw [show q.exponent = 1 by omega, pow_one] at h
    omega
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h

theorem card_eq_two_or_four_le_of_p_eq_two {q : TauCeti.PrimePower} (hp : q.p = 2) :
    q.card = 2 ∨ 4 ≤ q.card := by
  obtain ⟨h1, h2⟩ := exponent_cases_of_p_eq_two hp
  rcases Nat.lt_or_ge q.exponent 2 with h | h
  · exact Or.inl (h1.mpr (by have := q.exponent_pos; omega))
  · exact Or.inr (h2.mpr h)

end ToralCensus

theorem centNoncycThreeGroup_of_isLieOf_b {X : Type} [Group X] (h : IsLieOf IdxBCent X) :
    CentNoncycThreeGroup X := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d <;> simp only [IdxBCent] at hd
  rename_i r q
  obtain ⟨hp, hr⟩ := hd
  obtain ⟨h1, h2⟩ := exponent_cases_of_p_eq_two hp
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp
    (by omega) e
  rw [hp] at hm
  exact centNoncycThreeGroup_of_model_psp hm (by
    rcases hr with ⟨hq, hr⟩ | ⟨hq, hr⟩
    exacts [Or.inl ⟨h2.mp hq, hr⟩, Or.inr ⟨h1.mp hq, hr⟩])

theorem centNoncycThreeGroup_of_isLieOf_d {X : Type} [Group X] (h : IsLieOf IdxDCent X) :
    CentNoncycThreeGroup X := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d <;> simp only [IdxDCent] at hd
  rename_i r q
  obtain ⟨hp, hr⟩ := hd
  obtain ⟨h1, h2⟩ := exponent_cases_of_p_eq_two hp
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp e
  rw [hp] at hm
  exact centNoncycThreeGroup_of_model_pomegaPlus hm (by
    rcases hr with ⟨hq, hr⟩ | ⟨hq, hr⟩
    exacts [Or.inl ⟨h2.mp hq, hr⟩, Or.inr ⟨h1.mp hq, hr⟩])

theorem centNoncycThreeGroup_of_isLieOf_twistedD {X : Type} [Group X]
    (h : IsLieOf IdxTwistedDCent X) : CentNoncycThreeGroup X := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d <;> simp only [IdxTwistedDCent] at hd
  rename_i r q
  obtain ⟨hp, hr⟩ := hd
  obtain ⟨h1, h2⟩ := exponent_cases_of_p_eq_two hp
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp e
  rw [hp] at hm
  exact centNoncycThreeGroup_of_model_pomegaMinus hm (by
    rcases hr with ⟨hq, hr⟩ | ⟨hq, hr⟩
    exacts [Or.inl ⟨h2.mp hq, hr⟩, Or.inr ⟨h1.mp hq, hr⟩])

theorem kFactCentNoncycThree_b : KFactCentNoncycThree (IsLieOf IdxBCent) :=
  kFactCentNoncycThree_of_group fun _ _ h => centNoncycThreeGroup_of_isLieOf_b h

theorem kFactCentNoncycThree_d : KFactCentNoncycThree (IsLieOf IdxDCent) :=
  kFactCentNoncycThree_of_group fun _ _ h => centNoncycThreeGroup_of_isLieOf_d h

theorem kFactCentNoncycThree_twistedD : KFactCentNoncycThree (IsLieOf IdxTwistedDCent) :=
  kFactCentNoncycThree_of_group fun _ _ h => centNoncycThreeGroup_of_isLieOf_twistedD h

theorem fixThreeVoid_b_cent : FixThreeVoid (IsLieOf IdxBCent) :=
  fixThreeVoid_of_centNoncyc kFactCentNoncycThree_b

theorem fixThreeVoid_d_cent : FixThreeVoid (IsLieOf IdxDCent) :=
  fixThreeVoid_of_centNoncyc kFactCentNoncycThree_d

theorem fixThreeVoid_twistedD_cent : FixThreeVoid (IsLieOf IdxTwistedDCent) :=
  fixThreeVoid_of_centNoncyc kFactCentNoncycThree_twistedD

theorem isLieOf_idxB_cases {X : Type} [Group X] (h : IsLieOf IdxB X) :
    IsLieOf IdxBCent X ∨ IsLieOf IdxBResidual X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := h
  cases d <;> simp only [IdxB] at hd
  rename_i r q
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  simp only at hr
  rcases card_eq_two_or_four_le_of_p_eq_two hd with hq | hq
  · by_cases hr5 : 5 ≤ r
    · exact Or.inl ⟨⟨_, hv⟩, ⟨hd, Or.inr ⟨hq, hr5⟩⟩, he⟩
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hd, Or.inr ⟨hq, by
        have : ¬ (r = 2 ∧ q.card = 2) := hr.2
        omega⟩⟩, he⟩
  · by_cases hr3 : 3 ≤ r
    · exact Or.inl ⟨⟨_, hv⟩, ⟨hd, Or.inl ⟨hq, hr3⟩⟩, he⟩
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hd, Or.inl ⟨hq, by omega⟩⟩, he⟩

theorem isLieOf_idxD_cases {X : Type} [Group X] (h : IsLieOf IdxD X) :
    IsLieOf IdxDCent X ∨ IsLieOf IdxDResidual X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := h
  cases d <;> simp only [IdxD] at hd
  rename_i r q
  have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases card_eq_two_or_four_le_of_p_eq_two hd with hq | hq
  · by_cases hr6 : 6 ≤ r
    · exact Or.inl ⟨⟨_, hv⟩, ⟨hd, Or.inr ⟨hq, hr6⟩⟩, he⟩
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hd, hq, by omega⟩, he⟩
  · exact Or.inl ⟨⟨_, hv⟩, ⟨hd, Or.inl ⟨hq, hr⟩⟩, he⟩

theorem isLieOf_idxTwistedD_cases {X : Type} [Group X] (h : IsLieOf IdxTwistedD X) :
    IsLieOf IdxTwistedDCent X ∨ IsLieOf IdxTwistedDResidual X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := h
  cases d <;> simp only [IdxTwistedD] at hd
  rename_i r q
  have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases card_eq_two_or_four_le_of_p_eq_two hd with hq | hq
  · by_cases hr6 : 6 ≤ r
    · exact Or.inl ⟨⟨_, hv⟩, ⟨hd, Or.inr ⟨hq, hr6⟩⟩, he⟩
    · exact Or.inr ⟨⟨_, hv⟩, ⟨hd, hq, by omega⟩, he⟩
  · exact Or.inl ⟨⟨_, hv⟩, ⟨hd, Or.inl ⟨hq, hr⟩⟩, he⟩

theorem fixThreeVoid_b_of_residual (h : FixThreeVoid (IsLieOf IdxBResidual)) :
    FixThreeVoid (IsLieOf IdxB) := fun Y _ _ L J u hd hF =>
  (isLieOf_idxB_cases hF).elim (fixThreeVoid_b_cent Y L J u hd) (h Y L J u hd)

theorem fixThreeVoid_d_of_residual (h : FixThreeVoid (IsLieOf IdxDResidual)) :
    FixThreeVoid (IsLieOf IdxD) := fun Y _ _ L J u hd hF =>
  (isLieOf_idxD_cases hF).elim (fixThreeVoid_d_cent Y L J u hd) (h Y L J u hd)

theorem fixThreeVoid_twistedD_of_residual (h : FixThreeVoid (IsLieOf IdxTwistedDResidual)) :
    FixThreeVoid (IsLieOf IdxTwistedD) := fun Y _ _ L J u hd hF =>
  (isLieOf_idxTwistedD_cases hF).elim (fixThreeVoid_twistedD_cent Y L J u hd) (h Y L J u hd)

end CFSG.AGLEmbedding
