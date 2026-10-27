module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NoM12
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.ChildrenHered

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G]

theorem isSporadic_m12_of_sporadicRep
    (h1 : CentralTwoBound) (h2 : M11Exclusion) (h4 : M22M23M24Exclusion) (h5 : J1J3J4Exclusion)
    (h6 : HSMcLLyExclusion) (h7 : TwoHSGivesHN) (h8 : LargeExclusion) (h9 : Co2Exclusion)
    (h10 : TwoFi22Gives) (h11 : TwoBGivesM) (h12 : J2Exclusion) (hHe : Induction.ChildHeWHered)
    (hUG : Induction.Balance.UHered G)
    (hNo : NoM12List G → False) {X : Subgroup G} (hX : StdHyp G X)
    (hCo3 : ¬ IsSporadic X .Co3)
    (hSuz : Nat.card (center X) = 2 → ¬ IsSporadic (↥X ⧸ center ↥X) .Suz)
    (hMJ : IsSporadic (↥X ⧸ center ↥X) .M12 ∨ IsSporadic (↥X ⧸ center ↥X) .J2 →
      center X = ⊥)
    (hs : SporadicRep (↥X ⧸ center ↥X)) : IsSporadic X .M12 := by
  have hq := hX.standard.1
  obtain ⟨s, hs⟩ := hs
  have hs' : IsSporadic (↥X ⧸ center ↥X) s := hs
  obtain ⟨hbound, -⟩ := h1 X hq hX.centerTwo s hs'
  have hodd : twoPartBound s = 1 → IsSporadic X s := fun hb =>
    isSporadic_of_center_eq_bot (Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 (hb ▸ hbound))) hs'
  have htwo : twoPartBound s = 2 → IsSporadic X s ∨ Nat.card (center X) = 2 := fun hb =>
    (eq_bot_or_card_eq_two (hb ▸ hbound)).imp (fun h => isSporadic_of_center_eq_bot h hs') id
  have hHN : IsSporadic G .HN → False := fun h => hNo (by
    unfold NoM12List
    iterate 13 refine Or.inr ?_
    exact Or.inl h)
  have hFi23 : IsSporadic G .Fi23 → False := fun h => hNo (by
    unfold NoM12List
    iterate 15 refine Or.inr ?_
    exact Or.inl h)
  have hFi24 : IsSporadic G .Fi24Prime → False := fun h => hNo (by
    unfold NoM12List
    iterate 16 refine Or.inr ?_
    exact Or.inl h)
  have hM : IsSporadic G .M → False := fun h => hNo (by
    unfold NoM12List
    iterate 18 refine Or.inr ?_
    exact h)
  have hOdd : OddLieType G → False := fun h => hNo (Or.inr (Or.inl h))
  cases s with
  | M11 => exact absurd (hodd rfl) (h2 G X hX)
  | M12 => exact isSporadic_of_center_eq_bot (hMJ (Or.inl hs')) hs'
  | M22 => exact absurd hs' (h4 G X hX).1
  | M23 => exact absurd (hodd rfl) (h4 G X hX).2.1
  | M24 => exact absurd (hodd rfl) (h4 G X hX).2.2
  | J1 => exact absurd (hodd rfl) (h5 G X hX).1
  | J2 => exact absurd (isSporadic_of_center_eq_bot (hMJ (Or.inr hs')) hs') (h12 G X hX)
  | J3 => exact absurd (hodd rfl) (h5 G X hX).2.1
  | J4 => exact absurd (hodd rfl) (h5 G X hX).2.2
  | HS =>
    rcases htwo rfl with h | h
    · exact absurd h (h6 G X hX).1
    · exact (hHN (h7 G X hX h hs')).elim
  | McL => exact absurd (hodd rfl) (h6 G X hX).2.1
  | He => exact (hOdd (hHe G hUG X (stdSetting_of_stdHyp hX) hs')).elim
  | Ru =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G X hX).1.2.1
    · exact absurd hs' ((h8 G X hX).2 h).1
  | Suz =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G X hX).1.1
    · exact absurd hs' (hSuz h)
  | ONan => exact absurd (hodd rfl) (h8 G X hX).1.2.2.1
  | Co1 =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G X hX).1.2.2.2.1
    · exact absurd hs' ((h8 G X hX).2 h).2
  | Co2 => exact absurd (hodd rfl) (h9 G X hX)
  | Co3 => exact absurd (hodd rfl) hCo3
  | Fi22 =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G X hX).1.2.2.2.2.1
    · rcases h10 G X hX h hs' with h' | h'
      · exact (hFi23 h').elim
      · exact (hFi24 h').elim
  | Fi23 => exact absurd (hodd rfl) (h8 G X hX).1.2.2.2.2.2.1
  | Fi24Prime => exact absurd (hodd rfl) (h8 G X hX).1.2.2.2.2.2.2.1
  | HN => exact absurd (hodd rfl) (h8 G X hX).1.2.2.2.2.2.2.2.1
  | Ly => exact absurd (hodd rfl) (h6 G X hX).2.2
  | Th => exact absurd (hodd rfl) (h8 G X hX).1.2.2.2.2.2.2.2.2.2.2
  | B =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G X hX).1.2.2.2.2.2.2.2.2.1
    · exact (hM (h11 G X hX h hs')).elim
  | M => exact absurd (hodd rfl) (h8 G X hX).1.2.2.2.2.2.2.2.2.2.1

end CFSG.EvenSporadicStandard.M12Std.Rbc
