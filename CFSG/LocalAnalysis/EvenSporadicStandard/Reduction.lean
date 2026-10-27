module

public import CFSG.Blueprint.EvenStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure StdHyp (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G
  standard : standardComponentIsStandard L
  oddCore : ∀ t : G, orderOf t = 2 →
    standardComponentOddCore (centralizer ({t} : Set G)) = ⊥
  cyclicSylow : ∃ S : Sylow 2 (centralizer (L : Set G)),
    IsCyclic (S : Subgroup (centralizer (L : Set G)))
  centerTwo : IsPGroup 2 (center L)

@[expose] def twoPartBound : TauCeti.SporadicName → ℕ
  | .M22 => 4
  | .M12 | .J2 | .HS | .Ru | .Suz | .Co1 | .Fi22 | .B => 2
  | _ => 1

@[expose] def CentralTwoBound : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsPGroup 2 (center L) →
    ∀ s : TauCeti.SporadicName, IsSporadic (L ⧸ center L) s →
      Nat.card (center L) ∣ twoPartBound s ∧ (s = .M22 → IsCyclic (center L))

@[expose] def M11Exclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → ¬ IsSporadic L .M11

@[expose] def M12Co3Suz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    (IsSporadic L .M12 ∨ IsSporadic L .Co3 ∨
      (Nat.card (center L) = 2 ∧ IsSporadic (L ⧸ center L) .Suz)) →
    IsSporadic L .M12 ∧ IsSporadic G .Co3

@[expose] def M22M23M24Exclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    ¬ IsSporadic (L ⧸ center L) .M22 ∧ ¬ IsSporadic L .M23 ∧ ¬ IsSporadic L .M24

@[expose] def J1J3J4Exclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    ¬ IsSporadic L .J1 ∧ ¬ IsSporadic L .J3 ∧ ¬ IsSporadic L .J4

@[expose] def HSMcLLyExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    ¬ IsSporadic L .HS ∧ ¬ IsSporadic L .McL ∧ ¬ IsSporadic L .Ly

@[expose] def TwoHSGivesHN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    Nat.card (center L) = 2 → IsSporadic (L ⧸ center L) .HS → IsSporadic G .HN

@[expose] def LargeExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    (¬ IsSporadic L .Suz ∧ ¬ IsSporadic L .Ru ∧ ¬ IsSporadic L .ONan ∧ ¬ IsSporadic L .Co1 ∧
      ¬ IsSporadic L .Fi22 ∧ ¬ IsSporadic L .Fi23 ∧ ¬ IsSporadic L .Fi24Prime ∧
      ¬ IsSporadic L .HN ∧ ¬ IsSporadic L .B ∧ ¬ IsSporadic L .M ∧ ¬ IsSporadic L .Th) ∧
    (Nat.card (center L) = 2 →
      ¬ IsSporadic (L ⧸ center L) .Ru ∧ ¬ IsSporadic (L ⧸ center L) .Co1)

@[expose] def Co2Exclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → ¬ IsSporadic L .Co2

@[expose] def TwoFi22Gives : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    Nat.card (center L) = 2 → IsSporadic (L ⧸ center L) .Fi22 →
      IsSporadic G .Fi23 ∨ IsSporadic G .Fi24Prime

@[expose] def TwoBGivesM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    Nat.card (center L) = 2 → IsSporadic (L ⧸ center L) .B → IsSporadic G .M

@[expose] def J2Exclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → ¬ IsSporadic L .J2

@[expose] def ModelsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ (L : Subgroup G), standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 → standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    ∀ (S : Sylow 2 (centralizer (L : Set G))),
    IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    Recognition.Exact.EvenStandardType (L ⧸ center L) →
    ¬ Recognition.Exact.EvenStandardException (L ⧸ center L) →
    Recognition.Exact.EvenStandardResidual L →
    SporadicRep (L ⧸ center L) →
    (IsSporadic (L ⧸ center L) .M12 ∨ IsSporadic (L ⧸ center L) .J2 → center L = ⊥) →
    Recognition.EvenSporadicOutcome G

theorem isSporadic_of_center_eq_bot {L : Type} [Group L] (h : center L = ⊥)
    {s : TauCeti.SporadicName} (hs : IsSporadic (L ⧸ center L) s) : IsSporadic L s := by
  obtain ⟨e⟩ := hs
  exact ⟨((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem eq_bot_or_card_eq_two {L : Type} [Group L] [Finite L] (h : Nat.card (center L) ∣ 2) :
    center L = ⊥ ∨ Nat.card (center L) = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
  · exact Or.inr h2

theorem modelsStatement_of_children (h1 : CentralTwoBound) (h2 : M11Exclusion)
    (h3 : M12Co3Suz) (h4 : M22M23M24Exclusion) (h5 : J1J3J4Exclusion) (h6 : HSMcLLyExclusion)
    (h7 : TwoHSGivesHN) (h8 : LargeExclusion) (h9 : Co2Exclusion) (h10 : TwoFi22Gives)
    (h11 : TwoBGivesM) (h12 : J2Exclusion) : ModelsStatement := by
  intro G _ _ _ hnonab hK L hL hcore S hS _ hexc hres hspor hMJ
  have hZ : IsPGroup 2 (center L) := hres.1
  have std : StdHyp G L := ⟨inferInstance, hnonab, hK, hL, hcore, ⟨S, hS⟩, hZ⟩
  have hq : IsQuasisimple L := hL.1
  obtain ⟨s, hs⟩ := hspor
  have hs' : IsSporadic (L ⧸ center L) s := hs
  obtain ⟨hbound, -⟩ := h1 L hq hZ s hs'
  have hodd : twoPartBound s = 1 → IsSporadic L s := fun hb =>
    isSporadic_of_center_eq_bot (Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 (hb ▸ hbound))) hs'
  have htwo : twoPartBound s = 2 → IsSporadic L s ∨ Nat.card (center L) = 2 := fun hb =>
    (eq_bot_or_card_eq_two (hb ▸ hbound)).imp (fun h => isSporadic_of_center_eq_bot h hs') id
  unfold Recognition.EvenSporadicOutcome
  cases s with
  | M11 => exact absurd (hodd rfl) (h2 G L std)
  | M12 => exact Or.inl (h3 G L std (Or.inl (isSporadic_of_center_eq_bot (hMJ (Or.inl hs')) hs'))).2
  | M22 => exact absurd hs' (h4 G L std).1
  | M23 => exact absurd (hodd rfl) (h4 G L std).2.1
  | M24 => exact absurd (hodd rfl) (h4 G L std).2.2
  | J1 => exact absurd (hodd rfl) (h5 G L std).1
  | J2 => exact absurd (isSporadic_of_center_eq_bot (hMJ (Or.inr hs')) hs') (h12 G L std)
  | J3 => exact absurd (hodd rfl) (h5 G L std).2.1
  | J4 => exact absurd (hodd rfl) (h5 G L std).2.2
  | HS =>
    rcases htwo rfl with h | h
    · exact absurd h (h6 G L std).1
    · exact Or.inr (Or.inl (h7 G L std h hs'))
  | McL => exact absurd (hodd rfl) (h6 G L std).2.1
  | He =>
    exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hs')))))))
      hexc
  | Ru =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G L std).1.2.1
    · exact absurd hs' ((h8 G L std).2 h).1
  | Suz =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G L std).1.1
    · exact Or.inl (h3 G L std (Or.inr (Or.inr ⟨h, hs'⟩))).2
  | ONan => exact absurd (hodd rfl) (h8 G L std).1.2.2.1
  | Co1 =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G L std).1.2.2.2.1
    · exact absurd hs' ((h8 G L std).2 h).2
  | Co2 => exact absurd (hodd rfl) (h9 G L std)
  | Co3 => exact Or.inl (h3 G L std (Or.inr (Or.inl (hodd rfl)))).2
  | Fi22 =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G L std).1.2.2.2.2.1
    · rcases h10 G L std h hs' with h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
  | Fi23 => exact absurd (hodd rfl) (h8 G L std).1.2.2.2.2.2.1
  | Fi24Prime => exact absurd (hodd rfl) (h8 G L std).1.2.2.2.2.2.2.1
  | HN => exact absurd (hodd rfl) (h8 G L std).1.2.2.2.2.2.2.2.1
  | Ly => exact absurd (hodd rfl) (h6 G L std).2.2
  | Th => exact absurd (hodd rfl) (h8 G L std).1.2.2.2.2.2.2.2.2.2.2
  | B =>
    rcases htwo rfl with h | h
    · exact absurd h (h8 G L std).1.2.2.2.2.2.2.2.2.1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h11 G L std h hs'))))))
  | M => exact absurd (hodd rfl) (h8 G L std).1.2.2.2.2.2.2.2.2.2.1

end CFSG.EvenSporadicStandard
