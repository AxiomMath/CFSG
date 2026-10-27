module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporX
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Alt
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSporTwoPart

public section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup CFSG.Blueprint

theorem rowFor_spor_resid
    (hHe : TBLit.HeldTrivialMultiplier) (hCT : EvenSporadicStandard.CentralTwoBound)
    {s : TauCeti.SporadicName} (hs : s ≠ .M12 ∧ s ≠ .J2 ∧ s ≠ .HS) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y s := by
  have hJ3 := N36.hsj3TwoMultiplierFact_of_centralTwoBound hCT
  cases s with
  | M11 => exact rowFor_spor_of_compData sporCompData_M11
  | M12 => exact absurd rfl hs.1
  | M22 => exact rowFor_spor_of_compData sporCompData_M22
  | M23 => exact rowFor_spor_of_compData sporCompData_M23
  | M24 => exact rowFor_spor_of_compData sporCompData_M24
  | J1 => exact rowFor_spor_J1
  | J2 => exact absurd rfl hs.2.1
  | J3 => exact rowFor_spor_J3 hJ3
  | J4 => exact rowFor_spor_of_compData sporCompData_J4
  | HS => exact absurd rfl hs.2.2
  | McL => exact rowFor_spor_of_compData sporCompData_McL
  | Suz => exact rowFor_spor_Suz
  | Co1 => exact rowFor_spor_of_compData sporCompData_Co1
  | Co2 => exact rowFor_spor_of_compData sporCompData_Co2
  | Co3 => exact rowFor_spor_of_compData sporCompData_Co3
  | He => exact rowFor_spor_He hHe
  | Ly => exact rowFor_spor_of_compData sporCompData_Ly
  | ONan => exact rowFor_spor_ONan_of_centralTwoBound hCT
  | Ru => exact rowFor_spor_of_compData sporCompData_Ru
  | Fi22 => exact rowFor_spor_of_compData sporCompData_Fi22
  | Fi23 => exact rowFor_spor_of_compData sporCompData_Fi23
  | Fi24Prime => exact rowFor_spor_of_compData sporCompData_Fi24Prime
  | HN => exact rowFor_spor_of_compData sporCompData_HN
  | Th => exact rowFor_spor_of_compData sporCompData_Th
  | B => exact rowFor_spor_of_compData sporCompData_B
  | M => exact rowFor_spor_of_compData sporCompData_M

end CFSG.ComponentClassification.HarrisLit.L35

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def Harris81Lemma35IdentResidFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (w v : G) (L K : Subgroup G),
    L35.Config G p w v L K → ¬ N36.IsAlt (↥K ⧸ Open.fusionZStar ↥K) →
    (Milestones.ClassicalRep (↥K ⧸ Open.fusionZStar ↥K) ∨
      Blueprint.ExceptionalRep (↥K ⧸ Open.fusionZStar ↥K) ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .M12 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .J2 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .HS) →
    L35.Concl p v L K

theorem harris81Lemma35IdentNonAltFact_of_resid
    (hHe : TBLit.HeldTrivialMultiplier) (hCT : EvenSporadicStandard.CentralTwoBound)
    (hR : Harris81Lemma35IdentResidFact) : Harris81Lemma35IdentNonAltFact := by
  intro G _ _ p w v L K h halt
  rcases h.catalog_bar with ⟨q, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hex | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonabelian_bar
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact absurd ⟨n, hn, ⟨e⟩⟩ halt
  · exact hR G p w v L K h halt (Or.inl hcl)
  · exact hR G p w v L K h halt (Or.inr (Or.inl hex))
  · by_cases hM12 : s = .M12
    · subst hM12
      exact hR G p w v L K h halt (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    by_cases hJ2 : s = .J2
    · subst hJ2
      exact hR G p w v L K h halt (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))
    by_cases hHS : s = .HS
    · subst hHS
      exact hR G p w v L K h halt (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩))))
    exact L35.rowFor_spor_resid hHe hCT ⟨hM12, hJ2, hHS⟩ G p w v L K h ⟨e⟩

end CFSG.ComponentClassification.HarrisLit
