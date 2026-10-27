module

public import CFSG.LocalAnalysis.SectionRank.SimpleList
public import CFSG.LocalAnalysis.SectionRank.Sporadic.B
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co1
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi22
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi23
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi24prime
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HN
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Ly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Suz
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Th
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.SectionRank CFSG.Blueprint

section Exclusions

variable {G : Type} [Group G] [Finite G] (hSQT : CFSG.IsStronglyQuasithin G) (A : Subgroup G)
  [A.Normal] (hAZ : A ≤ Subgroup.center G)

include hSQT hAZ

theorem sectionRank_B_central_quotient_exclusion
    : IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .B) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ B_elementary_three_rank_four

theorem sectionRank_Co1_Co2_central_quotient_exclusion
    :
    IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .Co1) ∧
      IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .Co2) :=
  ⟨central_quotient_exclusion_of_three_rank_four hSQT A hAZ Co1_elementary_three_rank_four,
    central_quotient_exclusion_of_three_rank_four hSQT A hAZ Co2_elementary_three_rank_four⟩

theorem sectionRank_Co3_central_quotient_exclusion :
    IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .Co3) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ Co3_elementary_three_rank_four

theorem sectionRank_Fi22_central_quotient_exclusion :
    IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .Fi22) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ Fi22_elementary_three_rank_four

theorem sectionRank_Fi23_central_quotient_exclusion :
    IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .Fi23) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ Fi23_elementary_three_rank_four

theorem sectionRank_Fi24prime_central_quotient_exclusion :
    IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .Fi24Prime) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ Fi24prime_elementary_three_rank_four

theorem sectionRank_HN_central_quotient_exclusion
    : IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .HN) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ HN_elementary_three_rank_four

theorem sectionRank_Ly_central_quotient_exclusion
    : IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .Ly) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ Ly_elementary_three_rank_four

theorem sectionRank_McL_central_quotient_exclusion :
    IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .McL) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ McL_elementary_three_rank_four

theorem sectionRank_ON_central_quotient_exclusion :
    IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .ONan) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ ON_elementary_three_rank_four

theorem sectionRank_Suz_central_quotient_exclusion :
    IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .Suz) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ Suz_elementary_three_rank_four

theorem sectionRank_Th_central_quotient_exclusion
    : IsEmpty (G ⧸ A ≃* NativeSporadic.Carrier .Th) :=
  central_quotient_exclusion_of_three_rank_four hSQT A hAZ Th_elementary_three_rank_four

end Exclusions

theorem unique_SQT_sporadic_eleven_candidate_restriction
    {Q : Type} [Group Q] [Finite Q]
    [Nontrivial Q] (hSQT : CFSG.IsStronglyQuasithin Q) (hrep : NativeSporadic.SporadicRep Q) :
    ∃ s : TauCeti.SporadicName, s ∈ sqtkSporadicNames ∧
      Nonempty (Q ≃* NativeSporadic.Carrier s) := by
  obtain ⟨s, ⟨e⟩⟩ := hrep
  refine ⟨s, ?_, ⟨e⟩⟩
  by_contra hs
  have e0 : Q ⧸ (⊥ : Subgroup Q) ≃* NativeSporadic.Carrier s := QuotientGroup.quotientBot.trans e
  have hnt : Nontrivial (Q ⧸ (⊥ : Subgroup Q)) :=
    (QuotientGroup.quotientBot (G := Q)).symm.injective.nontrivial
  have hodd : Odd (Nat.card (⊥ : Subgroup Q)) := by
    rw [Subgroup.card_bot]
    exact odd_one
  cases s with
  | M11 | M12 | M22 | M23 | M24 | J1 | J2 | J4 | HS | He | Ru =>
    exact hs (by simp [sqtkSporadicNames])
  | J3 => exact (J3_odd_central_quotient_exclusion hSQT ⊥ bot_le hodd).false e0
  | M => exact (M_nontrivial_central_quotient_exclusion hSQT ⊥ bot_le hnt).false e0
  | McL => exact (sectionRank_McL_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | Suz => exact (sectionRank_Suz_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | ONan => exact (sectionRank_ON_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | Co1 => exact (sectionRank_Co1_Co2_central_quotient_exclusion hSQT ⊥ bot_le).1.false e0
  | Co2 => exact (sectionRank_Co1_Co2_central_quotient_exclusion hSQT ⊥ bot_le).2.false e0
  | Co3 => exact (sectionRank_Co3_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | Fi22 => exact (sectionRank_Fi22_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | Fi23 => exact (sectionRank_Fi23_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | Fi24Prime => exact (sectionRank_Fi24prime_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | HN => exact (sectionRank_HN_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | Ly => exact (sectionRank_Ly_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | Th => exact (sectionRank_Th_central_quotient_exclusion hSQT ⊥ bot_le).false e0
  | B => exact (sectionRank_B_central_quotient_exclusion hSQT ⊥ bot_le).false e0

end CFSG.QuasithinUnique.Setup.X1
