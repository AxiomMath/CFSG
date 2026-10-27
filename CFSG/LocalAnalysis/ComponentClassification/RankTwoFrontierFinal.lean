module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFrontierLeaves
public import Certificates.Certificate15104
public import Certificates.Certificate15107
public import Certificates.Certificate15121
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuH1Final
import CFSG.Sporadic.SuzRecog.MixedCell
import CFSG.Sporadic.SuzRecog.SuzLeaf
import CFSG.Sporadic.J2
import CFSG.Sporadic.Suz.Simple
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.Ru
import CFSG.Sporadic.Co1

public section

namespace CFSG.ComponentClassification.RankTwoStandard

open CFSG.Blueprint

theorem card_mem_of_isSporadic
    {G : Type} [Group G]
    (h : NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .Suz ∨
      NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Ru ∨
      NativeSporadic.IsSporadic G .Co1) :
    Nat.card G ∈ Open.standardComponentRankTwoSporadicOrders := by
  have key : ∀ s : TauCeti.SporadicName, NativeSporadic.IsSporadic G s →
      Nat.card G = Nat.card (NativeSporadic.Carrier s) := fun s h => by
    obtain ⟨e⟩ := h
    exact Nat.card_congr e.toEquiv
  rcases h with h | h | h | h | h
  · rw [key _ h, show Nat.card (NativeSporadic.Carrier .J2) = 604800 from
      CFSG.Sporadic.J2.card_J2]
    simp [Open.standardComponentRankTwoSporadicOrders, Open.standardComponentOrderJ2]
  · rw [key _ h, show Nat.card (NativeSporadic.Carrier .Suz) = 448345497600 from
      CFSG.Sporadic.Suz.card_Suz]
    simp [Open.standardComponentRankTwoSporadicOrders]
  · rw [key _ h, show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from
      CFSG.Sporadic.He.card_He]
    simp [Open.standardComponentRankTwoSporadicOrders, Open.standardComponentOrderHe]
  · rw [key _ h, show Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 from
      CFSG.Sporadic.Ru.card_Ru]
    simp [Open.standardComponentRankTwoSporadicOrders]
  · rw [key _ h, show Nat.card (NativeSporadic.Carrier .Co1) = 4157776806543360000 from
      CFSG.Sporadic.Co1.card_Co1]
    simp [Open.standardComponentRankTwoSporadicOrders]


theorem ct_rank_two_standard_recognition_models
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Catalog G) (L : Subgroup G) (hL : Open.standardComponentIsStandard L)
    (hrank : 2 ≤ Open.pRank 2 (Subgroup.centralizer (L : Set G))) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .Suz ∨
        NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Ru ∨
        NativeSporadic.IsSporadic G .Co1) :=
  ct_rank_two_standard_recognition_of_leaves GMS78.ruH1Stmt
      Sporadic.SuzRecog.MixedCell.mixedCellDichotomy G
    hnonab hK L hL hrank

theorem ct_rank_two_standard_recognition_orders
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Catalog G) (L : Subgroup G) (hL : Open.standardComponentIsStandard L)
    (hrank : 2 ≤ Open.pRank 2 (Subgroup.centralizer (L : Set G))) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      Nat.card G ∈ Open.standardComponentRankTwoSporadicOrders :=
  (ct_rank_two_standard_recognition_models G hnonab hK L hL hrank).imp_right
    card_mem_of_isSporadic

end CFSG.ComponentClassification.RankTwoStandard
