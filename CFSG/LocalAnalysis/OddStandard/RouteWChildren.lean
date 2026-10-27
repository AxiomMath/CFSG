module

public import CFSG.LocalAnalysis.OddStandard.OrderForm
public import CFSG.Blueprint.OddStandardExact

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def ChildLargeAltW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    (∃ n : ℕ, 8 ≤ n ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))) →
    AltOutcome G ∨ OddLieType G ∨ IsSporadic G .McL ∨ IsSporadic G .Ly

@[expose] def ChildL34W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    LieModel (L ⧸ center L) .PSL 3 2 2 →
    OddLieType G ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .ONan

@[expose] def ChildHeW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    IsSporadic (L ⧸ center L) .He → OddLieType G

theorem odd_standard_of_childrenW (h1 : ChildLargeAltW) (h2 : ChildSmallAltOdd)
    (h3 : ChildSmallAltEven) (h4 : ChildOddLie) (h5 : ChildL34W) (h6 : ChildHeW)
    (G : Type) [Group G] [Finite G] [hs : IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (htype : Recognition.Exact.OddStandardType (L ⧸ center L)) : OddOutcome G := by
  have hS : StandardSetting G L := ⟨hs, hnonab, hK, hL⟩
  unfold OddOutcome
  rcases htype with ⟨n, hn, e⟩ | hlie | hl34 | hhe
  · rcases le_or_gt 8 n with h8 | h8
    · have r := h1 G L hS ⟨n, h8, e⟩
      tauto
    · rcases Nat.even_or_odd (Nat.card (center L)) with hev | hodd
      · exact .inr (.inl (h3 G L hS ⟨n, hn, by omega, e⟩ hev))
      · have r := h2 G L hS ⟨n, hn, by omega, e⟩ hodd
        tauto
  · have r := h4 G L hS hlie
    tauto
  · have r := h5 G L hS hl34
    tauto
  · exact .inr (.inl (h6 G L hS hhe))

theorem odd_standard_order_of_childrenW
    (h1 : ChildLargeAltW) (h2 : ChildSmallAltOdd)
    (h3 : ChildSmallAltEven) (h4 : ChildOddLie) (h5 : ChildL34W) (h6 : ChildHeW)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (htype : Recognition.Exact.OddStandardType (L ⧸ center L)) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card G ∈ lieOrdersChar p) ∨
      Nat.card G ∈ standardComponentOddSporadicOrders :=
  orderForm_of_oddOutcome (odd_standard_of_childrenW h1 h2 h3 h4 h5 h6 G hnonab hK L hL htype)

end CFSG.OddStandard
