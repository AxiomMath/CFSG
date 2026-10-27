module

public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.RankThree.PartOne.F106.ConvOrdBound
public import CFSG.RankThree.PartOne.KS.Basic

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem center_eq_bot_of_mulEquiv {S G : Type*} [Group S] [Group G] (e : S ≃* G)
    (h : Subgroup.center G = ⊥) : Subgroup.center S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hcz : e z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  rw [h, Subgroup.mem_bot] at hcz
  rw [Subgroup.mem_bot]
  exact e.injective (hcz.trans (map_one e).symm)

theorem one_le_of_card_eq (K : Type) [Field K] [Finite K] {p e : ℕ} (hK : Nat.card K = p ^ e) :
    1 ≤ e := by
  by_contra h0
  have : e = 0 := by omega
  subst this
  have h1 := Finite.one_lt_card (α := K)
  rw [hK] at h1
  simp at h1

section Orders

@[expose] noncomputable def adjointQuotientEquiv (τ : Tag) (K : Type) [Field K] [Finite K] :
    AdjointQuotient τ K ≃* adjointGroup τ K :=
  (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := τ) (K := K))).trans
    QuotientGroup.quotientBot

theorem center_adjointQuotient_eq_bot (τ : Tag) (K : Type) [Field K] [Finite K] :
    Subgroup.center (AdjointQuotient τ K) = ⊥ :=
  center_eq_bot_of_mulEquiv (adjointQuotientEquiv τ K) center_adjointGroup_eq_bot

theorem card_mulAut_adjointQuotient_le (τ : Tag) (K : Type) [Field K] [Finite K] {b N : ℕ}
    (hout : Nat.card (Outer (adjointGroup τ K)) ≤ b)
    (hord : Nat.card (adjointGroup τ K) ≤ Nat.card K ^ N) :
    Nat.card (MulAut (AdjointQuotient τ K)) ≤ b * Nat.card K ^ N := by
  have hfin : Finite (MulAut (adjointGroup τ K)) :=
    Finite.of_injective (fun σ : MulAut (adjointGroup τ K) => (σ : adjointGroup τ K → _))
      DFunLike.coe_injective
  rw [Nat.card_congr (MulAut.congr (adjointQuotientEquiv τ K)).toEquiv,
    CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer (center_adjointGroup_eq_bot (τ := τ)
      (K := K)), mul_comm]
  exact Nat.mul_le_mul hout hord

theorem card_mulAut_adjointQuotient_E6_le (K : Type) [Field K] [Finite K] {p e : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p ^ e) :
    Nat.card (MulAut (AdjointQuotient .E6 K)) ≤ 6 * e * Nat.card K ^ 78 := by
  have he : 1 ≤ e := one_le_of_card_eq K hK
  obtain ⟨hd, -⟩ := ordinary_E_outer_order_Cartan_divisor .E6 (Or.inl rfl) Fact.out he K hK 3 2
    (Or.inl ⟨rfl, rfl, rfl⟩)
  refine card_mulAut_adjointQuotient_le .E6 K (b := 6 * e) (N := 78) ?_ ?_
  · exact (Nat.le_of_dvd (by positivity) hd).trans (le_of_eq (by ring))
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
    exact CFSG.RankThree.PartOne.F106.ordE6_le _

theorem card_mulAut_adjointQuotient_E7_le (K : Type) [Field K] [Finite K] {p e : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p ^ e) :
    Nat.card (MulAut (AdjointQuotient .E7 K)) ≤ 2 * e * Nat.card K ^ 133 := by
  have he : 1 ≤ e := one_le_of_card_eq K hK
  obtain ⟨hd, -⟩ := ordinary_E_outer_order_Cartan_divisor .E7 (Or.inr (Or.inl rfl)) Fact.out he K
    hK 2 1 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  refine card_mulAut_adjointQuotient_le .E7 K (b := 2 * e) (N := 133) ?_ ?_
  · exact (Nat.le_of_dvd (by positivity) hd).trans (le_of_eq (by ring))
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7]
    exact CFSG.RankThree.PartOne.F106.ordE7_le _

theorem card_mulAut_adjointQuotient_E8_le (K : Type) [Field K] [Finite K] {p e : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p ^ e) :
    Nat.card (MulAut (AdjointQuotient .E8 K)) ≤ e * Nat.card K ^ 248 := by
  have he : 1 ≤ e := one_le_of_card_eq K hK
  obtain ⟨hd, -⟩ := ordinary_E_outer_order_Cartan_divisor .E8 (Or.inr (Or.inr rfl)) Fact.out he K
    hK 1 1 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  refine card_mulAut_adjointQuotient_le .E8 K (b := e) (N := 248) ?_ ?_
  · exact (Nat.le_of_dvd (by positivity) hd).trans (le_of_eq (by ring))
  · rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8]
    exact CFSG.RankThree.PartOne.F106.ordE8_le _

end Orders

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
