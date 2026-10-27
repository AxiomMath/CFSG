module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem pairwise_commuting_centerless_subgroups_independent
    {G : Type*} [Group G] {Index : Type*} (factors : Index → Subgroup G)
    (hcommute : Pairwise (fun first second => factors first ≤
      Subgroup.centralizer (factors second : Set G)))
    (hcenterless : ∀ index, Subgroup.center (factors index) = ⊥) : iSupIndep factors := by
  apply iSupIndep_def.mpr
  intro index
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro element helement
  have hotherCentralizes : (⨆ otherIndex, ⨆ (_ : otherIndex ≠ index), factors otherIndex) ≤
      Subgroup.centralizer (factors index : Set G) := by
    apply iSup_le
    intro otherIndex
    apply iSup_le
    intro hdistinct
    exact hcommute hdistinct
  have hinternalCenter : (⟨element, helement.1⟩ : factors index) ∈
      Subgroup.center (factors index) := by
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hotherCentralizes helement.2) other.val other.property
  have hinternalOne := Subgroup.mem_bot.mp (hcenterless index ▸ hinternalCenter)
  exact congrArg Subtype.val hinternalOne

theorem cyclic_prime_order_subgroup_elemAbelian
    {G : Type*} [Group G] (prime : ℕ) (element : G) (horder : orderOf element = prime) :
    IsElemAbelian prime (Subgroup.zpowers element) := by
  refine ⟨inferInstance, ?_⟩
  intro value hvalue
  obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hvalue
  rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast,
    ← horder, pow_orderOf_eq_one, one_zpow]

theorem independent_prime_divisible_commuting_factors_card_le_rank
    {G : Type*} [Group G] [Finite G] {Index : Type*} [Fintype Index]
    (prime : ℕ) (hprime : prime.Prime) (factors : Index → Subgroup G)
    (hindependent : iSupIndep factors)
    (hcommute : Pairwise (fun first second => factors first ≤
      Subgroup.centralizer (factors second : Set G)))
    (hdivides : ∀ index, prime ∣ Nat.card (factors index)) :
    Fintype.card Index ≤ pRank prime (⊤ : Subgroup G) := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  have hlines : ∀ index, ∃ element : factors index, orderOf element = prime :=
    fun index => exists_prime_orderOf_dvd_card' prime (hdivides index)
  choose elements horders using hlines
  let lines := fun index => Subgroup.zpowers ((elements index).val)
  have hlineLe : ∀ index, lines index ≤ factors index :=
    fun index => Subgroup.zpowers_le.mpr (elements index).property
  have hlineIndependent : iSupIndep lines := hindependent.mono hlineLe
  have hlineCommute : Pairwise (fun first second => ∀ firstElement secondElement : G,
      firstElement ∈ lines first → secondElement ∈ lines second →
        Commute firstElement secondElement) := by
    intro first second hdistinct firstElement secondElement hfirst hsecond
    exact (Subgroup.mem_centralizer_iff.mp
      (hcommute hdistinct (hlineLe first hfirst)) secondElement (hlineLe second hsecond)).symm
  let productMap := Subgroup.noncommPiCoprod hlineCommute
  have hproductInjective : Function.Injective productMap :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hlineIndependent
  have hlineElementary : ∀ index, IsElemAbelian prime (lines index) := by
    intro index
    exact cyclic_prime_order_subgroup_elemAbelian prime (elements index).val
      ((Subgroup.orderOf_coe _).trans (horders index))
  have hproductElementary : IsElemAbelian prime (⊤ : Subgroup ((index : Index) → lines index)) := by
    refine ⟨?_, ?_⟩
    · apply isMulCommutative_iff.mpr
      intro first second
      apply Subtype.ext
      funext index
      exact isMulCommutative_iff.mp (hlineElementary index).1 (first.val index) (second.val index)
    · intro element _helement
      funext index
      apply Subtype.ext
      exact (hlineElementary index).2 (element index).val (element index).property
  have himageElementary := elementary_map_injective prime (⊤ : Subgroup ((index : Index) → lines index))
    productMap hproductInjective hproductElementary
  have himageCard : Nat.card (Subgroup.map productMap ⊤) = prime ^ Fintype.card Index := by
    rw [Subgroup.card_map_of_injective hproductInjective, Subgroup.card_top, Nat.card_pi]
    have hlineCard : ∀ index, Nat.card (lines index) = prime := by
      intro index
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, horders]
    simp only [hlineCard, Finset.prod_const, Finset.card_univ]
  apply le_csSup (pRank_set_bddAbove prime hprime.one_lt (⊤ : Subgroup G))
  exact ⟨Subgroup.map productMap ⊤, le_top, himageElementary, himageCard⟩

theorem commuting_centerless_prime_divisible_factors_card_le_rank
    {G : Type*} [Group G] [Finite G] {Index : Type*} [Fintype Index]
    (prime : ℕ) (hprime : prime.Prime) (factors : Index → Subgroup G)
    (hcommute : Pairwise (fun first second => factors first ≤
      Subgroup.centralizer (factors second : Set G)))
    (hcenterless : ∀ index, Subgroup.center (factors index) = ⊥)
    (hdivides : ∀ index, prime ∣ Nat.card (factors index)) :
    Fintype.card Index ≤ pRank prime (⊤ : Subgroup G) :=
  independent_prime_divisible_commuting_factors_card_le_rank prime hprime factors
    (pairwise_commuting_centerless_subgroups_independent factors hcommute hcenterless)
    hcommute hdivides

end CFSG.RankThreeCoreUniqueness.Helpers
