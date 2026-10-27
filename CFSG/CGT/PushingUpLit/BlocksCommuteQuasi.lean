module

public import CFSG.CGT.PushingUpLit.BlocksCommuteSchur
public import CFSG.CGT.PushingUpLit.BlocksCommuteQuasi2

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_ne_bot_of_short {X : Subgroup G} (hX : IsShortGroup ↥X) : ⁅X, X⁆ ≠ ⊥ := by
  intro h
  refine blockU_ne_bot_of_short hX (le_bot_iff.mp ?_)
  exact h ▸ Subgroup.commutator_mono (oTwoIn_le X) le_rfl

theorem commutator_eq_bot_of_qs {X Y : Subgroup G} (hX : IsBlockOf X)
    (hq : IsQuasisimple (↥X ⧸ pCore 2 ↥X)) (hY : IsBlockOf Y) (hne : X ≠ Y) : ⁅X, Y⁆ = ⊥ := by
  have h1 := commutator_mem_pCore_of_qs hX hq hY hne
  have hN : X ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_of_commutator_mem hY h1
  have hR : ∀ x ∈ X, ∀ l ∈ Y, ⁅x, l⁆ ∈ oTwoIn Y := by
    intro x hx l hl
    rw [oTwoIn_eq_inf_pCore hY.1]
    refine Subgroup.mem_inf.2 ⟨?_, h1 x hx l hl⟩
    have := (Subgroup.mem_normalizer_iff.1 (hN hx) l).1 hl
    exact mul_mem this (inv_mem hl)
  have hU : ∀ x ∈ X, ∀ l ∈ Y, ⁅x, l⁆ ∈ blockU Y :=
    fun x hx => commutator_mem_blockU hY (hR x hx)
  have hperf := commutator_eq_self_of_qs hX.2 hq
  have hZ := perfect_acts_trivially hY hN hperf hR
  have hodd : ∀ a ∈ X, Odd (orderOf a) → a ∈ Subgroup.centralizer (Y : Set G) := by
    intro a ha hao
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hZY := commutator_mem_blockZ_of_odd hY hU hZ ha hao
    have h2 := commutator_eq_one_of_mem_blockZ hY hZY l hl
    exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine (eq_oTwoUpper_of_short hX.2).le.trans ?_
  exact (Subgroup.closure_le _).2 fun a ha => hodd a ha.1 ha.2

theorem commutator_eq_bot_of_qs' {X Y : Subgroup G} (hX : IsBlockOf X) (hY : IsBlockOf Y)
    (hq : IsQuasisimple (↥Y ⧸ pCore 2 ↥Y)) (hne : X ≠ Y) : ⁅X, Y⁆ = ⊥ := by
  rw [Subgroup.commutator_comm]
  exact commutator_eq_bot_of_qs hY hq hX hne.symm

theorem eq_of_le_of_isBlock {X Y : Subgroup G} (hX : IsBlockOf X) (hY : IsBlockOf Y)
    (hle : X ≤ Y) : X = Y := by
  by_contra hne
  rcases hX.2.quotient_type with hqX | hpX
  · have h := commutator_eq_bot_of_qs hX hqX hY hne
    have h2 : ⁅X, X⁆ = ⊥ := le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hle)
    exact commutator_ne_bot_of_short hX.2 h2
  rcases hY.2.quotient_type with hqY | hpY
  · have h := commutator_eq_bot_of_qs' hX hY hqY hne
    have h2 : ⁅X, X⁆ = ⊥ := le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hle)
    exact commutator_ne_bot_of_short hX.2 h2
  · have hle' : barImg X ≤ barImg Y := Subgroup.map_mono hle
    have hdvd : Nat.card ↥(barImg X) ∣ Nat.card ↥(barImg Y) := Subgroup.card_dvd_of_le hle'
    rw [card_barImg hX, card_barImg hY] at hdvd
    have hpq : Nat.card (↥X ⧸ pCore 2 ↥X) = Nat.card (↥Y ⧸ pCore 2 ↥Y) :=
      (Nat.prime_dvd_prime_iff_eq hpX hpY).1 hdvd
    have heq : barImg X = barImg Y := by
      refine Subgroup.eq_of_le_of_card_ge hle' ?_
      rw [card_barImg hX, card_barImg hY, hpq]
    have e : Y ≤ X := le_of_le_sup_pCore hY hX (le_sup_pCore_of_barImg_le heq.ge)
    exact hne (le_antisymm hle e)

end CFSG.CGT.PushingUpLit
