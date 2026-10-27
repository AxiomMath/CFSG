module

public import CFSG.ClassicalInvolution.Q3.Q3T6AutInn
public import CFSG.ClassicalInvolution.SmallCases.NDB5dAct

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3T6
open scoped MatrixGroups commutatorElement

private def sl2Fourth : Subgroup SL(2, ZMod 3) where
  carrier := {g | g ^ 4 = 1}
  one_mem' := one_pow 4
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide +kernel
  inv_mem' := by
    intro a ha
    revert a
    decide +kernel

private theorem comm_mem_sl2Fourth : ∀ a b : SL(2, ZMod 3), ⁅a, b⁆ ^ 4 = 1 := by
  decide +kernel

private theorem comm_fourth_central : ∀ a b : SL(2, ZMod 3), a ^ 4 = 1 → b ^ 4 = 1 →
    ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = -1 := by
  decide +kernel

theorem derivedSeries_two_sl2Three_le_center :
    derivedSeries SL(2, ZMod 3) 2 ≤ Subgroup.center SL(2, ZMod 3) := by
  have h1 : derivedSeries SL(2, ZMod 3) 1 ≤ sl2Fourth := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact comm_mem_sl2Fourth a b
  rw [derivedSeries_succ]
  refine (Subgroup.commutator_mono h1 h1).trans ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Aut.mem_center_sl2Three_iff]
  exact comm_fourth_central a b ha hb

theorem derivedSeries_three_mulAut_sl2Three :
    derivedSeries (MulAut SL(2, ZMod 3)) 3 = ⊥ := by
  have hcomm : ∀ x y : MulAut SL(2, ZMod 3), ⁅x, y⁆ ∈ inn3 := by
    intro x y
    have hcard : Nat.card (MulAut SL(2, ZMod 3) ⧸ inn3) = 2 := by
      rw [← Subgroup.index.eq_1 inn3]
      exact inn3_index
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic (MulAut SL(2, ZMod 3) ⧸ inn3) := isCyclic_of_prime_card hcard
    have hc : ∀ a b : MulAut SL(2, ZMod 3) ⧸ inn3, a * b = b * a := fun a b =>
      (IsCyclic.commGroup (α := MulAut SL(2, ZMod 3) ⧸ inn3)).mul_comm a b
    have h1 : (QuotientGroup.mk' inn3) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hc _ _)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hD1 : derivedSeries (MulAut SL(2, ZMod 3)) 1 ≤ inn3 := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x y
  have hinn : inn3 = (⊤ : Subgroup SL(2, ZMod 3)).map
      (MulAut.conj : SL(2, ZMod 3) →* MulAut SL(2, ZMod 3)) := by
    unfold inn3
    exact MonoidHom.range_eq_map _
  have hD2 : derivedSeries (MulAut SL(2, ZMod 3)) 2 ≤
      (derivedSeries SL(2, ZMod 3) 1).map
        (MulAut.conj : SL(2, ZMod 3) →* MulAut SL(2, ZMod 3)) := by
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono hD1 hD1).trans ?_
    rw [hinn, ← Subgroup.map_commutator, derivedSeries_one, commutator_def]
  rw [eq_bot_iff, derivedSeries_succ]
  refine (Subgroup.commutator_mono hD2 hD2).trans ?_
  rw [← Subgroup.map_commutator, ← derivedSeries_succ]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := hx
  have hgc := derivedSeries_two_sl2Three_le_center hg
  have : (MulAut.conj g : MulAut SL(2, ZMod 3)) = 1 := by
    have : g ∈ (MulAut.conj : SL(2, ZMod 3) →* MulAut SL(2, ZMod 3)).ker := by
      rw [Aut.ker_conj_sl2Three]
      exact hgc
    exact this
  rw [Subgroup.mem_bot]
  exact this

section Act

variable {G : Type} [Group G] [Finite G]

theorem exists_sl2Three_action {J : Subgroup G} {z : G} (hJ : IsClassicalMember3 J z) :
    ∃ ρ : Subgroup.normalizer (J : Set G) →* MulAut SL(2, ZMod 3),
      ∀ g, ρ g = 1 → (g : G) ∈ trivialOnQuot J := by
  obtain ⟨e⟩ : Nonempty (↥J ⧸ CFSG.oddCore J ≃* SL(2, ZMod 3)) := hJ.nonempty_equiv
  refine ⟨(NDB.WC.autCongr e).comp (tl3Act J), fun g hg => ?_⟩
  rw [MonoidHom.comp_apply, NDB.WC.autCongr_eq_one_iff] at hg
  exact ⟨g.2, (tl3Act_eq_one_iff J g).mp hg⟩

theorem mem_trivialOnQuot_of_derived3 {J : Subgroup G} {z : G} (hJ : IsClassicalMember3 J z)
    {X : Subgroup G} (hXJ : X ≤ Subgroup.normalizer (J : Set G)) {x a : G} (hx : x ∈ X)
    (hx2 : x * x = 1) (ha : a ∈ X) (ha3 : (⟨a, ha⟩ : X) ∈ derivedSeries X 3)
    (hodd : Odd (orderOf (a⁻¹ * x))) : x ∈ trivialOnQuot J := by
  obtain ⟨ρ, hρ1⟩ := exists_sl2Three_action hJ
  set φ := ρ.comp (Subgroup.inclusion hXJ) with hφ
  have hφa : φ ⟨a, ha⟩ = 1 := by
    have h1 : φ ⟨a, ha⟩ ∈ (derivedSeries X 3).map φ := ⟨_, ha3, rfl⟩
    have h2 := map_derivedSeries_le_derivedSeries φ 3 h1
    rwa [derivedSeries_three_mulAut_sl2Three, Subgroup.mem_bot] at h2
  set b : X := (⟨a, ha⟩ : X)⁻¹ * ⟨x, hx⟩ with hb
  have hφx : φ ⟨x, hx⟩ = φ b := by
    rw [hb, map_mul, map_inv, hφa, inv_one, one_mul]
  have hob : Odd (orderOf (φ b)) := by
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd φ b)
    rw [← Subgroup.orderOf_coe]
    exact hodd
  have h2 : orderOf (φ ⟨x, hx⟩) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, pow_two]
    have : (⟨x, hx⟩ : X) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  rw [hφx] at h2
  have h1 : orderOf (φ b) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hob
      exact absurd hob (by decide)
  rw [orderOf_eq_one_iff, ← hφx] at h1
  exact hρ1 _ h1

end Act

end CFSG.ClassicalInvolution.Q3.Q3AM
