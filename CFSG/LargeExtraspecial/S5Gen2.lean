module

public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalInvolution.Basic

public section

namespace CFSG.LargeExtraspecial.S5

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem eq_bot_or_eq_of_isSubnormal_of_isSimpleGroup {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) (hB : IsSimpleGroup B) : A = ⊥ ∨ A = B := by
  exact CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup h hB

theorem relIndex_ne_zero_of_finite' [Finite X] (H K : Subgroup X) : H.relIndex K ≠ 0 :=
  (H.subgroupOf K).index_ne_zero_of_finite

theorem ne_bot_of_isQuasisimple {A : Subgroup X} (hA : CFSG.Open.IsQuasisimple A) : A ≠ ⊥ := by
  intro h
  have : Nontrivial A := CFSG.ComponentClassification.Quasisimple.nontrivial hA
  exact (A.nontrivial_iff_ne_bot.mp this) h

theorem not_isSolvable_of_isQuasisimple {A : Subgroup X} (hA : CFSG.Open.IsQuasisimple A) :
    ¬ Group.IsSolvable A :=
  CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hA

theorem commutator_eq_self_of_isQuasisimple {A : Subgroup X} (hA : CFSG.Open.IsQuasisimple A) :
    ⁅A, A⁆ = A := by
  rw [← map_subtype_commutator, hA.1, ← MonoidHom.range_eq_map, range_subtype]

theorem commutator_mem_of_relIndex_le_two [Finite X] {M₀ Y : Subgroup X}
    (hidx : M₀.relIndex Y ≤ 2) {a b : X} (ha : a ∈ Y) (hb : b ∈ Y) : ⁅a, b⁆ ∈ M₀ := by
  have hpos : M₀.relIndex Y ≠ 0 := (relIndex_ne_zero_of_finite' _ _)
  rcases (show M₀.relIndex Y = 1 ∨ M₀.relIndex Y = 2 by omega) with h1 | h2
  · exact relIndex_eq_one.mp h1
      (Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb))
  · have h2' : (M₀.subgroupOf Y).index = 2 := h2
    have key : ⁅(⟨a, ha⟩ : Y), ⟨b, hb⟩⁆ ∈ M₀.subgroupOf Y := by
      rw [commutatorElement_def, show (⟨a, ha⟩ : Y) * ⟨b, hb⟩ * (⟨a, ha⟩ : Y)⁻¹ *
          (⟨b, hb⟩ : Y)⁻¹ = ((⟨a, ha⟩ : Y) * ⟨b, hb⟩) * ((⟨a, ha⟩ : Y)⁻¹ * (⟨b, hb⟩ : Y)⁻¹) by
          group, mul_mem_iff_of_index_two h2', mul_mem_iff_of_index_two h2',
        mul_mem_iff_of_index_two h2', inv_mem_iff, inv_mem_iff]
    rw [mem_subgroupOf] at key
    simpa [commutatorElement_def] using key

theorem commutator_le_of_relIndex_le_two [Finite X] {M₀ Y : Subgroup X}
    (hidx : M₀.relIndex Y ≤ 2) : ⁅Y, Y⁆ ≤ M₀ :=
  commutator_le.mpr fun _ ha _ hb => commutator_mem_of_relIndex_le_two hidx ha hb

theorem isSolvable_of_card_le_two {A : Type*} [Group A] [Finite A] (h : Nat.card A ≤ 2) :
    Group.IsSolvable A := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  rcases (show Nat.card A = 1 ∨ Nat.card A = 2 by omega) with h1 | h2
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic A := isCyclic_of_prime_card h2
    exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b

theorem eq_of_isSubnormal_of_isQuasisimple [Finite X] {K M₀ Y : Subgroup X}
    (hK : CFSG.Open.IsSubnormal K Y) (hq : CFSG.Open.IsQuasisimple K) (hM : M₀ ≤ Y)
    (hMs : IsSimpleGroup M₀) (hidx : M₀.relIndex Y ≤ 2) : K = M₀ := by
  have hKY := CFSG.ClassicalInvolution.isSubnormal_le hK
  have hsub := CFSG.ClassicalInvolution.isSubnormal_inf hK M₀
  rw [inf_eq_right.mpr hM] at hsub
  rcases eq_bot_or_eq_of_isSubnormal_of_isSimpleGroup hsub hMs with h0 | h1
  · exfalso
    have hcard : Nat.card K ≤ 2 := by
      have e1 : M₀.relIndex K = Nat.card K := by
        rw [← inf_relIndex_right, inf_comm, h0, relIndex_bot_left]
      have e2 : M₀.relIndex K ≤ M₀.relIndex Y :=
        relIndex_le_of_le_right hKY (relIndex_ne_zero_of_finite' _ _)
      omega
    exact not_isSolvable_of_isQuasisimple hq (isSolvable_of_card_le_two hcard)
  · have hMK : M₀ ≤ K := h1 ▸ inf_le_left
    refine le_antisymm ?_ hMK
    calc K = ⁅K, K⁆ := (commutator_eq_self_of_isQuasisimple hq).symm
      _ ≤ ⁅Y, Y⁆ := commutator_mono hKY hKY
      _ ≤ M₀ := commutator_le_of_relIndex_le_two hidx

theorem exists_mul_of_relIndex_le_two [Finite X] {E M₀ Y : Subgroup X} (hEY : E ≤ Y)
    (hgen : Y ≤ closure {u | ∃ x ∈ Y, ∃ e ∈ E, u = x * e * x⁻¹})
    (hMn : (M₀.subgroupOf Y).Normal) (hidx : M₀.relIndex Y ≤ 2) :
    ∀ y ∈ Y, ∃ k ∈ M₀, ∃ e ∈ E, y = k * e := by
  intro y hy
  by_cases hEM : E ≤ M₀
  · have hYM : Y ≤ M₀ := by
      refine hgen.trans ((closure_le M₀).mpr ?_)
      rintro _ ⟨x, hx, e, he, rfl⟩
      have := hMn.conj_mem ⟨e, hEY he⟩ (show (⟨e, hEY he⟩ : Y) ∈ M₀.subgroupOf Y from hEM he)
        ⟨x, hx⟩
      rw [mem_subgroupOf] at this
      simpa using this
    exact ⟨y, hYM hy, 1, one_mem _, (mul_one y).symm⟩
  · obtain ⟨e₀, he₀, he₀M⟩ := IsConcreteLE.not_le_iff_exists.mp hEM
    have hpos : M₀.relIndex Y ≠ 0 := (relIndex_ne_zero_of_finite' _ _)
    have h2 : (M₀.subgroupOf Y).index = 2 := by
      have h1 : M₀.relIndex Y ≠ 1 := fun h => he₀M (relIndex_eq_one.mp h (hEY he₀))
      change M₀.relIndex Y = 2
      omega
    by_cases hyM : y ∈ M₀
    · exact ⟨y, hyM, 1, one_mem _, (mul_one y).symm⟩
    · refine ⟨y * e₀⁻¹, ?_, e₀, he₀, by group⟩
      have hmem : (⟨y, hy⟩ : Y) * (⟨e₀, hEY he₀⟩ : Y)⁻¹ ∈ M₀.subgroupOf Y := by
        rw [mul_mem_iff_of_index_two h2, inv_mem_iff]
        exact iff_of_false hyM he₀M
      rw [mem_subgroupOf] at hmem
      simpa using hmem

theorem relIndex_inf_le_two [Finite X] {E M₀ Y : Subgroup X} (hEY : E ≤ Y)
    (hidx : M₀.relIndex Y ≤ 2) : (E ⊓ M₀).relIndex E ≤ 2 := by
  rw [inf_comm, inf_relIndex_right]
  exact (relIndex_le_of_le_right hEY (relIndex_ne_zero_of_finite' _ _)).trans hidx

end CFSG.LargeExtraspecial.S5
