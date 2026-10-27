module

public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup Equiv Equiv.Perm

theorem alternatingGroup_le_of_cycle_of_threeCycle {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α = 7) (R : Subgroup (Perm α)) {c g : Perm α} (hc : c.IsCycle)
    (hcs : c.support = Finset.univ) (hcR : c ∈ R) (hg : g.IsThreeCycle) (hgR : g ∈ R) :
    alternatingGroup α ≤ R := by
  have hpre : MulAction.IsPretransitive R α := by
    refine ⟨fun a b => ?_⟩
    have ha : c a ≠ a := by
      have : a ∈ c.support := by rw [hcs]; exact Finset.mem_univ a
      exact mem_support.1 this
    have hb : c b ≠ b := by
      have : b ∈ c.support := by rw [hcs]; exact Finset.mem_univ b
      exact mem_support.1 this
    obtain ⟨i, hi⟩ := hc.exists_pow_eq ha hb
    exact ⟨⟨c ^ i, R.pow_mem hcR i⟩, hi⟩
  have hprim : MulAction.IsPreprimitive R α := by
    refine MulAction.IsPreprimitive.of_prime_card ?_
    rw [Nat.card_eq_fintype_card, hα]
    exact Nat.prime_seven
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hg hgR

theorem quotient_equiv_alternatingGroup {N : Type*} [Group N] [Finite N] {α : Type*} [Fintype α]
    [DecidableEq α] (hα : Fintype.card α = 7) (ρ : N →* Perm α) (F : Subgroup N) [F.Normal]
    (hF : F ≤ ρ.ker) (hFcard : Nat.card F = 16) (hN : Nat.card N ≤ 40320) {g7 g3 : N}
    (h7 : (ρ g7).IsCycle) (h7s : (ρ g7).support = Finset.univ) (h3 : (ρ g3).IsThreeCycle) :
    Nonempty (N ⧸ F ≃* alternatingGroup α) := by
  have hAR : alternatingGroup α ≤ ρ.range :=
    alternatingGroup_le_of_cycle_of_threeCycle hα ρ.range h7 h7s ⟨g7, rfl⟩ h3 ⟨g3, rfl⟩
  have hAcard : Nat.card (alternatingGroup α) = 2520 := by
    have : Nontrivial α := by
      rw [← Fintype.one_lt_card_iff_nontrivial, hα]
      norm_num
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hα]
    norm_num [Nat.factorial]
  have hRge : 2520 ≤ Nat.card ρ.range := hAcard ▸ Subgroup.card_le_of_le hAR
  have hkge : 16 ≤ Nat.card ρ.ker := hFcard ▸ Subgroup.card_le_of_le hF
  have hprod := Subgroup.card_ker_mul_card_range ρ
  have h1 : 16 * 2520 ≤ Nat.card ρ.ker * Nat.card ρ.range := Nat.mul_le_mul hkge hRge
  have hkle : Nat.card ρ.ker ≤ 16 := by
    by_contra hcon
    push Not at hcon
    have : 17 * 2520 ≤ Nat.card ρ.ker * Nat.card ρ.range := Nat.mul_le_mul hcon hRge
    omega
  have hRle : Nat.card ρ.range ≤ 2520 := by
    by_contra hcon
    push Not at hcon
    have : 16 * 2521 ≤ Nat.card ρ.ker * Nat.card ρ.range := Nat.mul_le_mul hkge hcon
    omega
  have hker : F = ρ.ker := Subgroup.eq_of_le_of_card_ge hF (by rw [hFcard]; exact hkle)
  have hrange : ρ.range = alternatingGroup α :=
    (Subgroup.eq_of_le_of_card_ge hAR (by rw [hAcard]; exact hRle)).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr hrange))⟩

end CFSG.EvenSporadicStandard.M23Std
