module

public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup Equiv Equiv.Perm

theorem alternatingGroup_le_of_five_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (R : Subgroup (Perm α)) {c g h : Perm α} {p : α}
    (hc : c.IsCycle) (hcp : c p = p) (hcs : ∀ x, x ≠ p → c x ≠ x) (hcR : c ∈ R)
    (hg : g.IsThreeCycle) (hgR : g ∈ R) (hhR : h ∈ R) (hhp : h p ≠ p) :
    alternatingGroup α ≤ R := by
  have hto : ∀ a : α, ∃ r ∈ R, r a = p := by
    intro a
    by_cases ha : a = p
    · exact ⟨1, R.one_mem, by simp [ha]⟩
    · have hha : c (h p) ≠ h p := hcs _ hhp
      have hca : c a ≠ a := hcs _ ha
      obtain ⟨i, hi⟩ := hc.exists_pow_eq hha hca
      refine ⟨(c ^ i * h)⁻¹, R.inv_mem (R.mul_mem (R.pow_mem hcR i) hhR), ?_⟩
      have : (c ^ i * h) p = a := by simpa using hi
      rw [Perm.inv_eq_iff_eq]
      exact this.symm
  have hrest : ∀ u v : α, u ≠ p → v ≠ p → ∃ s ∈ R, s p = p ∧ s u = v := by
    intro u v hu hv
    obtain ⟨i, hi⟩ := hc.exists_pow_eq (hcs u hu) (hcs v hv)
    refine ⟨c ^ i, R.pow_mem hcR i, ?_, hi⟩
    exact (Perm.pow_apply_eq_self_of_apply_eq_self hcp i)
  have h2 : MulAction.IsMultiplyPretransitive R α 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c' d hab hcd
    obtain ⟨r1, hr1, hr1a⟩ := hto a
    obtain ⟨r2, hr2, hr2c⟩ := hto c'
    have hb1 : r1 b ≠ p := by
      intro h1
      exact hab (r1.injective (by rw [h1, hr1a]))
    have hd2 : r2 d ≠ p := by
      intro h1
      exact hcd (r2.injective (by rw [h1, hr2c]))
    obtain ⟨s, hs, hsp, hsb⟩ := hrest _ _ hb1 hd2
    refine ⟨⟨r2⁻¹ * s * r1, R.mul_mem (R.mul_mem (R.inv_mem hr2) hs) hr1⟩, ?_, ?_⟩
    · show (r2⁻¹ * s * r1) a = c'
      simp only [Perm.mul_apply, hr1a, hsp]
      rw [Perm.inv_eq_iff_eq]
      exact hr2c.symm
    · show (r2⁻¹ * s * r1) b = d
      simp only [Perm.mul_apply, hsb]
      simp
  have hprim : MulAction.IsPreprimitive R α :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hg hgR

theorem quotient_equiv_alternatingGroup_six {N : Type*} [Group N] [Finite N] {α : Type*}
    [Fintype α] [DecidableEq α] (hα : Fintype.card α = 6) (ρ : N →* Perm α) (F : Subgroup N)
    [F.Normal] (hF : F ≤ ρ.ker) (hFcard : Nat.card F = 16) (hN : Nat.card N ≤ 5760)
    {c g h : N} {p : α} (hc : (ρ c).IsCycle) (hcp : ρ c p = p) (hcs : ∀ x, x ≠ p → ρ c x ≠ x)
    (hg : (ρ g).IsThreeCycle) (hhp : ρ h p ≠ p) :
    Nonempty (N ⧸ F ≃* alternatingGroup α) := by
  have hAR : alternatingGroup α ≤ ρ.range :=
    alternatingGroup_le_of_five_cycle ρ.range hc hcp hcs ⟨c, rfl⟩ hg ⟨g, rfl⟩ ⟨h, rfl⟩ hhp
  have hAcard : Nat.card (alternatingGroup α) = 360 := by
    have : Nontrivial α := by
      rw [← Fintype.one_lt_card_iff_nontrivial, hα]
      norm_num
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hα]
    norm_num [Nat.factorial]
  have hRge : 360 ≤ Nat.card ρ.range := hAcard ▸ Subgroup.card_le_of_le hAR
  have hkge : 16 ≤ Nat.card ρ.ker := hFcard ▸ Subgroup.card_le_of_le hF
  have hprod := Subgroup.card_ker_mul_card_range ρ
  have h1 : 16 * 360 ≤ Nat.card ρ.ker * Nat.card ρ.range := Nat.mul_le_mul hkge hRge
  have hkle : Nat.card ρ.ker ≤ 16 := by
    by_contra hcon
    push Not at hcon
    have : 17 * 360 ≤ Nat.card ρ.ker * Nat.card ρ.range := Nat.mul_le_mul hcon hRge
    omega
  have hRle : Nat.card ρ.range ≤ 360 := by
    by_contra hcon
    push Not at hcon
    have : 16 * 361 ≤ Nat.card ρ.ker * Nat.card ρ.range := Nat.mul_le_mul hkge hcon
    omega
  have hker : F = ρ.ker := Subgroup.eq_of_le_of_card_ge hF (by rw [hFcard]; exact hkle)
  have hrange : ρ.range = alternatingGroup α :=
    (Subgroup.eq_of_le_of_card_ge hAR (by rw [hAcard]; exact hRle)).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr hrange))⟩

end CFSG.EvenSporadicStandard.M22Std
