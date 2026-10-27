module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open scoped Pointwise

theorem frattini_reduction {Y : Type*} [Group Y] {B V : Subgroup Y}
    (hBV : B ≤ Subgroup.normalizer (V : Set Y))
    (hB : Nat.card ↥B = 192) {d : ↥B} (hd : Nat.card (Subgroup.zpowers d) = 3)
    (σ : MulAut ↥B) (hσ : ∀ b : ↥B, (b : Y) ∈ V ↔ ((σ b : ↥B) : Y) ∈ V) :
    ∃ (b : ↥B) (n : MulAut ↥B), σ = MulAut.conj b * n ∧ (n d = d ∨ n d = d⁻¹) ∧
      ∀ x : ↥B, (x : Y) ∈ V ↔ ((n x : ↥B) : Y) ∈ V := by
  haveI : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf d = 3 := by rw [← Nat.card_zpowers]; exact hd
  have hd3 : d ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one d
  have hddd : d * d * d = 1 := by rw [← hd3, pow_three, mul_assoc]
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    norm_num at hord
  have hσord : orderOf (σ d) = 3 := by rw [MulEquiv.orderOf_eq σ d, hord]
  set P : Subgroup ↥B := Subgroup.zpowers d with hPdef
  set Q : Subgroup ↥B := Subgroup.zpowers (σ d) with hQdef
  have hPcard : Nat.card P = 3 := hd
  have hQcard : Nat.card Q = 3 := by rw [hQdef, Nat.card_zpowers, hσord]
  have hPsyl : IsPGroup 3 P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  have hQsyl : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by rw [hQcard]; norm_num)
  have hPidx : ¬ 3 ∣ P.index := by
    have h := Subgroup.card_mul_index (H := P)
    rw [hPcard, hB] at h
    omega
  have hQidx : ¬ 3 ∣ Q.index := by
    have h := Subgroup.card_mul_index (H := Q)
    rw [hQcard, hB] at h
    omega
  let P3 : Sylow 3 ↥B := hPsyl.toSylow hPidx
  let Q3 : Sylow 3 ↥B := hQsyl.toSylow hQidx
  haveI : Finite (Sylow 3 ↥B) := Sylow.finite_of_finiteIndex P3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥B) P3 Q3
  have hconj : MulAut.conj g • P = Q := by
    have h1 : ((g • P3 : Sylow 3 ↥B) : Subgroup ↥B) = (Q3 : Subgroup ↥B) := by rw [hg]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hσdmem : σ d ∈ MulAut.conj g • P := by
    rw [hconj]
    exact Subgroup.mem_zpowers _
  obtain ⟨s, hsP, hs⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hσdmem
  have hσd : σ d = g * s * g⁻¹ := by
    rw [← hs]
    rfl
  set n : MulAut ↥B := MulAut.conj g⁻¹ * σ with hn
  have hnd : n d = s := by
    rw [hn, MulAut.mul_apply, hσd, MulAut.conj_apply]
    group
  refine ⟨g, n, ?_, ?_, ?_⟩
  · rw [hn, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  · have hs1 : s ≠ 1 := by
      intro h1
      apply hd1
      apply MulEquiv.injective n
      rw [map_one, hnd, h1]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsP
    have hr : d ^ (k % 3) = s := by
      have h3 := zpow_mod_orderOf d k
      rw [hord] at h3
      push_cast at h3
      rw [h3]
      exact hk
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rw [hnd]
    rcases hk3 with h | h | h
    · rw [h, zpow_zero] at hr
      exact absurd hr.symm hs1
    · rw [h, zpow_one] at hr
      exact Or.inl hr.symm
    · rw [h, zpow_two] at hr
      refine Or.inr ?_
      rw [← hr]
      exact eq_inv_of_mul_eq_one_left hddd
  · intro x
    have hgV : ∀ y : Y, y ∈ V ↔ (g : Y)⁻¹ * y * ((g : Y)⁻¹)⁻¹ ∈ V := fun y =>
      Subgroup.mem_normalizer_iff.mp (hBV (inv_mem g.2)) y
    have hnx : ((n x : ↥B) : Y) = (g : Y)⁻¹ * ((σ x : ↥B) : Y) * ((g : Y)⁻¹)⁻¹ := by
      rw [hn, MulAut.mul_apply, MulAut.conj_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hnx]
    exact (hσ x).trans (hgV _)

end CFSG.GH74.QTGen4.DSGen4.L34
