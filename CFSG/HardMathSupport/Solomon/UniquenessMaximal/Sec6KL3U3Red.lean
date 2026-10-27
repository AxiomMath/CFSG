module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DHeis

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open scoped commutatorElement

theorem relIndex_le_twentySeven {A : Type*} [Group A] [Finite A] (D P : Subgroup A)
    (hcyc : ∀ H ≤ P, ∃ x ∈ H, ∀ h ∈ H, ∃ k : ℤ, x ^ k * h⁻¹ ∈ D)
    (hD : ∀ H0 N0 : Subgroup A, H0 ≤ P → H0 ≤ D → N0 ≤ H0 →
      (∀ x ∈ H0, ∀ y ∈ H0, ⁅x, y⁆ ∈ N0) → (∀ x ∈ H0, x ^ 3 ∈ N0) → N0.relIndex H0 ≤ 9)
    {H N : Subgroup A} (hHP : H ≤ P) (hNH : N ≤ H)
    (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ ∈ N) (hcube : ∀ x ∈ H, x ^ 3 ∈ N) :
    N.relIndex H ≤ 27 := by
  classical
  obtain ⟨x, hxH, hx⟩ := hcyc H hHP
  set N' : Subgroup H := N.subgroupOf H with hN'
  haveI : N'.Normal := ⟨fun n hn g => hnorm g g.2 n hn⟩
  let π : H →* H ⧸ N' := QuotientGroup.mk' N'
  set H0 : Subgroup A := H ⊓ D with hH0
  let ρ0 : H0 →* H ⧸ N' := π.comp (Subgroup.inclusion inf_le_left)
  have hker : ρ0.ker = N.subgroupOf H0 := by
    ext y
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ρ0, π, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hrange : Nat.card ρ0.range = N.relIndex H0 := by
    rw [← Subgroup.index_ker, hker]
    rfl
  have h9 : N.relIndex H0 ≤ 9 := by
    have hN1 : N ⊓ H0 ≤ H0 := inf_le_right
    have := hD H0 (N ⊓ H0) (inf_le_left.trans hHP) inf_le_right hN1 (by
      intro y hy z hz
      refine ⟨hcomm y hy.1 z hz.1, ?_⟩
      refine ⟨H.mul_mem (H.mul_mem (H.mul_mem hy.1 hz.1) (H.inv_mem hy.1)) (H.inv_mem hz.1), ?_⟩
      exact D.mul_mem (D.mul_mem (D.mul_mem hy.2 hz.2) (D.inv_mem hy.2)) (D.inv_mem hz.2)) (by
      intro y hy
      exact ⟨hcube y hy.1, H.pow_mem hy.1 3, D.pow_mem hy.2 3⟩)
    rwa [Subgroup.inf_relIndex_right] at this
  set xq : H ⧸ N' := π ⟨x, hxH⟩ with hxq
  have hxq3 : xq ^ 3 = 1 := by
    rw [hxq, ← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 (hcube x hxH)
  let Φ : ρ0.range × Fin 3 → H ⧸ N' := fun p => (p.1 : H ⧸ N') * xq ^ (p.2 : ℕ)
  have hΦ : Function.Surjective Φ := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hx h.1 h.2
    have hh0 : h.1 * x ^ (-k) ∈ H0 := by
      refine ⟨H.mul_mem h.2 (H.zpow_mem hxH _), ?_⟩
      have : h.1 * x ^ (-k) = (x ^ k * h.1⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv, zpow_neg]
      rw [this]
      exact D.inv_mem hk
    refine ⟨(⟨ρ0 ⟨h.1 * x ^ (-k), hh0⟩, ⟨_, rfl⟩⟩, ⟨(k % 3).toNat, by omega⟩), ?_⟩
    show ρ0 ⟨h.1 * x ^ (-k), hh0⟩ * xq ^ ((k % 3).toNat) = QuotientGroup.mk h
    have e1 : ρ0 ⟨h.1 * x ^ (-k), hh0⟩ =
        QuotientGroup.mk (⟨h.1 * x ^ (-k), hh0.1⟩ : H) := rfl
    have e2 : xq ^ ((k % 3).toNat) = xq ^ k := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
      exact (zpow_eq_zpow_emod k (n := 3) (by exact_mod_cast hxq3)).symm
    rw [e1, e2, hxq, ← map_zpow, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp
  calc N.relIndex H = Nat.card (H ⧸ N') := (Subgroup.index_eq_card N')
    _ ≤ Nat.card (ρ0.range × Fin 3) := Nat.card_le_card_of_surjective Φ hΦ
    _ = Nat.card ρ0.range * 3 := by rw [Nat.card_prod]; simp
    _ ≤ 9 * 3 := by rw [hrange]; exact Nat.mul_le_mul h9 le_rfl
    _ = 27 := by norm_num

theorem not_hasElemSection3_four_of_reduction {A : Type*} [Group A] [Finite A] (D P : Subgroup A)
    (hcyc : ∀ H ≤ P, ∃ x ∈ H, ∀ h ∈ H, ∃ k : ℤ, x ^ k * h⁻¹ ∈ D)
    (hD : ∀ H0 N0 : Subgroup A, H0 ≤ P → H0 ≤ D → N0 ≤ H0 →
      (∀ x ∈ H0, ∀ y ∈ H0, ⁅x, y⁆ ∈ N0) → (∀ x ∈ H0, x ^ 3 ∈ N0) → N0.relIndex H0 ≤ 9) :
    ¬ HasElemSection3 P 4 := by
  rintro ⟨H, N, hNH, hHP, hnorm, hcomm, hcube, hidx⟩
  have h27 := relIndex_le_twentySeven D P hcyc hD hHP hNH hnorm
    (fun x hx y hy => by
      have := hcomm x hx y hy
      rwa [commutatorElement_def])
    hcube
  have : (N.subgroupOf H).index = N.relIndex H := rfl
  omega

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
