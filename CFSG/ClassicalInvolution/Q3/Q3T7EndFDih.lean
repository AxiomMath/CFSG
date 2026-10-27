module

public import CFSG.GH74.Uniqueness.Bender.UnitaryAut

public section

namespace CFSG.GH74.Uniqueness.Bender

open scoped Pointwise

private theorem zmod_eq_or_eq_neg_of_three_mul_eq_zero {N : ℕ} [NeZero N] {x y : ZMod N}
    (hx : 3 * x = 0) (hy : 3 * y = 0) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : y = x ∨ y = -x := by
  have key : ∀ z : ZMod N, 3 * z = 0 → z ≠ 0 → 3 * z.val = N ∨ 3 * z.val = 2 * N := by
    intro z hz hz0
    have h1 : N ∣ 3 * z.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      simpa using hz
    have h2 : 0 < z.val := by
      rwa [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
    have h3 : z.val < N := ZMod.val_lt z
    obtain ⟨k, hk⟩ := h1
    have hk3 : k < 3 := by
      by_contra hk3
      have := not_lt.mp hk3
      nlinarith
    interval_cases k <;> omega
  rcases key x hx hx0 with h1 | h1 <;> rcases key y hy hy0 with h2 | h2
  · exact Or.inl (ZMod.val_injective N (by omega))
  · refine Or.inr (eq_neg_iff_add_eq_zero.mpr ?_)
    have : ((y.val + x.val : ℕ) : ZMod N) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact ⟨1, by omega⟩
    simpa using this
  · refine Or.inr (eq_neg_iff_add_eq_zero.mpr ?_)
    have : ((y.val + x.val : ℕ) : ZMod N) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact ⟨1, by omega⟩
    simpa using this
  · exact Or.inl (ZMod.val_injective N (by omega))

private theorem dihedral_eq_or_eq_inv_of_pow_three_eq_one {N : ℕ} [NeZero N]
    {g h : DihedralGroup N} (hg : g ^ 3 = 1) (hh : h ^ 3 = 1) (hg1 : g ≠ 1) (hh1 : h ≠ 1) :
    h = g ∨ h = g⁻¹ := by
  have hsr : ∀ x : ZMod N, (DihedralGroup.sr x) ^ 3 = 1 → False := fun x hx => by
    have h3 : (DihedralGroup.sr x) ^ 3 = DihedralGroup.sr x := by
      rw [pow_succ, pow_two, DihedralGroup.sr_mul_self, one_mul]
    rw [h3, DihedralGroup.one_def] at hx
    cases hx
  have hr : ∀ x : ZMod N, (DihedralGroup.r x) ^ 3 = 1 → DihedralGroup.r x ≠ 1 →
      3 * x = 0 ∧ x ≠ 0 := fun x hx hx1 => by
    refine ⟨?_, fun h0 => hx1 (by rw [h0, DihedralGroup.r_zero])⟩
    rw [DihedralGroup.r_pow, ← DihedralGroup.r_zero, DihedralGroup.r.injEq] at hx
    simpa [mul_comm] using hx
  cases g with
  | sr x => exact (hsr x hg).elim
  | r x =>
    cases h with
    | sr y => exact (hsr y hh).elim
    | r y =>
      obtain ⟨hx, hx0⟩ := hr x hg hg1
      obtain ⟨hy, hy0⟩ := hr y hh hh1
      rcases zmod_eq_or_eq_neg_of_three_mul_eq_zero hx hy hx0 hy0 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (by rw [DihedralGroup.inv_r])

theorem exists_eq_mul_or_eq_mul_inv_of_pow_three_of_dihedral {G : Type*} [Group G]
    {I D : Subgroup G} {N : ℕ} [NeZero N] (hID : I ⊓ D = ⊥)
    (hDI : D ≤ Subgroup.normalizer (I : Set G)) (e : D ≃* DihedralGroup N) {σ τ : G}
    (hσ : σ ∈ I ⊔ D) (hτ : τ ∈ I ⊔ D) (hσ3 : σ ^ 3 = 1) (hτ3 : τ ^ 3 = 1) (hσ1 : σ ∉ I)
    (hτ1 : τ ∉ I) : ∃ b ∈ I, τ = b * σ ∨ τ = b * σ⁻¹ := by
  have hconj : ∀ d ∈ D, ∀ a ∈ I, d * a * d⁻¹ ∈ I := fun d hd a ha =>
    (Subgroup.mem_normalizer_iff.mp (hDI hd) a).mp ha
  have hdecomp : ∀ x ∈ I ⊔ D, ∃ a ∈ I, ∃ d ∈ D, a * d = x := by
    intro x hx
    have hx' : x ∈ ((I : Set G) * (D : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left I D hDI]
      exact hx
    obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨a, ha, d, hd, rfl⟩
  have hcube : ∀ a ∈ I, ∀ d ∈ D, (a * d) ^ 3 = 1 → d ^ 3 = 1 := by
    intro a ha d hd h3
    have h1 : (a * d) ^ 3 =
        (a * (d * a * d⁻¹) * (d ^ 2 * a * (d ^ 2)⁻¹)) * d ^ 3 := by
      rw [pow_succ, pow_two]
      group
    have hmem : a * (d * a * d⁻¹) * (d ^ 2 * a * (d ^ 2)⁻¹) ∈ I :=
      I.mul_mem (I.mul_mem ha (hconj d hd a ha)) (hconj (d ^ 2) (D.pow_mem hd 2) a ha)
    have hd3 : d ^ 3 ∈ I := by
      rw [eq_inv_of_mul_eq_one_right (h1.symm.trans h3)]
      exact I.inv_mem hmem
    have : d ^ 3 ∈ I ⊓ D := ⟨hd3, D.pow_mem hd 3⟩
    rwa [hID, Subgroup.mem_bot] at this
  obtain ⟨a, ha, δ, hδ, rfl⟩ := hdecomp σ hσ
  obtain ⟨a', ha', δ', hδ', rfl⟩ := hdecomp τ hτ
  have hδ3 := hcube a ha δ hδ hσ3
  have hδ'3 := hcube a' ha' δ' hδ' hτ3
  have hδ1 : δ ≠ 1 := fun h => hσ1 (by rw [h, mul_one]; exact ha)
  have hδ'1 : δ' ≠ 1 := fun h => hτ1 (by rw [h, mul_one]; exact ha')
  have hmain := dihedral_eq_or_eq_inv_of_pow_three_eq_one (g := e ⟨δ, hδ⟩) (h := e ⟨δ', hδ'⟩)
    (by rw [← map_pow]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext hδ3))
    (by rw [← map_pow]; exact (map_eq_one_iff e e.injective).mpr (Subtype.ext hδ'3))
    (fun h => hδ1 (by simpa using (map_eq_one_iff e e.injective).mp h))
    (fun h => hδ'1 (by simpa using (map_eq_one_iff e e.injective).mp h))
  rw [← map_inv, e.injective.eq_iff, e.injective.eq_iff] at hmain
  rcases hmain with h | h
  · have h' : δ' = δ := congrArg Subtype.val h
    subst h'
    refine ⟨a' * a⁻¹, I.mul_mem ha' (I.inv_mem ha), Or.inl ?_⟩
    group
  · have h' : δ' = δ⁻¹ := congrArg Subtype.val h
    subst h'
    have hm := hconj δ⁻¹ (D.inv_mem hδ) a ha
    rw [inv_inv] at hm
    refine ⟨a' * (δ⁻¹ * a * δ), I.mul_mem ha' hm, Or.inr ?_⟩
    group

theorem BenderType.exists_eq_mul_of_orderThree_unitary
    {K : Type} [Group K] [Finite K] {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K)
    {σ τ : MulAut K} (hσ : σ ∈ autCentralizer (rootCenter (Q : Subgroup K)))
    (hτ : τ ∈ autCentralizer (rootCenter (Q : Subgroup K))) (hσ3 : σ ^ 3 = 1) (hτ3 : τ ^ 3 = 1)
    (hσ1 : σ ∉ Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K))
    (hτ1 : τ ∉ Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K)) :
    ∃ b ∈ Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K),
      τ = b * σ ∨ τ = b * σ⁻¹ := by
  obtain ⟨D, hD1, hD2, hD3, -, ⟨eD⟩⟩ := h.lemma_3_6_c_unitary Q
  have hIM : Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K) ≤
      autCentralizer (rootCenter (Q : Subgroup K)) := hD2 ▸ le_sup_left
  have hDM : D ≤ autCentralizer (rootCenter (Q : Subgroup K)) := hD2 ▸ le_sup_right
  have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hIM).mp hD3
  rw [← hD2] at hσ hτ
  exact exists_eq_mul_or_eq_mul_inv_of_pow_three_of_dihedral hD1 (hDM.trans hnorm) eD hσ hτ hσ3
    hτ3 hσ1 hτ1

end CFSG.GH74.Uniqueness.Bender
