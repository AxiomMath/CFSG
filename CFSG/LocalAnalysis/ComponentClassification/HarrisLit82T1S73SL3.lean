module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73Sq

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.HighestRoot
open scoped MatrixGroups

theorem sl23_mul_pow_four : ∀ u v : SL23, u ^ 4 = 1 → v ^ 4 = 1 → (u * v) ^ 4 = 1 := by
  decide +kernel

theorem sl23_exists_pow_four : ∀ a : SL23, (a ^ 3 = 1 ∨ a ^ 3 = -1) → a ≠ 1 → a ≠ -1 →
    ∃ g : SL23, g ^ 4 = 1 ∧ (a ^ 5 * g * a * g ^ 3) ^ 2 ≠ 1 := by
  decide +kernel

theorem sl23_sq_of_pow_four : ∀ y : SL23, (y ^ 4 = 1 ∨ y ^ 4 = -1) → (y ^ 2 = 1 ∨ y ^ 2 = -1) := by
  decide +kernel

theorem sl23_conj_of_pow_three : ∀ x y : SL23, x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 → y ≠ 1 →
    ∃ g : SL23, g * x = y * g ∨ y * g * x = g := by
  decide +kernel

theorem sl23_exists_pow_three : ∃ x : SL23, x ^ 3 = 1 ∧ x ≠ 1 ∧ x ≠ -1 := by
  decide +kernel

section Iso

variable {J : Type*} [Group J]

theorem card_zmod_three : Nat.card (ZMod 3) = 3 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem normal_eq_top_of_mem_sl23 (e : J ≃* SL23) {N : Subgroup J} (hN : N.Normal) {x : J}
    (hxN : x ∈ N) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : N = ⊤ := by
  rw [eq_top_iff, ← closure_orderOf_three_eq_top_of_mulEquiv card_zmod_three e, closure_le]
  intro y hy
  have hy3 : y ^ 3 = 1 := by
    have h : orderOf y = 3 := hy
    rw [← h]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    have h' : orderOf y = 3 := hy
    rw [h, orderOf_one] at h'
    exact absurd h' (by norm_num)
  have hex3 : e x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hey3 : e y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hex1 : e x ≠ 1 := fun h => hx1 (e.injective (h.trans (map_one e).symm))
  have hey1 : e y ≠ 1 := fun h => hy1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg | hg⟩ := sl23_conj_of_pow_three (e x) (e y) hex3 hex1 hey3 hey1
  · have h1 : y = e.symm g * x * (e.symm g)⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg, mul_inv_cancel_right]
    rw [SetLike.mem_coe, h1]
    exact hN.conj_mem x hxN _
  · have h1 : y⁻¹ = e.symm g * x * (e.symm g)⁻¹ := by
      apply e.injective
      rw [map_inv, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, inv_eq_iff_mul_eq_one]
      calc e y * (g * e x * g⁻¹) = e y * g * e x * g⁻¹ := by simp only [mul_assoc]
        _ = g * g⁻¹ := by rw [hg]
        _ = 1 := mul_inv_cancel g
    have h2 : y⁻¹ ∈ N := by
      rw [h1]
      exact hN.conj_mem x hxN _
    rw [SetLike.mem_coe, ← inv_inv y]
    exact inv_mem h2

theorem psl23_sq_eq_one (e : J ≃* PSL(2, ZMod 3)) {y : J} (hy : y ^ 4 = 1) : y ^ 2 = 1 := by
  obtain ⟨Y, hY⟩ := QuotientGroup.mk_surjective (e y)
  have hY4 : (QuotientGroup.mk (Y ^ 4) : PSL(2, ZMod 3)) = 1 := by
    rw [QuotientGroup.mk_pow, hY, ← map_pow, hy, map_one]
  rw [QuotientGroup.eq_one_iff, mem_center_SL23_iff] at hY4
  have hY2 := sl23_sq_of_pow_four Y hY4
  apply e.injective
  rw [map_pow, map_one, ← hY, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    mem_center_SL23_iff]
  exact hY2

theorem le_closure_mul_self_of_sl23 {G : Type*} [Group G] {J : Subgroup G}
    (h : Nonempty (↥J ≃* PSL(2, ZMod 3)) ∨ Nonempty (↥J ≃* SL(2, ZMod 3))) :
    J ≤ closure {x | ∃ y ∈ J, y * y = x} := by
  have hodd : Odd (Nat.card (ZMod 3)) := by rw [card_zmod_three]; decide
  have hsq := closure_mul_self_sl2 (K := ZMod 3) hodd
  obtain ⟨φ, hφ⟩ : ∃ φ : SL(2, ZMod 3) →* ↥J, Function.Surjective φ := by
    rcases h with h | h
    · obtain ⟨e⟩ := h
      exact ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' _),
        e.symm.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    · obtain ⟨e⟩ := h
      exact ⟨e.symm.toMonoidHom, e.symm.surjective⟩
  have hrange : (J.subtype.comp φ).range = J := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective φ hφ, ← MonoidHom.range_eq_map,
      range_subtype]
  have h1 := range_le_closure_mul_self (J.subtype.comp φ) hsq
  rwa [hrange] at h1

end Iso

theorem conj_mem_of_isSubnormal {G : Type*} [Group G] {p q : ℕ} (hpq : Nat.Coprime p q)
    {N : Subgroup G} (hN : N.Normal) (hNp : ∀ n ∈ N, ∃ a : ℕ, n ^ p ^ a = 1)
    {H : Subgroup G} (hH : H.IsSubnormal) {x : G} (hxH : x ∈ H) {b : ℕ} (hxb : x ^ q ^ b = 1)
    {g : G} (hg : g ∈ N) : g * x * g⁻¹ ∈ H := by
  induction hH with
  | top => exact mem_top _
  | step H K hHK hK hHn ih =>
    have := hHn
    have hxK : x ∈ K := hHK hxH
    have hgxK : g * x * g⁻¹ ∈ K := ih hxK
    set n := g * x * g⁻¹ * x⁻¹ with hn
    have hnN : n ∈ N := by
      rw [hn, show g * x * g⁻¹ * x⁻¹ = g * (x * g⁻¹ * x⁻¹) by group]
      exact mul_mem hg (hN.conj_mem _ (inv_mem hg) x)
    have hnK : n ∈ K := mul_mem hgxK (inv_mem hxK)
    obtain ⟨a, ha⟩ := hNp n hnN
    set ψ := QuotientGroup.mk' (H.subgroupOf K) with hψ
    have hψx : ψ ⟨x, hxK⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hxH
    have h1 : ψ ⟨n, hnK⟩ ^ p ^ a = 1 := by
      rw [← map_pow, show (⟨n, hnK⟩ : K) ^ p ^ a = 1 from Subtype.ext (by simp [ha]), map_one]
    have hconj : (g * x * g⁻¹) ^ q ^ b = 1 := by
      rw [conj_pow, hxb, mul_one, mul_inv_cancel]
    have h2 : ψ ⟨n, hnK⟩ ^ q ^ b = 1 := by
      rw [show (⟨n, hnK⟩ : K) = ⟨g * x * g⁻¹, hgxK⟩ * (⟨x, hxK⟩ : K)⁻¹ from Subtype.ext rfl,
        map_mul, map_inv, hψx, inv_one, mul_one, ← map_pow,
        show (⟨g * x * g⁻¹, hgxK⟩ : K) ^ q ^ b = 1 from Subtype.ext (by simp [hconj]),
        map_one]
    have h3 : ψ ⟨n, hnK⟩ = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow a b hpq)
        (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2))
    have hnH' : (⟨n, hnK⟩ : K) ∈ H.subgroupOf K := (QuotientGroup.eq_one_iff _).mp h3
    have hnH : n ∈ H := hnH'
    have e : g * x * g⁻¹ = n * x := by rw [hn]; group
    rw [e]
    exact mul_mem hnH hxH

end CFSG.ComponentClassification.HarrisLit.T1
