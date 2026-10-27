module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveConj

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalB

open Subgroup JankoTwelve

variable {G : Type} [Group G]

theorem exists_mem_normalizer_not_mem [Finite G] {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hK : IsPGroup p K) (hHK : H < K) : ∃ g ∈ K, g ∉ H ∧ g ∈ normalizer (H : Set G) := by
  have : Group.IsNilpotent K := hK.isNilpotent
  have hlt : H.subgroupOf K < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hHK.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : K) ∈ H.subgroupOf K := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyH⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := K) _ hlt)
  refine ⟨y, y.2, fun h => hyH (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (H : Set G)).subgroupOf K := by
    rw [subgroupOf_normalizer_eq hHK.le]
    exact hyN
  exact mem_subgroupOf.mp hy

theorem exists_eq_mul_of_mem_sup {x y g : G} (hxy : x * y = y * x) (hx : orderOf x = 3)
    (hy : orderOf y = 3) (hg : g ∈ zpowers x ⊔ zpowers y) :
    ∃ a b : G, (a = 1 ∨ a = x ∨ a = x⁻¹) ∧ (b = 1 ∨ b = y ∨ b = y⁻¹) ∧ g = a * b := by
  have hle : zpowers x ≤ normalizer (zpowers y : Set G) :=
    le_normalizer_of_commute fun a ha b hb => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow hxy i j).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hle hg
  exact ⟨a, b, eq_one_or_eq_or_eq_inv_of_mem_zpowers hx ha,
    eq_one_or_eq_or_eq_inv_of_mem_zpowers hy hb, rfl⟩

theorem comm_of_comm_sq {g y : G} (hodd : Odd (orderOf g)) (h : g ^ 2 * y = y * g ^ 2) :
    g * y = y * g := by
  obtain ⟨k, hk⟩ := hodd
  have hg : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hc : Commute (g ^ 2) y := h
  rw [hg]
  exact (hc.pow_left (k + 1)).eq


theorem conj_eq_mul_or_eq_inv_mul {x y g : G} (hxy : x * y = y * x) (hx : orderOf x = 3)
    (hy : orderOf y = 3) (hbot : zpowers x ⊓ zpowers y = ⊥) (hgx : g * x = x * g)
    (hodd : Odd (orderOf g)) (hne : g * y * g⁻¹ ≠ y) (hmem : g * y * g⁻¹ ∈ zpowers x ⊔ zpowers y) :
    g * y * g⁻¹ = x * y ∨ g * y * g⁻¹ = x⁻¹ * y := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eq_mul_of_mem_sup hxy hx hy hmem
  have hga : g * a = a * g := by
    rcases ha with rfl | rfl | rfl
    · simp
    · exact hgx
    · exact (Commute.inv_right hgx).eq
  have hay : a * y = y * a := by
    rcases ha with rfl | rfl | rfl
    · simp
    · exact hxy
    · exact (Commute.inv_left hxy).eq
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  rcases hb with rfl | rfl | rfl
  · exfalso
    rw [mul_one] at hab
    have hyx : y = a := by
      have h4 : g * y = a * g := by rw [← hab]; group
      rw [← hga] at h4
      exact mul_left_cancel h4
    have hyx' : y ∈ zpowers x := by
      rw [hyx]
      rcases ha with h | h | h <;> rw [h]
      · exact one_mem _
      · exact mem_zpowers x
      · exact inv_mem (mem_zpowers x)
    have : y ∈ zpowers x ⊓ zpowers y := ⟨hyx', mem_zpowers y⟩
    rw [hbot, mem_bot] at this
    exact hy1 this
  · rcases ha with rfl | rfl | rfl
    · exact absurd (by rw [hab, one_mul]) hne
    · exact Or.inl hab
    · exact Or.inr hab
  · exfalso
    apply hne
    have h1 : g * y = a * y⁻¹ * g := by rw [← hab]; group
    have h2 : g * y⁻¹ = y * a⁻¹ * g := by
      have h3 : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [hab, mul_inv_eq_iff_eq_mul] at h3
      rw [h3]
      group
    have hsq : g ^ 2 * y = y * g ^ 2 := by
      calc g ^ 2 * y = g * (g * y) := by rw [sq, mul_assoc]
        _ = g * a * y⁻¹ * g := by rw [h1]; group
        _ = a * (g * y⁻¹) * g := by rw [hga]; group
        _ = a * y * a⁻¹ * g * g := by rw [h2]; group
        _ = y * g ^ 2 := by rw [hay, sq]; group
    rw [comm_of_comm_sq hodd hsq]
    group

theorem swap_conj {σ p g₁ u : G} (hσp : σ * p = p * σ) (hg₁σ : g₁ * σ = σ * g₁)
    (hg₁p : g₁ * p * g₁⁻¹ = σ * p) (hup : u * p = p * u) (huσ : u * σ * u⁻¹ = p⁻¹ * σ) :
    g₁ * u * g₁ * p * (g₁ * u * g₁)⁻¹ = σ ∧ g₁ * u * g₁ * σ * (g₁ * u * g₁)⁻¹ = p⁻¹ := by
  have e1 : MulAut.conj g₁ σ = σ := by rw [MulAut.conj_apply, hg₁σ, mul_inv_cancel_right]
  have e2 : MulAut.conj g₁ p = σ * p := by rw [MulAut.conj_apply, hg₁p]
  have e3 : MulAut.conj u p = p := by rw [MulAut.conj_apply, hup, mul_inv_cancel_right]
  have e4 : MulAut.conj u σ = p⁻¹ * σ := by rw [MulAut.conj_apply, huσ]
  have e5 : p⁻¹ * σ * p = σ := by rw [mul_assoc, hσp, inv_mul_cancel_left]
  have hc : ∀ x, g₁ * u * g₁ * x * (g₁ * u * g₁)⁻¹ =
      MulAut.conj g₁ (MulAut.conj u (MulAut.conj g₁ x)) := by
    intro x
    simp only [MulAut.conj_apply]
    group
  constructor
  · rw [hc, e2, map_mul, e4, e3, e5, e1]
  · rw [hc, e1, e4, map_mul, map_inv, e2, e1]
    group

theorem exists_conj_eq_mul {t y : G} (ht : t * t = 1) (hty : t * y * (t * y) = 1)
    (hodd : Odd (orderOf y)) : ∃ w ∈ zpowers y, w * t * w⁻¹ = t * y := by
  obtain ⟨k, hk⟩ := hodd
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * y * t⁻¹ = y⁻¹ := by
    rw [htinv]
    exact eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using hty)
  have h2 : t * y ^ k * t⁻¹ = (y ^ k)⁻¹ := by rw [← conj_pow, h1, inv_pow]
  have h3 : t * (y ^ k)⁻¹ = y ^ k * t := by
    have h4 : t * (y ^ k)⁻¹ * t⁻¹ = (t * y ^ k * t⁻¹)⁻¹ := by group
    rw [h2, inv_inv] at h4
    exact mul_inv_eq_iff_eq_mul.mp h4
  have h5 : y ^ k * y ^ k = y⁻¹ := by
    rw [← pow_add, eq_inv_iff_mul_eq_one, ← pow_succ, show k + k + 1 = orderOf y by omega,
      pow_orderOf_eq_one]
  have h6 : t * y = y⁻¹ * t := mul_inv_eq_iff_eq_mul.mp h1
  refine ⟨y ^ k, pow_mem (mem_zpowers y) k, ?_⟩
  rw [mul_assoc, h3, ← mul_assoc, h5, h6]
end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalB
