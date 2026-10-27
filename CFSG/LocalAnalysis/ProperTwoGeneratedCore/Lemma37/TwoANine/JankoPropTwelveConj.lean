module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveA

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem card_conj_orbit_mul [Finite G] (H : Subgroup G) (x : G) :
    {y | ∃ h ∈ H, h * x * h⁻¹ = y}.ncard * Nat.card (H ⊓ centralizer {x} : Subgroup G) =
      Nat.card H := by
  let _ : MulAction H G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : H) (y : G), h • y = (h : G) * y * (h : G)⁻¹ := fun h y =>
    ConjAct.toConjAct_smul (h : G) y
  have horb : MulAction.orbit H x = {y | ∃ h ∈ H, h * x * h⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h x).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsmul _ x⟩
  have hstab : MulAction.stabilizer H x = (centralizer {x}).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hcard := (MulAction.stabilizer H x).index_mul_card
  rw [MulAction.index_stabilizer, horb, hstab, ← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  exact hcard

theorem card_conj_subgroup_orbit_mul [Finite G] (H B : Subgroup G) :
    {D : Subgroup G | ∃ h ∈ H, B.map (MulAut.conj h).toMonoidHom = D}.ncard *
      Nat.card (H ⊓ normalizer (B : Set G) : Subgroup G) = Nat.card H := by
  let _ : MulAction H (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp H.subtype)
  have hsmul : ∀ (h : H) (D : Subgroup G), h • D = D.map (MulAut.conj (h : G)).toMonoidHom :=
    fun _ _ => rfl
  have horb : MulAction.orbit H B =
      {D : Subgroup G | ∃ h ∈ H, B.map (MulAut.conj h).toMonoidHom = D} := by
    ext D
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h B).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, hsmul _ B⟩
  have hstab : MulAction.stabilizer H B = (normalizer (B : Set G)).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    rfl
  have hcard := (MulAction.stabilizer H B).index_mul_card
  rw [MulAction.index_stabilizer, horb, hstab, ← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  exact hcard

theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {g x : G} (hg : orderOf g = 3)
    (hx : x ∈ zpowers g) : x = 1 ∨ x = g ∨ x = g⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hg]
  have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with hk | hk | hk <;> rw [hk]
  · left; exact zpow_zero g
  · right; left; exact zpow_one g
  · right; right
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num,
      zpow_natCast, ← hg, pow_orderOf_eq_one]

theorem conj_eq_or_eq_inv {y g : G} (hy : orderOf y = 3)
    (hg : g ∈ normalizer (zpowers y : Set G)) : g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y⁻¹ := by
  have hmem : g * y * g⁻¹ ∈ zpowers y :=
    (Subgroup.mem_normalizer_iff.mp hg y).mp (Subgroup.mem_zpowers y)
  rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hy hmem with h | h | h
  · exfalso
    rw [mul_inv_eq_one, mul_eq_left] at h
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)
  · exact Or.inl h
  · exact Or.inr h

theorem conj_eq_of_odd {y g : G} (hy : orderOf y = 3) (hg : g ∈ normalizer (zpowers y : Set G))
    (hodd : Odd (orderOf g)) : g * y * g⁻¹ = y := by
  rcases conj_eq_or_eq_inv hy hg with h | h
  · exact h
  exfalso
  have hg2 : (g ^ 2) * y * (g ^ 2)⁻¹ = y := by
    have h' : g * y⁻¹ * g⁻¹ = y := by
      rw [show g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ by group, h, inv_inv]
    calc (g ^ 2) * y * (g ^ 2)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by rw [pow_two]; group
      _ = y := by rw [h, h']
  obtain ⟨k, hk⟩ := hodd
  have hgk : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hmem : g ^ 2 ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g ^ 2 * y = (g ^ 2) * y * (g ^ 2)⁻¹ * g ^ 2 := by group
      _ = y * g ^ 2 := by rw [hg2]
  have hgc : g ∈ centralizer ({y} : Set G) := by
    rw [hgk]
    exact Subgroup.pow_mem _ hmem _
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  have hyy : y = y⁻¹ := by
    rw [← h, hgc, mul_inv_cancel_right]
  have h2 : y ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hyy]
    exact mul_inv_cancel y
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hy] at this
  exact absurd this (by norm_num)

theorem conj_eq_inv_of_inf_eq_bot {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {u : G} (hu : u * u = 1) (huA : u ∈ normalizer (A : Set G))
    (hfix : A ⊓ centralizer ({u} : Set G) = ⊥) {a : G} (ha : a ∈ A) : u * a * u⁻¹ = a⁻¹ := by
  have hua : u * a * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp huA a).mp ha
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hw : a * (u * a * u⁻¹) ∈ A ⊓ centralizer ({u} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem ha hua, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * (u * a * u⁻¹) * u = u * (u * a * u⁻¹ * a) := by
          rw [huinv]
          calc a * (u * a * u) * u = a * (u * a * (u * u)) := by group
            _ = a * (u * a) := by rw [hu, mul_one]
            _ = u * u * (a * (u * a)) := by rw [hu, one_mul]
            _ = u * (u * a * u * a) := by group
      _ = u * (a * (u * a * u⁻¹)) := by rw [hA _ hua a ha]
  rw [hfix, Subgroup.mem_bot] at hw
  exact eq_inv_of_mul_eq_one_right hw

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
