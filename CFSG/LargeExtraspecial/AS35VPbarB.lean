module

public import CFSG.LargeExtraspecial.AS35VPbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35V

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem natCard_le_ncard_of_mem {H : Subgroup S.O} {T : Set S.O} (hT : ∀ y ∈ H, y ∈ T) :
    Nat.card H ≤ T.ncard := by
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (fun y hy => hT y hy) (Set.toFinite _)

namespace PbarFacts

variable {τ : S.O} {P : Subgroup S.O}

theorem sq_commute (h : PbarFacts S τ P) {x y : S.O} (hx : x ∈ P) (hy : y ∈ P) :
    x * x * y = y * (x * x) := by
  have hτc : ∀ w ∈ P, w * τ = τ * w := fun w hw => h.commute hw
  rcases h.commutator_eq hx hy with hc | hc
  · have e : x * y = y * x := by
      calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
        _ = y * x := by rw [hc, one_mul]
    rw [mul_assoc, e, ← mul_assoc, e, mul_assoc]
  · have e : x * y = τ * y * x := by
      calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
        _ = τ * y * x := by rw [hc]
    have hτ2 : τ * τ = 1 := h.mul_self
    calc x * x * y = x * (τ * y * x) := by rw [mul_assoc, e]
      _ = (x * τ) * y * x := by group
      _ = (τ * x) * y * x := by rw [hτc x hx]
      _ = τ * (x * y) * x := by group
      _ = τ * (τ * y * x) * x := by rw [e]
      _ = (τ * τ) * y * (x * x) := by group
      _ = y * (x * x) := by rw [hτ2, one_mul]

theorem sq_eq (h : PbarFacts S τ P) {x : S.O} (hx : x ∈ P) : x * x = 1 ∨ x * x = τ :=
  h.center_eq _ (P.mul_mem hx hx) fun _ hy => h.sq_commute hx hy

theorem width_le_three (h : PbarFacts S τ P) (hinv : ∀ p ∈ P, p * p = 1 → p = 1 ∨ p = τ) :
    S.width ≤ 3 := by
  by_contra hw
  push Not at hw
  have hτc : ∀ w ∈ P, w * τ = τ * w := fun w hw => h.commute hw
  have hτ2 : τ * τ = 1 := h.mul_self
  have hcard : 32 ≤ Nat.card P := by
    rw [h.card_eq]
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (2 * S.width - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : ∀ x ∈ P, x ≠ 1 → x ≠ τ → x * x = τ := by
    intro x hx h1 h2
    rcases h.sq_eq hx with e | e
    · rcases hinv x hx e with e' | e'
      · exact absurd e' h1
      · exact absurd e' h2
    · exact e
  obtain ⟨u, hu, hu1, huτ⟩ : ∃ u ∈ P, u ≠ 1 ∧ u ≠ τ := by
    by_contra hcon
    push Not at hcon
    have h2 : Nat.card P ≤ 2 := by
      refine (natCard_le_ncard_of_mem (T := {1, τ}) fun x hx => ?_).trans ?_
      · by_cases h1 : x = 1
        · exact Or.inl h1
        · exact Or.inr (hcon x hx h1)
      · refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
    omega
  have huu : u * u = τ := hsq u hu hu1 huτ
  have huinv : u⁻¹ = u * τ := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, huu, hτ2]
  obtain ⟨v₁, hv₁, huv₁⟩ : ∃ v₁ ∈ P, u * v₁ * u⁻¹ * v₁⁻¹ = τ := by
    by_contra hcon
    push Not at hcon
    have hc : ∀ y ∈ P, u * y = y * u := by
      intro y hy
      rcases h.commutator_eq hu hy with e | e
      · calc u * y = (u * y * u⁻¹ * y⁻¹) * y * u := by group
          _ = y * u := by rw [e, one_mul]
      · exact absurd e (hcon y hy)
    rcases h.center_eq u hu hc with e | e
    · exact hu1 e
    · exact huτ e
  have hcent : ∀ y ∈ P, u * y = y * u → y = 1 ∨ y = τ ∨ y = u ∨ y = u * τ := by
    intro y hy huy
    by_contra hcon
    push Not at hcon
    obtain ⟨hy1, hyτ, hyu, hyuτ⟩ := hcon
    have hyy : y * y = τ := hsq y hy hy1 hyτ
    have h1 : u * y ≠ 1 := by
      intro e
      apply hyuτ
      rw [← huinv]
      exact eq_inv_of_mul_eq_one_right e
    have h2 : u * y ≠ τ := by
      intro e
      apply hyu
      have e' : y = u⁻¹ * τ := by rw [← e]; group
      rw [e', huinv, mul_assoc, hτ2, mul_one]
    have h3 := hsq (u * y) (P.mul_mem hu hy) h1 h2
    have h4 : u * y * (u * y) = 1 := by
      calc u * y * (u * y) = u * (y * u) * y := by group
        _ = u * (u * y) * y := by rw [huy]
        _ = (u * u) * (y * y) := by group
        _ = 1 := by rw [huu, hyy, hτ2]
    exact h.ne_one (h3.symm.trans h4)
  have hmem : ∀ y ∈ P, y ∈ ({1, τ, u, u * τ, v₁, v₁ * τ, v₁ * u, v₁ * (u * τ)} : Set S.O) := by
    intro y hy
    rcases h.commutator_eq hu hy with e | e
    · have huy : u * y = y * u := by
        calc u * y = (u * y * u⁻¹ * y⁻¹) * y * u := by group
          _ = y * u := by rw [e, one_mul]
      rcases hcent y hy huy with h' | h' | h' | h' <;> simp [h']
    · have huy : u * y = τ * y * u := by
        calc u * y = (u * y * u⁻¹ * y⁻¹) * y * u := by group
          _ = τ * y * u := by rw [e]
      have huv : u * v₁ = τ * v₁ * u := by
        calc u * v₁ = (u * v₁ * u⁻¹ * v₁⁻¹) * v₁ * u := by group
          _ = τ * v₁ * u := by rw [huv₁]
      have hw : u * (v₁⁻¹ * y) = v₁⁻¹ * y * u := by
        have e0 : v₁ * u = τ * u * v₁ := by
          calc v₁ * u = τ * (τ * v₁ * u) := by rw [← mul_assoc, ← mul_assoc, hτ2, one_mul]
            _ = τ * (u * v₁) := by rw [huv]
            _ = τ * u * v₁ := by group
        have e1 : u * v₁⁻¹ = τ * v₁⁻¹ * u := by
          calc u * v₁⁻¹ = v₁⁻¹ * (v₁ * u) * v₁⁻¹ := by group
            _ = v₁⁻¹ * (τ * u * v₁) * v₁⁻¹ := by rw [e0]
            _ = v₁⁻¹ * τ * u := by group
            _ = τ * v₁⁻¹ * u := by rw [hτc _ (P.inv_mem hv₁)]
        calc u * (v₁⁻¹ * y) = (u * v₁⁻¹) * y := by group
          _ = τ * v₁⁻¹ * (u * y) := by rw [e1]; group
          _ = τ * v₁⁻¹ * (τ * y * u) := by rw [huy]
          _ = v₁⁻¹ * (τ * τ) * y * u := by
            rw [(hτc _ (P.inv_mem hv₁)).symm]
            group
          _ = v₁⁻¹ * y * u := by rw [hτ2, mul_one]
      have hw' := hcent (v₁⁻¹ * y) (P.mul_mem (P.inv_mem hv₁) hy) hw
      have hy' : y = v₁ * (v₁⁻¹ * y) := by group
      rcases hw' with h' | h' | h' | h' <;> rw [hy', h'] <;> simp
  have h8 : Nat.card P ≤ 8 := by
    refine (natCard_le_ncard_of_mem hmem).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    rw [Set.ncard_singleton]
  omega

theorem commute_of_normalizes (h : PbarFacts S τ P) {c : S.O} (hcM : c ∈ S.Mbar)
    (hcτ : c * τ = τ * c) (hc3 : c ^ 3 = 1) (hP : ∀ p ∈ P, p * c * p⁻¹ ∈ zpowers c) {p : S.O}
    (hp : p ∈ P) : p * c = c * p := by
  set w := p * c * p⁻¹ * c⁻¹ with hw
  have hwc : w ∈ zpowers c := (zpowers c).mul_mem (hP p hp) (inv_mem (mem_zpowers c))
  have hwP : w ∈ P := by
    have h1 := h.normalized c hcM hcτ p⁻¹ (P.inv_mem hp)
    rw [hw, show p * c * p⁻¹ * c⁻¹ = p * (c * p⁻¹ * c⁻¹) by group]
    exact P.mul_mem hp h1
  have hw3 : w ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hwc
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hw1 : w = 1 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.extra.1) ⟨w, hwP⟩
    rw [Subgroup.orderOf_mk] at hk
    have hd : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
    rw [hk] at hd
    have hk0 : k = 0 := by
      by_contra hk0
      have : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans hd
      omega
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  calc p * c = (p * c * p⁻¹ * c⁻¹) * c * p := by group
    _ = c * p := by rw [← hw, hw1, one_mul]

end PbarFacts

end AS35V

end CFSG.LargeExtraspecial
