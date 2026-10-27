module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma111a

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK

private theorem mem_sup_of_commute' {C : Type} [Group C] {H K : Subgroup C}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : C} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩
    · exact ⟨1, H.one_mem, x, hx, (one_mul x).symm⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := hx
    obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := hy
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    have := hc h₂ hh₂ k₁ hk₁
    calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
      _ = h₁ * (h₂ * k₁) * k₂ := by rw [← this]
      _ = h₁ * h₂ * (k₁ * k₂) := by group
  | inv x _ hx =>
    obtain ⟨h, hh, k, hk, rfl⟩ := hx
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    have := hc h hh k hk
    have h1 : h⁻¹ * k⁻¹ = k⁻¹ * h⁻¹ := by
      have h0 : k * h = h * k := this.symm
      calc h⁻¹ * k⁻¹ = (k * h)⁻¹ := by group
        _ = (h * k)⁻¹ := by rw [h0]
        _ = k⁻¹ * h⁻¹ := by group
    calc (h * k)⁻¹ = k⁻¹ * h⁻¹ := by group
      _ = h⁻¹ * k⁻¹ := h1.symm

theorem eq_of_orderOf_two_of_cyclic_sylow {C : Type} [Group C] [Finite C]
    (hcyc : ∀ S : Sylow 2 C, IsCyclic ↥S) {a b : C} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ h ∈ zpowers a, ∀ k ∈ zpowers b, h * k = k * h := by
    intro h hh k hk
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hh
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hk
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have hsqz : ∀ {x : C}, orderOf x = 2 → ∀ h ∈ zpowers x, h ^ 2 = 1 := by
    intro x hx h hh
    have h1 : orderOf h ∣ 2 := by
      rw [← hx]
      exact (Subgroup.orderOf_dvd_natCard (zpowers x) hh).trans (by rw [Nat.card_zpowers])
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hW : IsPGroup 2 ↥(zpowers a ⊔ zpowers b) := by
    intro g
    obtain ⟨h, hh, k, hk, hg⟩ := mem_sup_of_commute' hcomm g.2
    have hh2 := hsqz ha h hh
    have hk2 := hsqz hb k hk
    have hg2 : (g : C) ^ 2 = 1 := by
      have hkh := hcomm h hh k hk
      rw [hg, pow_two]
      calc h * k * (h * k) = h * (k * h) * k := by group
        _ = h * (h * k) * k := by rw [← hkh]
        _ = (h * h) * (k * k) := by group
        _ = 1 := by rw [← pow_two, ← pow_two, hh2, hk2, one_mul]
    have hg2' : g ^ 2 = 1 := Subtype.ext hg2
    exact ⟨1, by simpa using hg2'⟩
  obtain ⟨S, hS⟩ := hW.exists_le_sylow
  have haS : a ∈ (S : Subgroup C) := hS (Subgroup.mem_sup_left (mem_zpowers a))
  have hbS : b ∈ (S : Subgroup C) := hS (Subgroup.mem_sup_right (mem_zpowers b))
  have := hcyc S
  let a' : ↥(S : Subgroup C) := ⟨a, haS⟩
  let b' : ↥(S : Subgroup C) := ⟨b, hbS⟩
  have ha' : orderOf a' = 2 := by rw [← Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf b' = 2 := by rw [← Subgroup.orderOf_coe]; exact hb
  have : Fintype ↥(S : Subgroup C) := Fintype.ofFinite _
  have h2dvd : 2 ∣ Fintype.card ↥(S : Subgroup C) := by
    have := orderOf_dvd_card (x := a')
    rwa [ha'] at this
  have hcard := IsCyclic.card_orderOf_eq_totient (α := ↥(S : Subgroup C)) (d := 2) h2dvd
  classical
  have h1 : (Finset.univ.filter (fun x : ↥(S : Subgroup C) => orderOf x = 2)).card ≤ 1 := by
    rw [hcard]; simp
  have := Finset.card_le_one.1 h1 a' (by simp [ha']) b' (by simp [hb'])
  exact congrArg Subtype.val this

end CFSG.GH74.GLS.IVK.Proofs2
