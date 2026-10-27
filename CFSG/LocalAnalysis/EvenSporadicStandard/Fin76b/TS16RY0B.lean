module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RY0A
public import CFSG.Assembly.OrderReductions.StrongEmbedding

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem exists_conj_order_three {C : Type*} [Group C] [Finite C] (hC : Nat.card C = 1920)
    {a b : C} (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ c : C, c * a * c⁻¹ = b ∨ c * a * c⁻¹ = b⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsyl : ∀ x : C, orderOf x = 3 → ¬ 3 ∣ (zpowers x).index ∧ IsPGroup 3 (zpowers x) := by
    intro x hx
    have hcard : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
    refine ⟨?_, IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)⟩
    have h1 := Subgroup.card_mul_index (zpowers x)
    rw [hcard, hC] at h1
    intro hd
    obtain ⟨k, hk⟩ := hd
    rw [hk] at h1
    omega
  obtain ⟨hia, hpa⟩ := hsyl a ha
  obtain ⟨hib, hpb⟩ := hsyl b hb
  let P : Sylow 3 C := hpa.toSylow hia
  let Q : Sylow 3 C := hpb.toSylow hib
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P Q
  refine ⟨c, ?_⟩
  have hmem : c * a * c⁻¹ ∈ zpowers b := by
    have h1 : c • (P : Subgroup C) = (Q : Subgroup C) := by
      have := congrArg (fun S : Sylow 3 C => (S : Subgroup C)) hc
      exact this
    have h2 : c * a * c⁻¹ ∈ c • (P : Subgroup C) :=
      ⟨a, mem_zpowers a, ConjAct.smul_def _ _⟩
    rw [h1] at h2
    exact h2
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  have hk' : b ^ (k % 3) = c * a * c⁻¹ := by
    have := zpow_mod_orderOf b k
    rw [hb] at this
    simp only [Nat.cast_ofNat] at this
    rw [this]
    exact hk
  have hb2 : b ^ (2 : ℤ) = b⁻¹ := by
    have h3 : b ^ (3 : ℤ) = 1 := by
      have := pow_orderOf_eq_one b
      rw [hb] at this
      exact_mod_cast this
    calc b ^ (2 : ℤ) = b ^ (3 : ℤ) * b⁻¹ := by rw [← zpow_neg_one, ← zpow_add]; norm_num
      _ = b⁻¹ := by rw [h3, one_mul]
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hk'
    have : a = 1 := by
      have h := hk'.symm
      rw [mul_inv_eq_one] at h
      simpa using h
    rw [this, orderOf_one] at ha
    omega
  · left
    rw [h1, zpow_one] at hk'
    exact hk'.symm
  · right
    rw [h2, hb2] at hk'
    exact hk'.symm

theorem S16Model.of_class {X : Type*} [Group X] [Finite X] {t₀ β₀ : X} (h₀ : S16Model X t₀ β₀)
    (hcls : ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ g : X, t = g * t₀ * g⁻¹)
    (hcard : Nat.card ↥(centralizer ({t₀} : Set X)) = 1920)
    (hβ₀ : β₀ ∈ centralizer ({t₀} : Set X)) (hβ₀3 : orderOf β₀ = 3) :
    ∀ t β : X, orderOf t = 2 → (∃ g : X, g * g = t) → β ∈ centralizer ({t} : Set X) →
      orderOf β = 3 → S16Model X t β := by
  intro t β ht2 hsq hβt hβ3
  obtain ⟨g, rfl⟩ := hcls t ht2 hsq
  set β' : X := g⁻¹ * β * g with hβ'
  have hβ't : β' ∈ centralizer ({t₀} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.1 hβt
    show β' * t₀ = t₀ * β'
    calc β' * t₀ = g⁻¹ * (β * (g * t₀ * g⁻¹)) * g := by rw [hβ']; group
      _ = g⁻¹ * ((g * t₀ * g⁻¹) * β) * g := by rw [h1]
      _ = t₀ * β' := by rw [hβ']; group
  have hβ'3 : orderOf β' = 3 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) β
    have h2 : (MulAut.conj g⁻¹) β = β' := by simp [MulAut.conj_apply, hβ']
    rw [h2, hβ3] at h1
    exact h1
  obtain ⟨c, hc⟩ := exists_conj_order_three (C := ↥(centralizer ({t₀} : Set X))) hcard
    (a := ⟨β₀, hβ₀⟩) (b := ⟨β', hβ't⟩) (by rw [← Subgroup.orderOf_coe]; exact hβ₀3)
    (by rw [← Subgroup.orderOf_coe]; exact hβ'3)
  have hct : (c : X) * t₀ = t₀ * (c : X) := mem_centralizer_singleton_iff.1 c.2
  have hρt : g * (c : X) * t₀ * (g * (c : X))⁻¹ = g * t₀ * g⁻¹ := by
    calc g * (c : X) * t₀ * (g * (c : X))⁻¹ = g * (((c : X) * t₀) * (c : X)⁻¹) * g⁻¹ := by group
      _ = g * t₀ * g⁻¹ := by rw [hct]; group
  have hmodel := h₀.of_mulEquiv (MulAut.conj (g * (c : X)))
  simp only [MulAut.conj_apply] at hmodel
  rw [hρt] at hmodel
  rcases hc with hc | hc
  · have hc' : (c : X) * β₀ * (c : X)⁻¹ = β' := congrArg Subtype.val hc
    have : g * (c : X) * β₀ * (g * (c : X))⁻¹ = β := by
      calc g * (c : X) * β₀ * (g * (c : X))⁻¹ = g * ((c : X) * β₀ * (c : X)⁻¹) * g⁻¹ := by group
        _ = β := by rw [hc', hβ']; group
    rw [this] at hmodel
    exact hmodel
  · have hc' : (c : X) * β₀ * (c : X)⁻¹ = β'⁻¹ := congrArg Subtype.val hc
    have : g * (c : X) * β₀ * (g * (c : X))⁻¹ = β⁻¹ := by
      calc g * (c : X) * β₀ * (g * (c : X))⁻¹ = g * ((c : X) * β₀ * (c : X)⁻¹) * g⁻¹ := by group
        _ = β⁻¹ := by rw [hc', hβ']; group
    rw [this] at hmodel
    have := hmodel.inv
    rwa [inv_inv] at this

end CFSG.EvenSporadicStandard.Fin76b
