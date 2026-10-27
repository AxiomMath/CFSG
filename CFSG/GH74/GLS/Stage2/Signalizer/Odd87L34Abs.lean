module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Facts

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem le_closure_exc {G : Type*} [Group G] {a : G} (ha : a * a = 1) {X : Subgroup G} {p e : ℕ}
    (haN : a ∈ Subgroup.normalizer (X : Set G)) (hcomm : ⁅X, Subgroup.zpowers a⁆ = X)
    (hexp : ∀ x ∈ X, x ^ p = 1) (hord : ∀ w ∈ X, w ^ e = 1)
    (D : Set G) (hD : ∀ d ∈ D, d ∈ Subgroup.normalizer (X : Set G)) (Exc : Set G)
    (hwit : ∀ y : G, y ≠ 1 → y ^ p = 1 → a * y * a * y = 1 → y ∈ Exc ∨
        (∃ d ∈ D, (y * (d * y * d⁻¹)) ^ e ≠ 1) ∨
        (∃ d ∈ D, ∃ d' ∈ D, (y * (d * y * d⁻¹) * (d' * y * d'⁻¹)) ^ e ≠ 1)) :
    X ≤ Subgroup.closure Exc := by
  have hconj : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    exact (Subgroup.mem_set_normalizer_iff.1 hg x).1 hx
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hgen : ∀ x ∈ X, ⁅x, a⁆ ∈ Subgroup.closure Exc := by
    intro x hx
    set c : G := ⁅x, a⁆ with hc_def
    have hcX : c ∈ X := by
      have h1 : a * x⁻¹ * a⁻¹ ∈ X := hconj a haN x⁻¹ (X.inv_mem hx)
      have h2 : x * (a * x⁻¹ * a⁻¹) ∈ X := X.mul_mem hx h1
      have : c = x * (a * x⁻¹ * a⁻¹) := by
        rw [hc_def, commutatorElement_def]
        group
      rw [this]
      exact h2
    have hcp : c ^ p = 1 := hexp c hcX
    have ha2 : ∀ t : G, a * (a * t) = t := fun t => by rw [← mul_assoc, ha, one_mul]
    have hcinv : a * c * a * c = 1 := by
      rw [hc_def, commutatorElement_def, ha_inv]
      simp only [mul_assoc, ha2, ha, one_mul, inv_mul_cancel_left, mul_inv_cancel_left]
    by_cases hc1 : c = 1
    · rw [hc1]
      exact Subgroup.one_mem _
    · rcases hwit c hc1 hcp hcinv with hmem | ⟨d, hd, hne⟩ | ⟨d, hd, d', hd', hne⟩
      · exact Subgroup.subset_closure hmem
      · exfalso
        apply hne
        apply hord
        exact X.mul_mem hcX (hconj d (hD d hd) c hcX)
      · exfalso
        apply hne
        apply hord
        exact X.mul_mem (X.mul_mem hcX (hconj d (hD d hd) c hcX)) (hconj d' (hD d' hd') c hcX)
  conv_lhs => rw [← hcomm]
  rw [Subgroup.commutator_def, Subgroup.closure_le]
  rintro g ⟨x, hx, k, hk, rfl⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hmod : a ^ m = 1 ∨ a ^ m = a := by
    have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
    have hm : m = 2 * (m / 2) + m % 2 := (Int.mul_ediv_add_emod m 2).symm
    rcases Int.emod_two_eq_zero_or_one m with h | h
    · left
      rw [hm, h, add_zero, zpow_mul, h2, one_zpow]
    · right
      rw [hm, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  rcases hmod with h | h
  · rw [h, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · rw [h]
    exact hgen x hx

theorem l34Concl_of_mulEquiv {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (ψ : Y ≃* Y') {α : MulAut Y} {X : Subgroup (MulAut Y)}
    (h : L34Concl Y' (MulAut.congr ψ α) (X.map (MulAut.congr ψ).toMonoidHom)) :
    L34Concl Y α X := by
  have hin := map_innSub ψ
  generalize MulAut.congr ψ = Φ at h hin
  unfold L34Concl at h ⊢
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h
  have hinj : Function.Injective Φ.toMonoidHom := Φ.injective
  have hsup : (innSub Y ⊔ X).map Φ.toMonoidHom = innSub Y' ⊔ X.map Φ.toMonoidHom := by
    rw [Transport.map_sup, hin]
  have hJ : (innSub Y ⊓ centralizer ({α} : Set (MulAut Y))).map Φ.toMonoidHom =
      innSub Y' ⊓ centralizer ({Φ α} : Set (MulAut Y')) := by
    rw [Transport.map_inf, hin, Transport.map_centralizer_singleton]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hinj]
    exact c1
  · apply (Subgroup.map_eq_bot_iff_of_injective _ hinj).1
    rw [Transport.map_inf, hin]
    exact c2
  · intro hmem
    apply c3
    have := Subgroup.mem_map_of_mem Φ.toMonoidHom hmem
    rw [hsup] at this
    exact this
  · exact Transport.isPGL3Four_of_mulEquiv (Transport.subEquiv Φ hsup).symm c4
  · apply Subgroup.map_injective hinj
    rw [Transport.map_inf, Transport.map_inf, hin, Transport.map_centralizer_singleton,
      Transport.map_centralizer]
    exact c5
  · exact Transport.isL2_of_mulEquiv (Transport.subEquiv Φ hJ).symm c6
  · apply Subgroup.map_injective hinj
    rw [Transport.map_inf, Transport.map_sup, Transport.map_sup, Transport.map_sup,
      Transport.map_zpowers, hin, Transport.map_centralizer, hJ]
    exact c7

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
