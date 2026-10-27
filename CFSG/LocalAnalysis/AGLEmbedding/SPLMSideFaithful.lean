module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideRankSix
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding.SPLMSide

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_centralizer {Λ : Subgroup G} {g v : G}
    (hg : g ∈ Subgroup.normalizer (Λ : Set G)) (hv : v ∈ Subgroup.centralizer (Λ : Set G)) :
    g * v * g⁻¹ ∈ Subgroup.centralizer (Λ : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hv ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ Λ := by
    have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr
    apply this
    simpa [mul_assoc] using hy
  have h := hv _ hy'
  calc y * (g * v * g⁻¹) = g * ((g⁻¹ * y * g) * v) * g⁻¹ := by group
    _ = g * (v * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = g * v * g⁻¹ * y := by group

theorem mem_normalizer_of_rank {p r : ℕ} [Fact p.Prime] {u c : G} {X Λ : Subgroup G}
    (hΛ : CFSG.IsComponent Λ) (hup : ∃ k : ℕ, u ^ p ^ k = 1)
    (hu : u ∈ Subgroup.normalizer (Λ : Set G)) (hcC : c ∈ Subgroup.centralizer ({u} : Set G))
    (hcX : ∀ x ∈ X, c * x = x * c) (hcr : ∃ k : ℕ, c ^ r ^ k = 1) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hXu : X ≤ Subgroup.centralizer ({u} : Set G))
    (hXel : CFSG.Open.IsElemAbelian p X) (hXcard : Nat.card X = p ^ 2)
    (hXE : ∀ Λ' : Subgroup G, CFSG.IsComponent Λ' → ∀ x ∈ X, ∀ a ∈ Λ', x * a = a * x)
    (hZX : ∀ φ ∈ Λ, (∀ a ∈ Λ, a * φ = φ * a) → (∃ k : ℕ, φ ^ p ^ k = 1) → φ ∈ X)
    (hrank : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({u} : Set G) →
      CFSG.Open.IsElemAbelian p A → Nat.card A < p ^ 6)
    (hpZ : p ∣ (Subgroup.center Λ).index) : c ∈ Subgroup.normalizer (Λ : Set G) := by
  by_contra hcN
  have hcu : c * u = u * c := (Subgroup.mem_centralizer_iff.mp hcC u (Set.mem_singleton u)).symm
  have hci : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → c ^ i ∉ Subgroup.normalizer (Λ : Set G) := by
    intro i hi1 hi4 hmem
    apply hcN
    obtain ⟨k, hk⟩ := hcr
    have hcop : i.Coprime (orderOf c) := by
      have hir : i.Coprime r := ((Nat.Prime.coprime_iff_not_dvd hr).mpr
        (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))).symm
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk) (hir.pow_right k)
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hj]
    exact Subgroup.pow_mem _ hmem j
  obtain ⟨A, hA, hAel, hAcard⟩ := exists_elemAbelian_six hΛ hu hup hcu hci hcX
    (fun x hx => (Subgroup.mem_centralizer_iff.mp (hXu hx) u (Set.mem_singleton u)).symm)
    hXE hXel hXcard hZX hpZ
  exact absurd (hrank A hA hAel) (not_lt.mpr hAcard)

omit [Finite G] in
theorem inf_centralizer_le_of_moved {c : G} {T X Λ : Subgroup G} (hXT : X ≤ T)
    (hXE : ∀ x ∈ X, ∀ a ∈ Λ, x * a = a * x) (hTN : T ≤ Subgroup.normalizer (Λ : Set G))
    (hcN : c ∈ Subgroup.normalizer (Λ : Set G)) (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T)
    (hirr : ∀ V : Subgroup G, X ≤ V → V ≤ T → (∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) →
      (∀ v ∈ V, c * v * c⁻¹ ∈ V) → V = X ∨ V = T)
    (hmov : ∃ t ∈ T, t ∉ Subgroup.centralizer (Λ : Set G)) :
    T ⊓ Subgroup.centralizer (Λ : Set G) ≤ X := by
  have hV := hirr (T ⊓ Subgroup.centralizer (Λ : Set G))
    (le_inf hXT (fun x hx => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hXE x hx y hy).symm)) inf_le_left
    (fun t ht v hv => ⟨T.mul_mem (T.mul_mem ht hv.1) (T.inv_mem ht),
      conj_mem_centralizer (hTN ht) hv.2⟩)
    (fun v hv => ⟨hcT v hv.1, conj_mem_centralizer hcN hv.2⟩)
  rcases hV with hV | hV
  · rw [hV]
  · exfalso
    obtain ⟨t, ht, htc⟩ := hmov
    apply htc
    have : t ∈ T ⊓ Subgroup.centralizer (Λ : Set G) := by rw [hV]; exact ht
    exact this.2

end CFSG.AGLEmbedding.SPLMSide
