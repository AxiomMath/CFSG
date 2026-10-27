module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideFixed

public section

namespace CFSG.AGLEmbedding.SPLMSide

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem false_of_moved_component {p : ℕ} [hp : Fact p.Prime] {Λ Z₀ : Subgroup G}
    (hΛ : CFSG.IsQuasisimple Λ) {u t : G}
    (hu : u ∈ Subgroup.normalizer (Λ : Set G)) (hup : u ^ p = 1) (hut : u * t = t * u)
    (hc1 : ∀ a ∈ Λ, ∀ b ∈ Λ, a * (t * b * t⁻¹) = (t * b * t⁻¹) * a)
    (hc2 : ∀ a ∈ Λ, ∀ b ∈ Λ, a * (t * (t * b * t⁻¹) * t⁻¹) = (t * (t * b * t⁻¹) * t⁻¹) * a)
    (hZ₀ : ∀ a ∈ Λ, ∀ x ∈ Z₀, a * x = x * a)
    (hcomm : ∀ a ∈ Λ, ∀ b ∈ Λ, (a * (t * b * t⁻¹)) * u = u * (a * (t * b * t⁻¹)) →
      (a * (t * b * t⁻¹))⁻¹ * (t * (a * (t * b * t⁻¹)) * t⁻¹) ∈ Z₀)
    (hcen : ∀ φ ∈ Λ, (∀ a ∈ Λ, a * φ = φ * a) → (∃ k : ℕ, φ ^ p ^ k = 1) →
      φ * t = t * φ ∧ φ * u = u * φ) : False := by
  classical
  let N : Subgroup Λ := Subgroup.center Λ ⊓
    (Subgroup.centralizer ({t, u} : Set G)).subgroupOf Λ
  have hmemN : ∀ n : Λ, n ∈ N ↔ n ∈ Subgroup.center Λ ∧ (n : G) * t = t * n ∧
      (n : G) * u = u * n := by
    intro n
    simp only [N, Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.symm, h3.symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.symm, h3.symm⟩
  have hN : ¬ p ∣ (N.subgroupOf (Subgroup.center Λ)).index := by
    obtain ⟨PZ⟩ : Nonempty (Sylow p (Subgroup.center Λ)) := inferInstance
    have hle : (PZ : Subgroup (Subgroup.center Λ)) ≤ N.subgroupOf (Subgroup.center Λ) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf, hmemN]
      obtain ⟨k, hk⟩ := (PZ.isPGroup' ⟨x, hx⟩)
      have hk' : ((x : Λ) : G) ^ p ^ k = 1 := by
        have := congrArg (fun y : PZ => (((y : Subgroup.center Λ) : Λ) : G)) hk
        simpa using this
      have hcx : ∀ a ∈ Λ, a * ((x : Λ) : G) = ((x : Λ) : G) * a := fun a ha =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨a, ha⟩)
      obtain ⟨h1, h2⟩ := hcen _ (x : Λ).2 hcx ⟨k, hk'⟩
      exact ⟨x.2, h1, h2⟩
    intro hdvd
    exact PZ.not_dvd_index (dvd_trans hdvd (Subgroup.index_dvd_of_le hle))
  have hcN : ∀ n ∈ N, (⟨u * (n : G) * u⁻¹, (Subgroup.mem_normalizer_iff.mp hu n).mp n.2⟩ : Λ) ∈ N
      := by
    intro n hn
    have hnu := ((hmemN n).mp hn).2.2
    have : (⟨u * (n : G) * u⁻¹, (Subgroup.mem_normalizer_iff.mp hu n).mp n.2⟩ : Λ) = n :=
      Subtype.ext (by show u * (n : G) * u⁻¹ = n; rw [← hnu]; group)
    rw [this]; exact hn
  obtain ⟨y, hyZ, hyN⟩ := exists_noncentral_mod hΛ hu hup N hN hcN
  obtain ⟨-, hφt, hφu⟩ := (hmemN _).mp hyN
  set φ : G := (y : G)⁻¹ * (u * (y : G) * u⁻¹) with hφdef
  have hφt' : φ * t = t * φ := by simpa [hφdef] using hφt
  have huy : u * (y : G) * u⁻¹ = (y : G) * φ := by rw [hφdef]; group
  have hw : ((y : G) * (t * (y : G)⁻¹ * t⁻¹)) * u = u * ((y : G) * (t * (y : G)⁻¹ * t⁻¹)) := by
    have h1 : u * ((y : G) * (t * (y : G)⁻¹ * t⁻¹)) * u⁻¹ =
        (u * (y : G) * u⁻¹) * t * (u * (y : G) * u⁻¹)⁻¹ * t⁻¹ := by
      have hut' : u * t * u⁻¹ = t := by rw [hut]; group
      calc u * ((y : G) * (t * (y : G)⁻¹ * t⁻¹)) * u⁻¹
          = (u * (y : G) * u⁻¹) * (u * t * u⁻¹) * (u * (y : G) * u⁻¹)⁻¹ *
              (u * t * u⁻¹)⁻¹ := by group
        _ = _ := by rw [hut']
    have h2 : (u * (y : G) * u⁻¹) * t * (u * (y : G) * u⁻¹)⁻¹ * t⁻¹ =
        (y : G) * (t * (y : G)⁻¹ * t⁻¹) := by
      rw [huy]
      calc (y : G) * φ * t * ((y : G) * φ)⁻¹ * t⁻¹ =
            (y : G) * (φ * t) * φ⁻¹ * (y : G)⁻¹ * t⁻¹ := by group
        _ = (y : G) * (t * φ) * φ⁻¹ * (y : G)⁻¹ * t⁻¹ := by rw [hφt']
        _ = _ := by group
    have h3 := h1.trans h2
    calc ((y : G) * (t * (y : G)⁻¹ * t⁻¹)) * u
        = (u * ((y : G) * (t * (y : G)⁻¹ * t⁻¹)) * u⁻¹) * u := by rw [h3]
      _ = _ := by group
  have hg := hcomm (y : G) y.2 (y : G)⁻¹ (Λ.inv_mem y.2) hw
  set y₁ : G := t * (y : G) * t⁻¹ with hy₁
  set y₂ : G := t * y₁ * t⁻¹ with hy₂
  set g : G := ((y : G) * (t * (y : G)⁻¹ * t⁻¹))⁻¹ *
    (t * ((y : G) * (t * (y : G)⁻¹ * t⁻¹)) * t⁻¹) with hgdef
  have hgform : (y : G)⁻¹ = y₁⁻¹ * g * y₂ * y₁⁻¹ := by
    rw [hgdef, hy₂, hy₁]; group
  apply hyZ
  rw [Subgroup.mem_center_iff]
  intro a
  have ha := a.2
  have h1 : Commute (a : G) y₁⁻¹ := by
    have := hc1 a ha y y.2
    rw [← hy₁] at this
    exact Commute.inv_right this
  have h2 : Commute (a : G) g := hZ₀ a ha g hg
  have h3 : Commute (a : G) y₂ := by
    have := hc2 a ha y y.2
    rwa [← hy₁, ← hy₂] at this
  have hinv : Commute (a : G) (y : G)⁻¹ := by
    rw [hgform]
    exact ((h1.mul_right h2).mul_right h3).mul_right h1
  exact Subtype.ext (Commute.inv_right_iff.mp hinv).eq

end CFSG.AGLEmbedding.SPLMSide
