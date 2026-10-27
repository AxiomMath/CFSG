module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement

private theorem mul_inv_mem_of_commutator_mem {G : Type*} [Group G] {H : Subgroup G} {s w y : G}
    (hc : ⁅s, w⁆ ∈ H) (h : s * w * s⁻¹ * y⁻¹ ∈ H) : w * y⁻¹ ∈ H := by
  have e : (⁅s, w⁆)⁻¹ * (s * w * s⁻¹ * y⁻¹) = w * y⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [← e]
  exact mul_mem (inv_mem hc) h

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

private theorem φ_pow_mem_S' (k : ℕ) {y : X} (hy : y ∈ d.S) : (d.φ ^ k) y ∈ d.S := by
  have h1 := map_rangeSubgroup_le_D4 d.x₁_add (d.φ ^ k) _ (d.φ_pow_x₁ k)
  have hD : d.D.map (d.φ ^ k).toMonoidHom ≤ d.D := by
    rintro _ ⟨z, hz, rfl⟩
    exact d.φ_pow_mem_D k hz
  have hS : d.S.map (d.φ ^ k).toMonoidHom ≤ d.S := by
    rw [d.S_eq_sup, Subgroup.map_sup]
    exact sup_le_sup h1 hD
  exact hS ⟨y, hy, rfl⟩

theorem eq_conj_of_trivial_S_mod_F {α : MulAut X} (hS : ∀ y ∈ d.S, α y ∈ d.S)
    (hα : ∀ y ∈ d.S, α y * y⁻¹ ∈ d.F) : ∃ n ∈ d.S, α = MulAut.conj n := by
  obtain ⟨g, k, rfl⟩ := d.aut_eq α
  have := d.finite
  have hgB : g ∈ d.B := by
    rw [← d.normalizer_S]
    refine mem_normalizer_fintype fun s hs => ?_
    have hsurj : Function.Surjective fun s₀ : d.S =>
        (⟨(d.φ ^ k) s₀, d.φ_pow_mem_S' k s₀.2⟩ : d.S) :=
      Finite.surjective_of_injective fun a b hab => Subtype.ext ((d.φ ^ k).injective
        (congrArg Subtype.val hab))
    obtain ⟨s₀, hs₀⟩ := hsurj ⟨s, hs⟩
    have h1 := hS s₀ s₀.2
    rw [MulAut.mul_apply, MulAut.conj_apply] at h1
    have h2 : (d.φ ^ k) s₀ = s := congrArg Subtype.val hs₀
    rwa [h2] at h1
  obtain ⟨s, hs, j, hj, rfl⟩ := d.mem_B_iff.1 hgB
  obtain ⟨⟨l, m⟩, rfl⟩ := hj
  have hJN : d.torus (l, m) ∈ normalizer (d.S : Set X) := by
    rw [d.normalizer_S]
    exact d.J_le_B (MonoidHom.mem_range.2 ⟨(l, m), rfl⟩)
  have hw : ∀ y ∈ d.S, d.torus (l, m) * (d.φ ^ k) y * (d.torus (l, m))⁻¹ ∈ d.S :=
    fun y hy => (mem_normalizer_iff.1 hJN _).1 (d.φ_pow_mem_S' k hy)
  have key : ∀ y ∈ d.S, d.torus (l, m) * (d.φ ^ k) y * (d.torus (l, m))⁻¹ * y⁻¹ ∈ d.F := by
    intro y hy
    have h1 := hα y hy
    rw [MulAut.mul_apply, MulAut.conj_apply] at h1
    have h2 : s * (d.torus (l, m) * (d.φ ^ k) y * (d.torus (l, m))⁻¹) * s⁻¹ * y⁻¹ ∈ d.F := by
      rwa [show s * (d.torus (l, m) * (d.φ ^ k) y * (d.torus (l, m))⁻¹) * s⁻¹ * y⁻¹ =
        s * d.torus (l, m) * (d.φ ^ k) y * (s * d.torus (l, m))⁻¹ * y⁻¹ by group]
    have h3 : ⁅s, d.torus (l, m) * (d.φ ^ k) y * (d.torus (l, m))⁻¹⁆ ∈ d.F :=
      d.commutator_S_S (commutator_mem_commutator hs (hw y hy))
    exact mul_inv_mem_of_commutator_mem h3 h2
  have hx1 : ∀ a : d.Γ, (m : d.Γ) * a ^ 2 ^ k = a := by
    intro a
    have e : d.torus (l, m) * (d.φ ^ k) (d.x₁ a) * (d.torus (l, m))⁻¹ * (d.x₁ a)⁻¹ =
        d.x₁ ((m : d.Γ) * a ^ 2 ^ k + a) := by
      rw [d.φ_pow_x₁, d.torus_x₁, d.x₁_inv, d.x₁_add]
    have h := key (d.x₁ a) (d.U₁_le_S (d.x₁_mem_U₁ a))
    rw [e] at h
    exact CharTwo.add_eq_zero.1 (d.x₁_mem_D_iff.1 (d.F_le_D h))
  have hm : m = 1 := Units.ext (by simpa using hx1 1)
  have hk : ∀ c : d.Γ, c ^ 2 ^ k = c := fun c => by simpa [hm] using hx1 c
  have hφ : d.φ ^ k = 1 := d.φ_pow_eq_one_of_forall hk
  subst hm
  have hx2 : ∀ b : d.Γ₀, (l : d.Γ₀) * b = b := by
    intro b
    have e : d.torus (l, 1) * (d.φ ^ k) (d.x₂ b) * (d.torus (l, 1))⁻¹ * (d.x₂ b)⁻¹ =
        d.x₂ ((l : d.Γ₀) * b + b) := by
      rw [hφ, MulAut.one_apply, d.torus_x₂, d.x₂_inv, d.x₂_add]
    have h := key (d.x₂ b) (d.U₂_le_S (d.x₂_mem_U₂ b))
    rw [e] at h
    have hc := eq_neg_of_add_eq_zero_left (d.x₂_mem_F_iff.1 h)
    rwa [neg_eq_of_add_eq_zero_left (d.add_self_Γ₀ b)] at hc
  have hl : l = 1 := Units.ext (by simpa using hx2 1)
  subst hl
  refine ⟨s, hs, ?_⟩
  rw [hφ, show d.torus (1, 1) = 1 from map_one d.torus, mul_one, mul_one]

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
