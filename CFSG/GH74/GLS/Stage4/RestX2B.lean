module

public import CFSG.GH74.GLS.Stage4.RestX2A
public import CFSG.GH74.GLS.Stage4.RestZB
public import CFSG.GH74.GLS.Stage4.RestP93

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank DodecA
open scoped Pointwise

variable {G : Type} [Group G] {D : Ch6Notation G}

theorem Ch6S6.mem_R₂_of_inv (hS : Ch6S6 D) (hb : Ch6Basics D) {y : G} (hyP : y ∈ D.P)
    (hy : D.z * y * D.z⁻¹ = y⁻¹) : y ∈ D.R₂ := by
  have hX₁K : D.X₁ ≤ D.K₁ := by rw [hb.K₁_eq]; exact le_sup_left
  have hnorm : D.X₁ ≤ normalizer (D.R₂ : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      exact hS.K₁_normR₂ x (hX₁K hx) r hr
    · intro hr
      have := hS.K₁_normR₂ x⁻¹ (D.K₁.inv_mem (hX₁K hx)) _ hr
      simpa [mul_assoc] using this
  have hmul : (↑(D.R₂ ⊔ D.X₁) : Set G) = (D.R₂ : Set G) * (D.X₁ : Set G) :=
    coe_mul_of_right_le_normalizer_left D.R₂ D.X₁ hnorm
  have hyP' : y ∈ (D.R₂ : Set G) * (D.X₁ : Set G) := by
    rw [← hmul, ← hS.P_eq]
    exact hyP
  obtain ⟨r, hr, x, hx, rfl⟩ := hyP'
  have hzr : D.z * r * D.z⁻¹ ∈ D.R₂ := hS.K₁_normR₂ _ hb.z_mem_K₁ r hr
  have hzx : D.z * x * D.z⁻¹ = x := by
    have h1 := hb.K_comm x (hX₁K hx) D.z hb.z_mem_K₂
    rw [← h1]
    group
  have hxr : x * (D.z * r * D.z⁻¹) * x⁻¹ ∈ D.R₂ := hS.K₁_normR₂ x (hX₁K hx) _ hzr
  have h2 : (D.z * r * D.z⁻¹) * x = x⁻¹ * r⁻¹ := by
    have e : D.z * (r * x) * D.z⁻¹ = (D.z * r * D.z⁻¹) * (D.z * x * D.z⁻¹) := by group
    rw [e, hzx] at hy
    rw [hy]
    group
  have hxx : x * x ∈ D.R₂ := by
    have e : x * x = (x * (D.z * r * D.z⁻¹) * x⁻¹)⁻¹ * r⁻¹ := by
      calc x * x = (x * (D.z * r * D.z⁻¹) * x⁻¹)⁻¹ * (x * ((D.z * r * D.z⁻¹) * x)) := by group
        _ = (x * (D.z * r * D.z⁻¹) * x⁻¹)⁻¹ * (x * (x⁻¹ * r⁻¹)) := by rw [h2]
        _ = (x * (D.z * r * D.z⁻¹) * x⁻¹)⁻¹ * r⁻¹ := by group
    rw [e]
    exact D.R₂.mul_mem (D.R₂.inv_mem hxr) (D.R₂.inv_mem hr)
  have hxR : x ∈ D.R₂ := by
    obtain ⟨k, hk⟩ := hb.prime.odd_of_ne_two hb.p_ne_two
    have h6 : (x * x) ^ k * x = 1 := by
      rw [← pow_two, ← pow_mul, ← pow_succ, ← hk]
      exact hb.X₁_exp x hx
    have : x = ((x * x) ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h6
    rw [this]
    exact D.R₂.inv_mem (pow_mem hxx k)
  exact D.R₂.mul_mem hr hxR

theorem Ch6Pre.a_conj (h : Ch6Pre D) :
    D.u ∈ D.H ∧ D.a * D.z * D.a⁻¹ = D.z * D.u ∧ D.a * D.u * D.a⁻¹ = D.z ∧
      D.a ^ 2 * D.z * (D.a ^ 2)⁻¹ = D.u := by
  have hb := h.basics
  have hzz := hb.z_mul_z
  have hzH := hb.z_mem_H
  have haN := hb.a_normH
  have ha3 := hb.a_cube
  have hcyc := h.pre.a_cycle
  have hcomm_z_a3 : D.a ^ 3 * D.z = D.z * D.a ^ 3 := hb.H_comm _ ha3 _ hzH
  have hu : D.u ∈ D.H := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ haN) D.z).1 hzH
    simpa [Ch6Notation.u] using this
  have hzu_comm : D.u * D.z = D.z * D.u := (hb.H_comm D.z hzH D.u hu).symm
  have hu' : D.a * D.z * D.a⁻¹ = D.z * D.u := by
    calc D.a * D.z * D.a⁻¹
        = D.a⁻¹ * D.a⁻¹ * (D.a ^ 3 * D.z * (D.a ^ 3)⁻¹) * D.a * D.a := by group
      _ = D.a⁻¹ * (D.a⁻¹ * D.z * D.a) * D.a := by rw [hcomm_z_a3]; group
      _ = D.z * D.u := hcyc
  have hauz : D.a * D.u * D.a⁻¹ = D.z := by
    simp only [Ch6Notation.u]
    group
  refine ⟨hu, hu', hauz, ?_⟩
  have e : D.a ^ 2 * D.z * (D.a ^ 2)⁻¹ = D.a * (D.a * D.z * D.a⁻¹) * D.a⁻¹ := by
    rw [pow_two]; group
  rw [e, hu']
  have e2 : D.a * (D.z * D.u) * D.a⁻¹ = (D.a * D.z * D.a⁻¹) * (D.a * D.u * D.a⁻¹) := by group
  rw [e2, hu', hauz]
  calc D.z * D.u * D.z = D.z * (D.u * D.z) := by group
    _ = D.z * (D.z * D.u) := by rw [hzu_comm]
    _ = (D.z * D.z) * D.u := by group
    _ = D.u := by rw [hzz, one_mul]

theorem Ch6Pre.noAllX2 (h : Ch6Pre D) (hS : Ch6S6 D) : ¬ D.AllX2 := by
  rintro ⟨α, γ, hαγ, hSh⟩
  have hb := h.basics
  have hp := h.pre
  obtain ⟨hPα, hPβ, hPγ, hPδ⟩ := Ch6Notation.shape_le hSh
  rw [Ch6Notation.B_false] at hPβ hPδ
  obtain ⟨-, hu', -, huu⟩ := h.a_conj
  have ha := hb.a_normH
  have ha3 := hb.a_cube
  have hX₂ : HInv D.H D.X₂ := hb.H_norm_X₂
  have hX₂K : D.X₂ ≤ D.K₂ := by rw [hb.K₂_eq]; exact le_sup_left
  have hX₂ne : D.X₂ ≠ ⊥ := ne_bot_of_card (by have := hb.q₂_ge; omega) hb.card_X₂
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q : Subgroup G, Q = conjBy (D.a ^ 2) D.X₂ := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q : Subgroup G, Q = conjBy D.a D.X₂ := ⟨_, rfl⟩
  have hmem₁ : ∀ q, q ∈ Q₁ ↔ D.a ^ 2 * q * (D.a ^ 2)⁻¹ ∈ D.X₂ := fun q => by
    rw [hQ₁, mem_conjBy_iff]
  have hmem₂ : ∀ q, q ∈ Q₂ ↔ D.a * q * D.a⁻¹ ∈ D.X₂ := fun q => by
    rw [hQ₂, mem_conjBy_iff]
  have hQ₁P : Q₁ ≤ D.P := by rw [hQ₁]; exact hPδ
  have hQ₂P : Q₂ ≤ D.P := by rw [hQ₂]; exact hPβ
  have hQ₁H : HInv D.H Q₁ := by rw [hQ₁]; exact hX₂.map_conjBy (pow_mem ha 2)
  have hQ₂H : HInv D.H Q₂ := by rw [hQ₂]; exact hX₂.map_conjBy ha
  have hQ₁c : ∀ q ∈ Q₁, ∀ q' ∈ Q₁, q * q' = q' * q := by
    rw [hQ₁]; exact comm_conjBy hb.X₂_comm
  have hQ₂c : ∀ q ∈ Q₂, ∀ q' ∈ Q₂, q * q' = q' * q := by
    rw [hQ₂]; exact comm_conjBy hb.X₂_comm
  have hQ₁ne : Q₁ ≠ ⊥ := by rw [hQ₁]; exact conjBy_ne_bot hX₂ne
  have hQ₂ne : Q₂ ≠ ⊥ := by rw [hQ₂]; exact conjBy_ne_bot hX₂ne
  have hzQ₁ : ∀ q ∈ Q₁, D.z * q * D.z⁻¹ = q⁻¹ := by
    intro q hq
    rw [hmem₁] at hq
    have h1 := hp.u_inv_X₂ _ hq
    have e : D.z * q * D.z⁻¹ = (D.a ^ 2)⁻¹ * ((D.a ^ 2 * D.z * (D.a ^ 2)⁻¹) *
        (D.a ^ 2 * q * (D.a ^ 2)⁻¹) * (D.a ^ 2 * D.z * (D.a ^ 2)⁻¹)⁻¹) * D.a ^ 2 := by group
    rw [e, huu, h1]
    group
  have hzQ₂ : ∀ q ∈ Q₂, D.z * q * D.z⁻¹ = q⁻¹ := by
    intro q hq
    rw [hmem₂] at hq
    have h1 := hp.u_inv_X₂ _ hq
    have e : D.z * q * D.z⁻¹ = D.a⁻¹ * ((D.a * D.z * D.a⁻¹) * (D.a * q * D.a⁻¹) *
        (D.a * D.z * D.a⁻¹)⁻¹) * D.a := by group
    rw [e, hu']
    have e3 : (D.z * D.u) * (D.a * q * D.a⁻¹) * (D.z * D.u)⁻¹ =
        D.z * (D.u * (D.a * q * D.a⁻¹) * D.u⁻¹) * D.z⁻¹ := by group
    rw [e3, h1]
    have hx' : (D.a * q * D.a⁻¹)⁻¹ ∈ D.X₂ := D.X₂.inv_mem hq
    have h4 := hb.K_comm D.z hb.z_mem_K₁ _ (hX₂K hx')
    have h5 : D.z * (D.a * q * D.a⁻¹)⁻¹ * D.z⁻¹ = (D.a * q * D.a⁻¹)⁻¹ := by
      rw [h4]; group
    rw [h5]
    group
  have hQ₁R : Q₁ ≤ D.R₂ := fun q hq => hS.mem_R₂_of_inv hb (hQ₁P hq) (hzQ₁ q hq)
  have hQ₂R : Q₂ ≤ D.R₂ := fun q hq => hS.mem_R₂_of_inv hb (hQ₂P hq) (hzQ₂ q hq)
  have hcomm12 : ∀ q₁ ∈ Q₁, ∀ q₂ ∈ Q₂, q₁ * q₂ = q₂ * q₁ := by
    intro q₁ hq₁ q₂ hq₂
    rw [hmem₁] at hq₁
    have hy : D.a * q₁ * D.a⁻¹ ∈ Q₂ := by
      rw [hmem₂]
      have e : D.a * (D.a * q₁ * D.a⁻¹) * D.a⁻¹ = D.a ^ 2 * q₁ * (D.a ^ 2)⁻¹ := by
        rw [pow_two]; group
      rw [e]
      exact hq₁
    have hq₂' := (hmem₂ q₂).1 hq₂
    have h1 := hp.X₂_central _ hq₂' _ (hQ₂P hy)
    have e1 : q₁ * q₂ = D.a⁻¹ * ((D.a * q₁ * D.a⁻¹) * (D.a * q₂ * D.a⁻¹)) * D.a := by group
    have e2 : q₂ * q₁ = D.a⁻¹ * ((D.a * q₂ * D.a⁻¹) * (D.a * q₁ * D.a⁻¹)) * D.a := by group
    rw [e1, e2, h1]
  have hQ₁repr : ∀ q ∈ Q₁, ∃ x ∈ D.X₂, q = D.a * x * D.a⁻¹ := by
    intro q hq
    rw [hmem₁] at hq
    refine ⟨(D.a ^ 3)⁻¹ * (D.a ^ 2 * q * (D.a ^ 2)⁻¹) * D.a ^ 3, ?_, ?_⟩
    · have := hX₂ _ (D.H.inv_mem ha3) _ hq
      rwa [inv_inv] at this
    · group
  have hQ₂repr : ∀ q ∈ Q₂, ∃ x ∈ D.X₂, q = D.a ^ 2 * x * (D.a ^ 2)⁻¹ := by
    intro q hq
    rw [hmem₂] at hq
    refine ⟨(D.a ^ 3)⁻¹ * (D.a * q * D.a⁻¹) * D.a ^ 3, ?_, ?_⟩
    · have := hX₂ _ (D.H.inv_mem ha3) _ hq
      rwa [inv_inv] at this
    · group
  have hcent₁ : ∀ q ∈ Q₁, ∀ y ∈ D.A α, q * y = y * q := by
    intro q hq y hy
    obtain ⟨x, hx, rfl⟩ := hQ₁repr q hq
    exact centralizes_of_conjBy_le hPα hp.X₂_central x hx y hy
  have hcent₂ : ∀ q ∈ Q₂, ∀ y ∈ D.A γ, q * y = y * q := by
    intro q hq y hy
    obtain ⟨x, hx, rfl⟩ := hQ₂repr q hq
    exact centralizes_of_conjBy_le hPγ hp.X₂_central x hx y hy
  have hw₁x : ∀ x ∈ D.X₂, D.w₁ * x * D.w₁⁻¹ = x := by
    intro x hx
    have := hb.K_comm D.w₁ hb.w₁_mem x (hX₂K hx)
    rw [this]
    group
  obtain ⟨h₁, hh₁, hrel⟩ := hb.w₁_a
  have hw12 : ∀ q ∈ Q₁, D.w₁ * q * D.w₁⁻¹ ∈ Q₂ := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := hQ₁repr q hq
    rw [hmem₂]
    have e0 : D.w₁ * (D.a * x * D.a⁻¹) * D.w₁⁻¹ =
        (D.w₁ * D.a * D.w₁⁻¹) * (D.w₁ * x * D.w₁⁻¹) * (D.w₁ * D.a * D.w₁⁻¹)⁻¹ := by group
    have e : D.a * (D.w₁ * (D.a * x * D.a⁻¹) * D.w₁⁻¹) * D.a⁻¹ = h₁ * x * h₁⁻¹ := by
      rw [e0, hrel, hw₁x x hx]
      group
    rw [e]
    exact hX₂ h₁ hh₁ x hx
  have hw21 : ∀ q ∈ Q₂, D.w₁ * q * D.w₁⁻¹ ∈ Q₁ := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := hQ₂repr q hq
    rw [hmem₁]
    have e0 : D.w₁ * (D.a ^ 2 * x * (D.a ^ 2)⁻¹) * D.w₁⁻¹ =
        (D.w₁ * D.a * D.w₁⁻¹) ^ 2 * (D.w₁ * x * D.w₁⁻¹) * ((D.w₁ * D.a * D.w₁⁻¹) ^ 2)⁻¹ := by
      simp only [pow_two]; group
    have hh'' : D.a * h₁ * D.a⁻¹ * h₁ ∈ D.H :=
      D.H.mul_mem ((Subgroup.mem_normalizer_iff.1 ha h₁).1 hh₁) hh₁
    have e : D.a ^ 2 * (D.w₁ * (D.a ^ 2 * x * (D.a ^ 2)⁻¹) * D.w₁⁻¹) * (D.a ^ 2)⁻¹ =
        (D.a * h₁ * D.a⁻¹ * h₁) * x * (D.a * h₁ * D.a⁻¹ * h₁)⁻¹ := by
      rw [e0, hrel, hw₁x x hx]
      simp only [pow_two]; group
    rw [e]
    exact hX₂ _ hh'' x hx
  by_cases hα : α = false
  · have hA : D.A α = D.X₁ := by rw [hα]; exact Ch6Notation.A_false
    refine hS.false_of_Q hb hQ₁R hQ₁H hQ₁ne hzQ₁ hQ₁c ?_ ?_
    · intro x hx q hq
      have h1 := hcent₁ q hq x (by rw [hA]; exact hx)
      calc x * q * x⁻¹ = (x * q) * x⁻¹ := rfl
        _ = (q * x) * x⁻¹ := by rw [h1]
        _ = q := by group
    · intro q hq q' hq'
      exact hcomm12 q hq _ (hw12 q' hq')
  · have hα' : α = true := by simpa using hα
    have hγ : γ = false := by
      cases γ
      · rfl
      · exact absurd (hα'.trans rfl) hαγ
    have hA : D.A γ = D.X₁ := by rw [hγ]; exact Ch6Notation.A_false
    refine hS.false_of_Q hb hQ₂R hQ₂H hQ₂ne hzQ₂ hQ₂c ?_ ?_
    · intro x hx q hq
      have h1 := hcent₂ q hq x (by rw [hA]; exact hx)
      calc x * q * x⁻¹ = (x * q) * x⁻¹ := rfl
        _ = (q * x) * x⁻¹ := by rw [h1]
        _ = q := by group
    · intro q hq q' hq'
      exact (hcomm12 _ (hw21 q' hq') q hq).symm

end CFSG.GH74.GLS.Stage4.Rest
