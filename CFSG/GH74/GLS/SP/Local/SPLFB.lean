module

public import CFSG.GH74.GLS.SP.Local.SPLWt3

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem cenP_H_eq_bot (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (h42 : D.L42) : centralizer (D.H : Set G) ⊓ D.P = ⊥ := by
  have hHab := H_comm D hs h1
  have hnorm : Normalizes D.H (centralizer (D.H : Set G) ⊓ D.P) := by
    intro g hg x hx
    have hgx : g * x * g⁻¹ = x := by
      have := mem_centralizer_iff.mp hx.1 g hg
      rw [this]
      group
    rw [hgx]
    exact hx
  have hnone : ∀ i : ℤ, ¬ ((1 ≤ i ∧ i ≤ 4) ∧ D.root i ≤ centralizer (D.H : Set G) ⊓ D.P) := by
    rintro i ⟨⟨hi1, hi4⟩, hle⟩
    have hker : ∀ g ∈ D.H, ∀ x ∈ D.root i, g * x = x * g := fun g hg x hx =>
      mem_centralizer_iff.mp (hle hx).1 g hg
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi' with rfl | rfl | rfl | rfl
    · rw [root_p1] at hker
      exact z_not_mem_ker₄ D hs h1 h3 (mem_kernelOf_iff.mpr ⟨z_mem_H D h1, hker _ (z_mem_H D h1)⟩)
    · rw [root_p2] at hker
      exact h₂_not_mem_ker₂ D hs h1 h3
        (mem_kernelOf_iff.mpr ⟨H₂_le_H D (mem_zpowers _), hker _ (H₂_le_H D (mem_zpowers _))⟩)
    · rw [root_p3] at hker
      exact z_not_mem_ker₃ D hs h3 (mem_kernelOf_iff.mpr ⟨z_mem_H D h1, hker _ (z_mem_H D h1)⟩)
    · rw [root_p4] at hker
      exact h₁_not_mem_ker₁ D hs h1 h3
        (mem_kernelOf_iff.mpr ⟨H₁_le_H D (mem_zpowers _), hker _ (H₁_le_H D (mem_zpowers _))⟩)
  have := (h42 (centralizer (D.H : Set G) ⊓ D.P) inf_le_right hnorm [] (Or.inl List.Pairwise.nil)
    (fun i => by simpa using hnone i)).1
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ ((centralizer (D.H : Set G) ⊓ D.P : Subgroup G) : Set G) := hx
  rw [this] at hx'
  simp only [chainProd, List.map_nil, List.prod_nil, Set.mem_one] at hx'
  rw [hx']
  exact Subgroup.one_mem _

theorem H_inf_P_eq_bot (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    D.H ⊓ D.P = ⊥ := by
  have : Fact D.p.Prime := ⟨hs.prime⟩
  rw [eq_bot_iff]
  rintro x ⟨hxH, hxP⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 h3.P_pGroup ⟨x, hxP⟩
  have h2 : orderOf x = D.p ^ k := by simpa using hk
  have h4 : orderOf x ∣ D.p ^ k := h2 ▸ dvd_refl _
  obtain ⟨a, -, hord⟩ := (Nat.dvd_prime_pow hs.prime).1 h4
  by_cases ha0 : a = 0
  · rw [ha0, pow_zero] at hord
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.1 hord)
  · exact absurd (hord ▸ dvd_pow_self D.p ha0) (H_pPrime D hs h1 x hxH)

theorem F_inf_B (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (h42 : D.L42) : D.F ⊓ (D.H ⊔ D.P) = ⊥ := by
  have hHab := H_comm D hs h1
  have hHP : D.H ≤ normalizer (D.P : Set G) := by
    have hP : Normalizes D.H D.P := by
      show Normalizes D.H (D.X₁ ⊔ (D.X₂ ⊔ D.X₃ ⊔ D.X₄))
      exact normalizes_sup h3.H_X₁
        (normalizes_sup (normalizes_sup (H_X₂ D hs h1 h3.toSPL3X) h3.H_X₃)
          (H_X₄ D hs h1 h3))
    exact le_normalizer_of_normalizes hP
  rw [eq_bot_iff]
  rintro f ⟨hfF, hfB⟩
  have hmul : f ∈ (D.H : Set G) * (D.P : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right D.H D.P hHP]
    exact hfB
  obtain ⟨h, hh, p, hp, rfl⟩ := hmul
  have hFP := F_normalizes_P D hs h3
  have hpc : ∀ h' ∈ D.H, p * h' = h' * p := by
    intro h' hh'
    have hfH : h * p * h' * (h * p)⁻¹ ∈ D.H := h1.F_norm_H _ hfF _ hh'
    have h2 : p * h' * p⁻¹ ∈ D.H := by
      have e : p * h' * p⁻¹ = h⁻¹ * (h * p * h' * (h * p)⁻¹) * h := by group
      rw [e]
      exact D.H.mul_mem (D.H.mul_mem (D.H.inv_mem hh) hfH) hh
    have h3' : p * h' * p⁻¹ * h'⁻¹ ∈ D.H := D.H.mul_mem h2 (D.H.inv_mem hh')
    have h4 : p * h' * p⁻¹ * h'⁻¹ ∈ D.P := by
      have hh'P : h' * p⁻¹ * h'⁻¹ ∈ D.P :=
        (mem_normalizer_iff.mp (hHP hh') p⁻¹).mp (D.P.inv_mem hp) |> fun x => by
          simpa [mul_assoc] using x
      have e : p * h' * p⁻¹ * h'⁻¹ = p * (h' * p⁻¹ * h'⁻¹) := by group
      rw [e]
      exact D.P.mul_mem hp hh'P
    have h5 : p * h' * p⁻¹ * h'⁻¹ ∈ D.H ⊓ D.P := ⟨h3', h4⟩
    rw [H_inf_P_eq_bot D hs h1 h3] at h5
    have h6 : p * h' * p⁻¹ * h'⁻¹ = 1 := Subgroup.mem_bot.mp h5
    calc p * h' = (p * h' * p⁻¹ * h'⁻¹) * (h' * p) := by group
      _ = h' * p := by rw [h6, one_mul]
  have hpZ : p ∈ centralizer (D.H : Set G) ⊓ D.P :=
    ⟨mem_centralizer_iff.mpr fun h' hh' => (hpc h' hh').symm, hp⟩
  rw [cenP_H_eq_bot D hs h1 h3 h42] at hpZ
  have hp1 : p = 1 := Subgroup.mem_bot.mp hpZ
  subst hp1
  have hK : h ∈ D.K := by
    have : D.H ≤ D.K₁ ⊔ D.K₂ :=
      sup_le (le_trans (H₁_le_K₁ D h1) le_sup_left) (le_trans (H₂_le_K₂ D hs h1) le_sup_right)
    exact this hh
  have hFh : h ∈ D.F := by simpa using hfF
  have : h ∈ D.F ⊓ D.K := ⟨hFh, hK⟩
  rw [F_inf_K_eq hs] at this
  have h1' : h = 1 := Subgroup.mem_bot.mp this
  simp [h1']

end CFSG.GH74.GLS.SP.Local
