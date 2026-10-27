module

public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem alphaOf_eq_bot_of_generation (H : Subgroup G) [H.Normal]
    (hO : classicalInvolutionOddCore G = ⊥) {A : Subgroup G} (hAH : A ≤ H)
    (hA2 : ∀ x ∈ A, x * x = 1) (hA1 : ∃ a ∈ A, a ≠ 1)
    (hN : ∀ a ∈ A, a ≠ 1 → oddCoreOf (Subgroup.centralizer ({a} : Set G)) ⊓ H = ⊥)
    (hgen : H ≤ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set G) ⊓ H) :
    alphaOf A = ⊥ := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h := hA2 (x * y) (A.mul_mem hx hy)
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hA2 x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hA2 y hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hxi, hyi]
  have hNC : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ oddCoreOf (Subgroup.centralizer ({a} : Set G)),
      ∀ h ∈ Subgroup.centralizer ({a} : Set G) ⊓ H, n * h = h * n := by
    intro a ha ha1 n hn h hh
    have hn' : n ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := hn
    have h1 : h * n⁻¹ * h⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) :=
      conj_mem_oddCoreIn hh.1 ((oddCoreIn _).inv_mem hn')
    have h2 : n * h * n⁻¹ * h⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({a} : Set G)) := by
      have : n * h * n⁻¹ * h⁻¹ = n * (h * n⁻¹ * h⁻¹) := by group
      rw [this]
      exact (oddCoreIn _).mul_mem hn' h1
    have h3 : n * h * n⁻¹ * h⁻¹ ∈ H :=
      H.mul_mem (Subgroup.Normal.conj_mem inferInstance h hh.2 n) (H.inv_mem hh.2)
    have h4 : n * h * n⁻¹ * h⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({a} : Set G)) ⊓ H := ⟨h2, h3⟩
    rw [hN a ha ha1, Subgroup.mem_bot] at h4
    calc n * h = (n * h * n⁻¹ * h⁻¹) * (h * n) := by group
      _ = h * n := by rw [h4, one_mul]
  have hcomm : (⨆ a ∈ A, ⨆ (_ : a ≠ 1),
      ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) = ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
    refine (Subgroup.commutator_le.2 fun n hn x hx => ?_)
    have hxC : x ∈ Subgroup.centralizer ({a} : Set G) ⊓ H :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hAc a ha x hx).symm, hAH hx⟩
    rw [Subgroup.mem_bot, commutatorElement_def]
    have := hNC a ha ha1 n hn x hxC
    calc n * x * n⁻¹ * x⁻¹ = (x * n) * n⁻¹ * x⁻¹ := by rw [this]
      _ = 1 := by group
  set M : Subgroup G := ⨅ a ∈ A, ⨅ (_ : a ≠ 1), oddCoreOf (Subgroup.centralizer ({a} : Set G))
    with hM
  have hMN : ∀ a ∈ A, a ≠ 1 → ∀ m ∈ M, m ∈ oddCoreOf (Subgroup.centralizer ({a} : Set G)) := by
    intro a ha ha1 m hm
    simp only [hM, Subgroup.mem_iInf] at hm
    exact hm a ha ha1
  have hMZ : M ≤ Subgroup.centralizer (H : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ ⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set G) ⊓ H := hgen hh
    have hle : (⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set G) ⊓ H) ≤
        Subgroup.centralizer (M : Set G) := by
      refine iSup₂_le fun a ha => iSup_le fun ha1 => fun u hu => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro m' hm'
      exact (hNC a ha ha1 m' (hMN a ha ha1 m' hm') u hu)
    exact (Subgroup.mem_centralizer_iff.mp (hle hh') m hm).symm
  obtain ⟨a₀, ha₀, ha₀1⟩ := hA1
  have hModd : Odd (Nat.card M) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn (Subgroup.centralizer ({a₀} : Set G)))
      (Subgroup.card_dvd_of_le ((iInf₂_le a₀ ha₀).trans (iInf_le _ ha₀1)))
  have hZn : (Subgroup.centralizer (H : Set G)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro h hh
    have hh' : g⁻¹ * h * g ∈ H := by
      simpa using Subgroup.Normal.conj_mem inferInstance h hh g⁻¹
    have := hn _ hh'
    calc h * (g * n * g⁻¹) = g * ((g⁻¹ * h * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * h * g)) * g⁻¹ := by rw [this]
      _ = (g * n * g⁻¹) * h := by group
  have hMn : Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer (M : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g' ∈ Subgroup.centralizer (H : Set G), ∀ m ∈ M, g' * m * g'⁻¹ ∈ M := by
      intro g' hg' m hm
      simp only [hM, Subgroup.mem_iInf]
      intro a ha ha1
      have hgC : g' ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hg' a (hAH ha)).symm
      exact conj_mem_oddCoreIn hgC (hMN a ha ha1 m hm)
    intro m
    refine ⟨fun hm => key g hg m hm, fun hm => ?_⟩
    have := key g⁻¹ ((Subgroup.centralizer (H : Set G)).inv_mem hg) _ hm
    simpa [mul_assoc] using this
  have hMo : M ≤ oddCoreIn (Subgroup.centralizer (H : Set G)) :=
    le_oddCoreIn_of_normalizes hMZ hMn hModd
  have hZ : classicalInvolutionOddCore (Subgroup.centralizer (H : Set G)) = ⊥ :=
    oddCore_normal_eq_bot _ hO
  have hMbot : M = ⊥ := by
    refine le_bot_iff.mp (hMo.trans ?_)
    show (classicalInvolutionOddCore (Subgroup.centralizer (H : Set G))).map
      (Subgroup.centralizer (H : Set G)).subtype ≤ ⊥
    rw [hZ, Subgroup.map_bot]
  unfold alphaOf
  rw [hcomm, bot_sup_eq]
  exact hMbot

end CFSG.ClassicalInvolution.Uniform
