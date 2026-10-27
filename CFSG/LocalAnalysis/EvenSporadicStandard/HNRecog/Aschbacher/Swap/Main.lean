module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Inner
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Free

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private lemma exists_mul_of_swap {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} {b : V ≃ₗ[ZMod 2] V}
    (hsw : SwapsFactors σ b) (g : A5 × A5) :
    ∃ g' : A5 × A5, b * σ g = σ g' * b := by
  classical
  choose y hy using hsw.1
  choose x hx using hsw.2
  refine ⟨(x g.2, y g.1), ?_⟩
  have hg : σ g = σ (g.1, 1) * σ (1, g.2) := by
    rw [← map_mul]
    congr 1
  have hconj : b * σ g * b⁻¹ = σ (x g.2, y g.1) := by
    rw [hg]
    calc b * (σ (g.1, 1) * σ (1, g.2)) * b⁻¹
        = (b * σ (g.1, 1) * b⁻¹) * (b * σ (1, g.2) * b⁻¹) := by group
      _ = σ (1, y g.1) * σ (x g.2, 1) := by rw [hy g.1, hx g.2]
      _ = σ (x g.2, y g.1) := by
          rw [← map_mul]
          congr 1
  calc b * σ g = b * σ g * b⁻¹ * b := by group
    _ = σ (x g.2, y g.1) * b := by rw [hconj]

private lemma isometry_conj {B : LinearMap.BilinForm (ZMod 2) V}
    {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} {b : V ≃ₗ[ZMod 2] V}
    (hBσ : ∀ g x y, B (σ g x) (σ g y) = B x y)
    (hbB : ∀ x y, B (b x) (b y) = B x y) (h : A5 × A5) :
    ∀ x y, B ((σ h * b * (σ h)⁻¹) x) ((σ h * b * (σ h)⁻¹) y) = B x y := by
  intro x y
  simp only [LinearEquiv.mul_apply]
  rw [hBσ h, hbB]
  rw [← map_inv σ h]
  exact hBσ h⁻¹ x y

theorem exists_mul_of_swap_free (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hS : StdHyp σ)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hBσ : ∀ g x y, B (σ g x) (σ g y) = B x y)
    {b b' : V ≃ₗ[ZMod 2] V} (hb : b * b = 1) (hb' : b' * b' = 1)
    (hBb : ∀ x y, B (b x) (b y) = B x y) (hBb' : ∀ x y, B (b' x) (b' y) = B x y)
    (hsw : SwapsFactors σ b) (hsw' : SwapsFactors σ b')
    (hfree : 4 ≤ finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1)))
    (hfree' : 4 ≤ finrank (ZMod 2) (LinearMap.range ((b' : V →ₗ[ZMod 2] V) + 1))) :
    ∃ g : A5 × A5, b = σ g * b' := by
  classical
  obtain ⟨c, Fp, Fm, hE⟩ := exists_eigenData σ hS
  obtain ⟨z, k, hk, hkα⟩ := exists_conj_normalized hS.inj hb hsw
  obtain ⟨z', k', hk', hk'α⟩ := exists_conj_normalized hS.inj hb' hsw'
  have hk₀ex : ∃ k₀ : ℕ, (k * k₀) % 5 = 1 := by
    rcases hk with rfl | rfl
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
  obtain ⟨k₀, hkk₀⟩ := hk₀ex
  have hk'₀ex : ∃ k₀' : ℕ, (k' * k₀') % 5 = 1 := by
    rcases hk' with rfl | rfl
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
  obtain ⟨k₀', hk'k₀'⟩ := hk'₀ex
  set g₁ : V ≃ₗ[ZMod 2] V := σ (1, z⁻¹) with hg₁
  set b₁ : V ≃ₗ[ZMod 2] V := g₁ * b * g₁⁻¹ with hb₁def
  set g₂ : V ≃ₗ[ZMod 2] V := σ (1, z'⁻¹) with hg₂
  set b₂ : V ≃ₗ[ZMod 2] V := g₂ * b' * g₂⁻¹ with hb₂def
  have hα₁ : b₁ * σ (a₀, 1) * b₁⁻¹ = σ (1, a₀ ^ k) := by
    rw [hb₁def, hg₁]
    exact hkα
  have hα₂' : b₂ * σ (a₀, 1) * b₂⁻¹ = σ (1, a₀ ^ k') := by
    rw [hb₂def, hg₂]
    exact hk'α
  have hb₁ : b₁ * b₁ = 1 := by
    rw [hb₁def]
    calc (g₁ * b * g₁⁻¹) * (g₁ * b * g₁⁻¹) = g₁ * (b * b) * g₁⁻¹ := by group
      _ = 1 := by rw [hb]; group
  have hb₂ : b₂ * b₂ = 1 := by
    rw [hb₂def]
    calc (g₂ * b' * g₂⁻¹) * (g₂ * b' * g₂⁻¹) = g₂ * (b' * b') * g₂⁻¹ := by group
      _ = 1 := by rw [hb']; group
  have hsw₁ : SwapsFactors σ b₁ := by
    rw [hb₁def, hg₁]
    exact hsw.conj (1, z⁻¹)
  have hsw₂ : SwapsFactors σ b₂ := by
    rw [hb₂def, hg₂]
    exact hsw'.conj (1, z'⁻¹)
  have hBb₁ : ∀ x y, B (b₁ x) (b₁ y) = B x y := by
    rw [hb₁def, hg₁]
    exact isometry_conj hBσ hBb (1, z⁻¹)
  have hBb₂ : ∀ x y, B (b₂ x) (b₂ y) = B x y := by
    rw [hb₂def, hg₂]
    exact isometry_conj hBσ hBb' (1, z'⁻¹)
  have hfree₁ : 4 ≤ finrank (ZMod 2) (LinearMap.range ((b₁ : V →ₗ[ZMod 2] V) + 1)) := by
    rw [hb₁def]
    rw [finrank_range_conj g₁ b]
    exact hfree
  have hfree₂ : 4 ≤ finrank (ZMod 2) (LinearMap.range ((b₂ : V →ₗ[ZMod 2] V) + 1)) := by
    rw [hb₂def]
    rw [finrank_range_conj g₂ b']
    exact hfree'
  have hkc₁ : (k * c) % 5 = 2 ∨ (k * c) % 5 = 3 :=
    EigenData.mul_mod_five_of_free hS hE b₁ hb₁ hkk₀ hα₁ hfree₁
  have hkc₂ : (k' * c) % 5 = 2 ∨ (k' * c) % 5 = 3 :=
    EigenData.mul_mod_five_of_free hS hE b₂ hb₂ hk'k₀' hα₂' hfree₂
  have hc1 : 1 ≤ c := hE.one_le
  have hc4 : c ≤ 4 := hE.le_four
  have hk_eq : k = k' := by
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> omega
  have hα₂ : b₂ * σ (a₀, 1) * b₂⁻¹ = σ (1, a₀ ^ k) := by
    simpa [← hk_eq] using hα₂'
  have hb₁α : b₁ * σ (a₀, 1) = σ (1, a₀ ^ k) * b₁ := by
    calc b₁ * σ (a₀, 1) = b₁ * σ (a₀, 1) * b₁⁻¹ * b₁ := by group
      _ = σ (1, a₀ ^ k) * b₁ := by rw [hα₁]
  have hb₂α : b₂ * σ (a₀, 1) = σ (1, a₀ ^ k) * b₂ := by
    calc b₂ * σ (a₀, 1) = b₂ * σ (a₀, 1) * b₂⁻¹ * b₂ := by group
      _ = σ (1, a₀ ^ k) * b₂ := by rw [hα₂]
  have hb₂σ : b₂ * σ (1, a₀ ^ k) = σ (a₀, 1) * b₂ := by
    calc b₂ * σ (1, a₀ ^ k)
        = b₂ * (b₂ * σ (a₀, 1) * b₂⁻¹) := by rw [← hα₂]
      _ = σ (a₀, 1) * b₂ := by
          rw [inv_eq_of_mul_eq_one_right hb₂]
          calc b₂ * (b₂ * σ (a₀, 1) * b₂) = (b₂ * b₂) * σ (a₀, 1) * b₂ := by group
            _ = σ (a₀, 1) * b₂ := by rw [hb₂, one_mul]
  set u : V ≃ₗ[ZMod 2] V := b₂ * b₁ with hu_def
  have hαu : u * σ (a₀, 1) = σ (a₀, 1) * u := by
    rw [hu_def]
    calc b₂ * b₁ * σ (a₀, 1)
        = b₂ * (b₁ * σ (a₀, 1)) := by group
      _ = b₂ * (σ (1, a₀ ^ k) * b₁) := by rw [hb₁α]
      _ = (b₂ * σ (1, a₀ ^ k)) * b₁ := by group
      _ = (σ (a₀, 1) * b₂) * b₁ := by rw [hb₂σ]
      _ = σ (a₀, 1) * (b₂ * b₁) := by group
  have hβ₁ : b₁ * σ (1, a₀) * b₁⁻¹ = σ (a₀ ^ k₀, 1) :=
    conj_beta_of_normalized b₁ hb₁ hkk₀ hα₁
  have hβ₂ : b₂ * σ (1, a₀) * b₂⁻¹ = σ (a₀ ^ k₀, 1) :=
    conj_beta_of_normalized b₂ hb₂ hkk₀ hα₂
  have hb₁β : b₁ * σ (1, a₀) = σ (a₀ ^ k₀, 1) * b₁ := by
    calc b₁ * σ (1, a₀) = b₁ * σ (1, a₀) * b₁⁻¹ * b₁ := by group
      _ = σ (a₀ ^ k₀, 1) * b₁ := by rw [hβ₁]
  have hb₂β' : b₂ * σ (a₀ ^ k₀, 1) = σ (1, a₀) * b₂ := by
    calc b₂ * σ (a₀ ^ k₀, 1)
        = b₂ * (b₂ * σ (1, a₀) * b₂⁻¹) := by rw [← hβ₂]
      _ = σ (1, a₀) * b₂ := by
          rw [inv_eq_of_mul_eq_one_right hb₂]
          calc b₂ * (b₂ * σ (1, a₀) * b₂) = (b₂ * b₂) * σ (1, a₀) * b₂ := by group
            _ = σ (1, a₀) * b₂ := by rw [hb₂, one_mul]
  have hβu : u * σ (1, a₀) = σ (1, a₀) * u := by
    rw [hu_def]
    calc b₂ * b₁ * σ (1, a₀)
        = b₂ * (b₁ * σ (1, a₀)) := by group
      _ = b₂ * (σ (a₀ ^ k₀, 1) * b₁) := by rw [hb₁β]
      _ = (b₂ * σ (a₀ ^ k₀, 1)) * b₁ := by group
      _ = (σ (1, a₀) * b₂) * b₁ := by rw [hb₂β']
      _ = σ (1, a₀) * (b₂ * b₁) := by group
  have hu : PreservesFactors σ u := by
    rw [hu_def]
    exact SwapsFactors.mul hsw₂ hsw₁
  have hBu : ∀ x y, B (u x) (u y) = B x y := by
    rw [hu_def]
    intro x y
    simp only [LinearEquiv.mul_apply]
    rw [hBb₂, hBb₁]
  obtain ⟨g, hg⟩ := exists_eq_of_preservesFactors σ hS B hB hBσ u hu hαu hβu hBu
  have hmul : b₂ * b₁ = σ g := by
    rw [hu_def] at hg
    exact hg
  have hb₁_eq : b₁ = b₂ * σ g := by
    calc b₁ = (b₂ * b₂) * b₁ := by rw [hb₂, one_mul]
      _ = b₂ * (b₂ * b₁) := by group
      _ = b₂ * σ g := by rw [hmul]
  obtain ⟨g', hg'⟩ := exists_mul_of_swap hsw₂ g
  have hb₁_eq' : b₁ = σ g' * b₂ := hb₁_eq.trans hg'
  have hb_decomp : b = g₁⁻¹ * b₁ * g₁ := by
    rw [hb₁def]
    group
  have hb_calc : b = g₁⁻¹ * σ g' * g₂ * (b' * g₂⁻¹ * g₁) := by
    calc b = g₁⁻¹ * b₁ * g₁ := hb_decomp
      _ = g₁⁻¹ * (σ g' * b₂) * g₁ := by rw [hb₁_eq']
      _ = g₁⁻¹ * (σ g' * (g₂ * b' * g₂⁻¹)) * g₁ := by rw [hb₂def]
      _ = g₁⁻¹ * σ g' * g₂ * (b' * g₂⁻¹ * g₁) := by group
  obtain ⟨h₂', hh₂'⟩ := exists_mul_of_swap hsw' ((1, z'⁻¹)⁻¹)
  obtain ⟨h₁', hh₁'⟩ := exists_mul_of_swap hsw' (1, z⁻¹)
  have hg₂inv : g₂⁻¹ = σ ((1, z'⁻¹)⁻¹) := by
    rw [hg₂]
    exact (map_inv σ (1, z'⁻¹)).symm
  have hg₁inv : g₁⁻¹ = σ ((1, z⁻¹)⁻¹) := by
    rw [hg₁]
    exact (map_inv σ (1, z⁻¹)).symm
  have hbg : b' * g₂⁻¹ * g₁ = σ h₂' * σ h₁' * b' := by
    calc b' * g₂⁻¹ * g₁
        = b' * σ ((1, z'⁻¹)⁻¹) * σ (1, z⁻¹) := by rw [hg₂inv, hg₁]
      _ = (σ h₂' * b') * σ (1, z⁻¹) := by rw [hh₂']
      _ = σ h₂' * (b' * σ (1, z⁻¹)) := by group
      _ = σ h₂' * (σ h₁' * b') := by rw [hh₁']
      _ = σ h₂' * σ h₁' * b' := by group
  have hcombine : g₁⁻¹ * σ g' * g₂ * (σ h₂' * σ h₁') =
      σ ((1, z⁻¹)⁻¹ * g' * (1, z'⁻¹) * (h₂' * h₁')) := by
    rw [hg₁inv, hg₂]
    simp only [← map_mul]
  have hfinal : b = σ ((1, z⁻¹)⁻¹ * g' * (1, z'⁻¹) * (h₂' * h₁')) * b' := by
    rw [hb_calc, hbg]
    rw [show g₁⁻¹ * σ g' * g₂ * (σ h₂' * σ h₁' * b') =
        (g₁⁻¹ * σ g' * g₂ * (σ h₂' * σ h₁')) * b' from by group]
    rw [hcombine]
  exact ⟨_, hfinal⟩

end CFSG.EvenSporadicStandard.HNRecog.Swap
