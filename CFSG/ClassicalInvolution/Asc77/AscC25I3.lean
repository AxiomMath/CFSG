module

public import CFSG.ClassicalInvolution.Asc77.AscC25I2
public import CFSG.ClassicalInvolution.Asc77.AscC25H4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25I

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' t₀ : G}


theorem exists_conj_azt' (h11 : C25_11 p f) (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hsw : IsSwap K K' z t₀) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    {a n : G} (ha2 : a * a = 1) (haz : a * z = z * a) (hat : a * t₀ = t₀ * a)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hnK : n ∈ Subgroup.normalizer (K : Set G))
    (hnz : n * z = z * n) (hn'K : t₀ * n * t₀ ∈ Subgroup.normalizer (K : Set G))
    (hδa : diagGamma (nuG hp hq e a) = 1)
    (hδ : diagGamma (nuG hp hq e n) = diagGamma (nuG hp hq e (t₀ * n * t₀)))
    (hχ : SemidirectProduct.rightHom (nuG hp hq e n) =
      SemidirectProduct.rightHom (nuG hp hq e (t₀ * n * t₀)) *
        SemidirectProduct.rightHom (nuG hp hq e a))
    (hg : ∃ g : G, g * z * g⁻¹ = t₀) :
    (∃ g : G, g * z * g⁻¹ = a * z * t₀) ∨ (∃ g : G, g * z * g⁻¹ = a * t₀) := by
  have hsq : z * z = 1 := h.hz.sq
  have htz : t₀ * z = z * t₀ := hsw.comm
  obtain ⟨c, m₁, hcz, hm₁, hmt, hcm⟩ :=
    exists_triv_conj' h hsw hp hq e ha2 haz hat haK hnK hnz hn'K hδa hδ hχ
  have h2 : ∀ (i : ℕ) (y : G), y ∈ Subgroup.zpowers m₁ → orderOf y = 2 ^ i → y = 1 ∨ y = z :=
    fun i y hy hord => eq_one_or_eq_z_of_triv h11 h hp hq e
      (triv_of_triv_swap h hsw hp hq e ((Subgroup.zpowers_le.mpr hm₁) hy)) hord
  obtain ⟨g, ε, hgm, hε, hconj⟩ := exists_conj_mul_of_inverted hsw.sq hsq hmt h2
  have hgz : g * z = z * g := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgm
    exact (Commute.zpow_left (show Commute m₁ z from hm₁.2.1) j).eq
  obtain ⟨g₁, hg₁⟩ := hg
  have hb : a * z * t₀ = (c⁻¹ * g) * (t₀ * z ^ ε) * (c⁻¹ * g)⁻¹ := by
    calc a * z * t₀ = c⁻¹ * (c * (a * z * t₀) * c⁻¹) * c := by group
      _ = c⁻¹ * (t₀ * m₁) * c := by rw [hcm]
      _ = c⁻¹ * (g * (t₀ * z ^ ε) * g⁻¹) * c := by rw [hconj]
      _ = (c⁻¹ * g) * (t₀ * z ^ ε) * (c⁻¹ * g)⁻¹ := by group
  have hhz' : (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ = z := by
    have hc' : Commute c z := hcz
    have hg' : Commute g z := hgz
    have : Commute (c⁻¹ * g) z := hc'.inv_left.mul_left hg'
    calc (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ = (c⁻¹ * g) * z * (c⁻¹ * g)⁻¹ := rfl
      _ = z * (c⁻¹ * g) * (c⁻¹ * g)⁻¹ := by rw [this.eq]
      _ = z := by group
  interval_cases ε
  · left
    refine ⟨(c⁻¹ * g) * g₁, ?_⟩
    calc (c⁻¹ * g) * g₁ * z * ((c⁻¹ * g) * g₁)⁻¹ =
        (c⁻¹ * g) * (g₁ * z * g₁⁻¹) * (c⁻¹ * g)⁻¹ := by group
      _ = (c⁻¹ * g) * t₀ * (c⁻¹ * g)⁻¹ := by rw [hg₁]
      _ = a * z * t₀ := by rw [hb, pow_zero, mul_one]
  · right
    rw [pow_one] at hb
    have e1 : a * t₀ = (a * z * t₀) * z := by
      calc a * t₀ = a * (z * z) * t₀ := by rw [hsq, mul_one]
        _ = a * z * (z * t₀) := by group
        _ = a * z * (t₀ * z) := by rw [htz]
        _ = (a * z * t₀) * z := by group
    refine ⟨(c⁻¹ * g) * g₁, ?_⟩
    calc (c⁻¹ * g) * g₁ * z * ((c⁻¹ * g) * g₁)⁻¹ =
        (c⁻¹ * g) * (g₁ * z * g₁⁻¹) * (c⁻¹ * g)⁻¹ := by group
      _ = (c⁻¹ * g) * t₀ * (c⁻¹ * g)⁻¹ := by rw [hg₁]
      _ = ((c⁻¹ * g) * t₀ * (c⁻¹ * g)⁻¹ * ((c⁻¹ * g) * z * (c⁻¹ * g)⁻¹)) * z := by
          rw [hhz', mul_assoc _ z z, hsq, mul_one]
      _ = ((c⁻¹ * g) * (t₀ * z) * (c⁻¹ * g)⁻¹) * z := by group
      _ = (a * z * t₀) * z := by rw [← hb]
      _ = a * t₀ := e1.symm


end Main

end CFSG.ClassicalInvolution.Asc77.C25I
