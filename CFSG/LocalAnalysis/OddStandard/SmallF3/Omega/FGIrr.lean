module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGFixZero
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGSmallRep

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {B : LinearMap.BilinForm (ZMod 3) V} {ρ : V →ₗ[ZMod 3] V} {lam : ZMod 3}

theorem fg_irreducible (hB : B.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hρ : FGCplx B ρ lam) {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hH : FGCplxGroup B ρ H)
    [IsSimpleGroup ↥H] (hcard : ¬ Nat.card ↥H ∣ 11232) (W : Submodule (ZMod 3) V)
    (hW : ∀ g ∈ H, ∀ w ∈ W, g w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hne : ∃ g ∈ H, g ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥H)
    exact ⟨g, g.2, fun h => hg (Subtype.ext h)⟩
  have hsmall : ∀ U : Submodule (ZMod 3) V, (∀ g ∈ H, ∀ u ∈ U, g u ∈ U) →
      Module.finrank (ZMod 3) U ≤ 3 → U = ⊥ := by
    intro U hU hd
    rw [eq_bot_iff]
    intro u hu
    have h1 := fg_pointwise_of_finrank_le H hcard U hU hd
    have h0 := fg_fixed_eq_bot hB hdim hρ hH hne (y := u) (fun g hg => h1 g hg u hu)
    rw [h0]
    exact Submodule.zero_mem _
  by_cases h3 : Module.finrank (ZMod 3) W ≤ 3
  · exact Or.inl (hsmall W hW h3)
  · right
    have hWperp : ∀ g ∈ H, ∀ x ∈ B.orthogonal W, g x ∈ B.orthogonal W := by
      intro g hg x hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
      intro w hw
      have hgi : g⁻¹ ∈ H := H.inv_mem hg
      have h1 : B (g (g⁻¹ w)) (g x) = B (g⁻¹ w) x := hH.isom g hg _ _
      have h2 : g (g⁻¹ w) = w := g.apply_symm_apply w
      rw [h2] at h1
      rw [h1]
      exact hx _ (hW g⁻¹ hgi w hw)
    have hdperp : Module.finrank (ZMod 3) (B.orthogonal W) ≤ 3 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hB W, hdim]
      omega
    have hperp0 : B.orthogonal W = ⊥ := hsmall _ hWperp hdperp
    have h6 : Module.finrank (ZMod 3) W = 6 := by
      have h := LinearMap.BilinForm.finrank_orthogonal hB W
      have hle := Submodule.finrank_le W
      rw [hperp0, finrank_bot, hdim] at h
      rw [hdim] at hle
      omega
    exact Submodule.eq_top_of_finrank_eq (by rw [h6, hdim])

end CFSG.OddStandard.SmallF3.Omega
