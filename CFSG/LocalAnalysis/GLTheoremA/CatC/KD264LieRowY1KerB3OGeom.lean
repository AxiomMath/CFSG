module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerB3OCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerB3OPSL
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MGeom

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KB3O

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3 CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4
  QuadraticMap Module TauCeti.QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.Open

noncomputable section
open Classical

section Geom7

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem geometry7 (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {Q : QuadraticForm K V}
    (hdim : finrank K V = 7) (hnd : (polarBilin Q).Nondegenerate)
    (P : Subgroup (V ≃ₗ[K] V)) (hPO : P ≤ orthogonalGroup Q) (hP : Nat.card P = 27)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ F : Subgroup (V ≃ₗ[K] V), F ≤ P ∧ Nat.card F = 9 ∧
      ∃ Hv : Subgroup (V ≃ₗ[K] V), Hv ≤ ⁅orthogonalGroup Q, orthogonalGroup Q⁆ ∧
        (∀ h ∈ Hv, ∀ f ∈ F, h * f = f * h) ∧
        (∀ g ∈ orthogonalGroup Q, (∀ f ∈ F, g * f = f * g) → ∀ h ∈ Hv, g * h * g⁻¹ ∈ Hv) ∧
        CFSG.Open.IsQuasisimple Hv ∧ 3 ∣ Nat.card (Hv ⧸ Subgroup.center Hv) ∧
        (∃ w : V, w ≠ 0 ∧ ∀ h ∈ Hv, h w = w) := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  haveI : Fintype P := Fintype.ofFinite P
  let ρ : P →* Module.End K V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp P.subtype
  have hρ : ∀ (g : P) (v : V), ρ g v = (g : V ≃ₗ[K] V) v := fun g v => rfl
  have hs : Setting ρ Q :=
    { h3 := h3
      hΓ := hP
      hexp := fun g => Subtype.ext (hexp g.1 g.2)
      hcomm := fun g h => Subtype.ext (hcomm g.1 g.2 h.1 h.2)
      hnd := hnd
      hQ := fun g v => by
        rw [hρ]
        exact map_app_of_mem_orthogonalGroup (hPO g.2) v }
  have hfaith : ∀ g : P, (∀ v : V, ρ g v = v) → g = 1 := by
    intro g hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact hg v
  obtain ⟨F₀, hF₀, hd3, hUnd⟩ := core7 hs hdim hfaith
  set U : Submodule K V := LinearMap.range (av ρ F₀) with hUdef
  have hFcard : Nat.card F₀ = 9 := card_of_index_eq_three hP ((mem_idx3 F₀).1 hF₀)
  have hfix : ∀ f ∈ F₀, ∀ u ∈ U, ρ f u = u := by
    rintro f hf _ ⟨y, rfl⟩
    have := congrArg (fun m : Module.End K V => m y) (left_mul_av (ρ := ρ) hf)
    simpa [Module.End.mul_apply] using this
  have hAav : OIdem Q (av ρ F₀) := by
    refine ⟨av_mul_self ρ (natCard_ne_zero' h3 hP F₀), fun u v => ?_⟩
    have := bilin_av ρ (polarBilin Q) (fun g u w => by
      simp only [QuadraticMap.polarBilin_apply_apply]; exact hs.hB g u w) F₀ u v
    simpa only [QuadraticMap.polarBilin_apply_apply] using this
  have hU : IsCompl U (perpOf Q U) := isCompl_perpOf_range hnd hAav
  have hperp : ∃ w ∈ perpOf Q U, w ≠ 0 := by
    have h1 : finrank K (perpOf Q U) = finrank K V - finrank K U :=
      LinearMap.BilinForm.finrank_orthogonal hnd U
    have hne : perpOf Q U ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot, hd3, hdim] at h1
      omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hUdim : finrank K U = 3 := hd3
  have hUnd' : (polarBilin (Q.restrict U)).Nondegenerate := nondeg_comp_subtype' hUnd
  obtain ⟨N, hNO, hnorm, hsN, hpN, hnaN, h3N⟩ :=
    three_component h2 h3 (Q.restrict U) hUnd' hUdim
  obtain ⟨Hv, hHvle, hHvcomm, hHvnorm, hHvq, hHv3, hHvw⟩ :=
    exists_component hU hperp hNO hnorm hsN hpN hnaN h3N
  refine ⟨F₀.map P.subtype, ?_, ?_, Hv, hHvle, ?_, ?_, hHvq, hHv3, hHvw⟩
  · rintro _ ⟨f, _, rfl⟩
    exact f.2
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hFcard]
  · rintro h hh _ ⟨f, hf, rfl⟩
    exact hHvcomm h hh f (hPO f.2) (fun u hu => hfix f hf u hu)
  · intro g hg hgF h hh
    have hY : ∀ f ∈ F₀, (LinearEquiv.automorphismGroup.toLinearMapMonoidHom g) * ρ f =
        ρ f * (LinearEquiv.automorphismGroup.toLinearMapMonoidHom g) := by
      intro f hf
      have := hgF (f : V ≃ₗ[K] V) ⟨f, hf, rfl⟩
      show LinearEquiv.automorphismGroup.toLinearMapMonoidHom g *
        LinearEquiv.automorphismGroup.toLinearMapMonoidHom (f : V ≃ₗ[K] V) = _
      rw [← map_mul, this, map_mul]
      rfl
    have hY' : ∀ f ∈ F₀, (LinearEquiv.automorphismGroup.toLinearMapMonoidHom g⁻¹) * ρ f =
        ρ f * (LinearEquiv.automorphismGroup.toLinearMapMonoidHom g⁻¹) := by
      intro f hf
      have h1 := hgF (f : V ≃ₗ[K] V) ⟨f, hf, rfl⟩
      have h2' : g⁻¹ * (f : V ≃ₗ[K] V) = (f : V ≃ₗ[K] V) * g⁻¹ := by
        calc g⁻¹ * (f : V ≃ₗ[K] V) = g⁻¹ * ((f : V ≃ₗ[K] V) * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * (f : V ≃ₗ[K] V)) * g⁻¹ := by rw [h1]
          _ = (f : V ≃ₗ[K] V) * g⁻¹ := by group
      show LinearEquiv.automorphismGroup.toLinearMapMonoidHom g⁻¹ *
        LinearEquiv.automorphismGroup.toLinearMapMonoidHom (f : V ≃ₗ[K] V) = _
      rw [← map_mul, h2', map_mul]
      rfl
    have hgU : ∀ u ∈ U, g u ∈ U := by
      rintro _ ⟨y, rfl⟩
      have := congrArg (fun m : Module.End K V => m y) (commute_av_of F₀ _ hY)
      simp only [Module.End.mul_apply] at this
      exact ⟨_, this.symm⟩
    have hgU' : ∀ u ∈ U, g⁻¹ u ∈ U := by
      rintro _ ⟨y, rfl⟩
      have := congrArg (fun m : Module.End K V => m y) (commute_av_of F₀ _ hY')
      simp only [Module.End.mul_apply] at this
      exact ⟨_, this.symm⟩
    exact hHvnorm g hg hgU hgU' h hh

end Geom7

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KB3O

end
