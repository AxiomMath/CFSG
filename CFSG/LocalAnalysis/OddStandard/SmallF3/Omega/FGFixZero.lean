module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCount
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGSigma
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {B : LinearMap.BilinForm (ZMod 3) V} {ρ : V →ₗ[ZMod 3] V} {lam : ZMod 3}

@[expose] def fgFixSp (H : Subgroup (V ≃ₗ[ZMod 3] V)) : Submodule (ZMod 3) V where
  carrier := {y | ∀ g ∈ H, g y = y}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  smul_mem' := fun c {x} hx g hg => by rw [map_smul, hx g hg]

theorem fg_finrank_ne_one_of_rho (hsq : ∀ v, ρ (ρ v) = -v) (Y : Submodule (ZMod 3) V)
    (hY : ∀ y ∈ Y, ρ y ∈ Y) : Module.finrank (ZMod 3) Y ≠ 1 := by
  intro h1
  obtain ⟨y, hy0, hspan⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨c, hc⟩ := hspan ⟨ρ y, hY y y.2⟩
  have hρy : ρ (y : V) = c • (y : V) := (congrArg Subtype.val hc).symm
  have h2 : ρ (ρ (y : V)) = -(y : V) := hsq y
  rw [hρy, map_smul, hρy, smul_smul] at h2
  have h3 : (c * c + 1) • (y : V) = 0 := by rw [add_smul, h2, one_smul, neg_add_cancel]
  have hy0' : (y : V) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have h4 := (smul_eq_zero.mp h3).resolve_right hy0'
  have h5 : ∀ k : ZMod 3, k * k + 1 ≠ 0 := by decide
  exact h5 c h4

theorem fg_fixed_eq_bot (hB : B.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hρ : FGCplx B ρ lam) {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hH : FGCplxGroup B ρ H)
    (hne : ∃ g ∈ H, g ≠ 1) {y : V} (hy : ∀ g ∈ H, g y = y) : y = 0 := by
  let Y : Submodule (ZMod 3) V := fgFixSp H
  have hYρ : ∀ v ∈ Y, ρ v ∈ Y := by
    intro v hv g hg
    rw [hH.comm g hg v, hv g hg]
  have hYσ : ∀ σ : V ≃ₗ[ZMod 3] V, (∀ x y, B (σ x) (σ y) = B x y) →
      (∀ x, σ (ρ x) = ρ (σ x)) → ∀ v ∈ Y, σ v ∈ Y := by
    intro σ hσB hσρ v hv g hg
    have hσinvB : ∀ x y, B (σ⁻¹ x) (σ⁻¹ y) = B x y := by
      intro x y
      have h := hσB (σ⁻¹ x) (σ⁻¹ y)
      have h1 : σ (σ⁻¹ x) = x := σ.apply_symm_apply x
      have h2 : σ (σ⁻¹ y) = y := σ.apply_symm_apply y
      rw [h1, h2] at h
      exact h.symm
    have hσinvρ : ∀ x, σ⁻¹ (ρ x) = ρ (σ⁻¹ x) := by
      intro x
      apply σ.injective
      have h1 : σ (σ⁻¹ (ρ x)) = ρ x := σ.apply_symm_apply (ρ x)
      rw [h1, hσρ]
      have h2 : σ (σ⁻¹ x) = x := σ.apply_symm_apply x
      rw [h2]
    have hmem := hH.normal σ⁻¹ hσinvB hσinvρ g hg
    rw [inv_inv] at hmem
    have h1 : σ⁻¹ (g (σ v)) = v := hv _ hmem
    have h2 := congrArg σ h1
    have h3 : σ (σ⁻¹ (g (σ v))) = g (σ v) := σ.apply_symm_apply _
    rw [h3] at h2
    exact h2
  have hlam : lam ≠ 0 := by
    rcases hρ.lam_eq with h | h <;> rw [h] <;> decide
  have hYperp : ∀ x ∈ B.orthogonal Y, ρ x ∈ B.orthogonal Y := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro w hw
    have h1 := hx (ρ w) (hYρ w hw)
    have h3 := hρ.adj w x
    rw [h1] at h3
    have h4 : lam * B w (ρ x) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp h4).resolve_left hlam
  have hcover : ∀ v, B v v ≠ 0 → v ∈ Y ∨ v ∈ B.orthogonal Y := by
    intro v hv
    by_cases hex : ∃ w ∈ Y, B w v ≠ 0
    · left
      obtain ⟨w, hwY, hwB⟩ := hex
      obtain ⟨σ, hσB, hσρ, hσ⟩ := fg_exists_sigma hρ hv
      obtain ⟨m₁, m₂, hm, hσw⟩ := hσ w hwB
      have hmem : m₁ • v + m₂ • ρ v ∈ Y := by
        rw [← hσw]
        exact Y.sub_mem (hYσ σ hσB hσρ w hwY) hwY
      have h2 : m₁ • (m₁ • v + m₂ • ρ v) - m₂ • ρ (m₁ • v + m₂ • ρ v) ∈ Y :=
        Y.sub_mem (Y.smul_mem _ hmem) (Y.smul_mem _ (hYρ _ hmem))
      have h3 : m₁ • (m₁ • v + m₂ • ρ v) - m₂ • ρ (m₁ • v + m₂ • ρ v) =
          (m₁ * m₁ + m₂ * m₂) • v := by
        simp only [map_add, map_smul, hρ.sq]
        module
      rw [h3] at h2
      have hunit : m₁ * m₁ + m₂ * m₂ ≠ 0 := by
        have h' : ∀ a b : ZMod 3, (a ≠ 0 ∨ b ≠ 0) → a * a + b * b ≠ 0 := by decide
        exact h' m₁ m₂ hm
      exact (Submodule.smul_mem_iff Y hunit).mp h2
    · right
      push Not at hex
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      exact hex w hw
  have hY0 : Y = ⊥ := by
    by_contra hbot
    have hd1 : Module.finrank (ZMod 3) Y ≠ 1 := fg_finrank_ne_one_of_rho hρ.sq Y hYρ
    have hd5 : Module.finrank (ZMod 3) Y ≠ 5 := by
      intro h5
      have h1 : Module.finrank (ZMod 3) (B.orthogonal Y) = 1 := by
        rw [LinearMap.BilinForm.finrank_orthogonal hB Y, hdim, h5]
      exact fg_finrank_ne_one_of_rho hρ.sq _ hYperp h1
    have hpos : 0 < Module.finrank (ZMod 3) Y := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hbot (Submodule.finrank_eq_zero.mp h0)
    by_cases htop : Y = ⊤
    · obtain ⟨g, hgH, hg1⟩ := hne
      apply hg1
      ext v
      have hv : v ∈ Y := by rw [htop]; trivial
      exact hv g hgH
    · have hlt : Module.finrank (ZMod 3) Y < 6 := by
        rw [← hdim]
        exact Submodule.finrank_lt htop
      obtain ⟨v, hv, hvY, hvY'⟩ :=
        fg_exists_nonisotropic_not_mem B hB hρ.symm hdim Y (by omega) (by omega)
      exact (hcover v hv).elim hvY hvY'
  have hyY : y ∈ Y := hy
  rw [hY0] at hyY
  exact (Submodule.mem_bot (ZMod 3)).mp hyY

end CFSG.OddStandard.SmallF3.Omega
