module

public import CFSG.ClassicalInvolution.Asc77.AscT7MN
public import CFSG.ClassicalInvolution.Asc77.AscT7MM

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

set_option linter.unusedSectionVars false

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F]

theorem alphaOf_klein_conj (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {X : Type} [Group X]
    [Finite X] {θ : X →* MulAut (projectiveSL 4 F)} {ι : projectiveSL 4 F →* X}
    (hθ : Function.Injective θ) (hι : ∀ p, θ (ι p) = MulAut.conj p) (Γ : GL (Fin 4) F) {y z : X}
    (hy : θ y = conjAut 4 F Γ * conjAut 4 F (dGL 1) * (conjAut 4 F Γ)⁻¹)
    (hz : z = ι (conjAut 4 F Γ (proj 4 F (x0 F)))) :
    alphaOf (Subgroup.closure ({z, y} : Set X)) = ⊥ := by
  set ρ : MulAut (projectiveSL 4 F) := (conjAut 4 F Γ)⁻¹ with hρ
  set θ' : X →* MulAut (projectiveSL 4 F) := (MulAut.conj ρ).toMonoidHom.comp θ with hθ'
  set ι' : projectiveSL 4 F →* X := ι.comp (conjAut 4 F Γ).toMonoidHom with hι'def
  have hθ'inj : Function.Injective θ' := (MulAut.conj ρ).injective.comp hθ
  have hθ'ι' : ∀ p, θ' (ι' p) = MulAut.conj p := by
    intro p
    have h1 : θ' (ι' p) = ρ * θ (ι (conjAut 4 F Γ p)) * ρ⁻¹ := rfl
    rw [h1, hι, mulAut_conj_conj]
    congr 1
    show (conjAut 4 F Γ)⁻¹ (conjAut 4 F Γ p) = p
    simp
  have hy' : θ' y = conjAut 4 F (dGL 1) := by
    show (conjAut 4 F Γ)⁻¹ * θ y * ((conjAut 4 F Γ)⁻¹)⁻¹ = _
    rw [hy, hρ]
    group
  have key := alphaOf_klein_diag h2 h4 hθ'inj hθ'ι' hy'
  have hz' : ι' (proj 4 F (x0 F)) = z := by rw [hz]; rfl
  rw [hz'] at key
  exact key

theorem conj_injective_psl : Function.Injective (MulAut.conj : projectiveSL 4 F →* _) := by
  intro a b h
  have hc : MulAut.conj (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h]; group
  have : a⁻¹ * b = 1 := centre_trivial _ (fun q => by
    have h1 := congrArg (fun φ : MulAut (projectiveSL 4 F) => φ q) hc
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc a⁻¹ * b * q = (a⁻¹ * b * q * (a⁻¹ * b)⁻¹) * (a⁻¹ * b) := by group
      _ = q * (a⁻¹ * b) := by rw [h1])
  exact inv_mul_eq_one.mp this

theorem fixes_of_comm {φ : MulAut (projectiveSL 4 F)} {p : projectiveSL 4 F}
    (h : φ * MulAut.conj p = MulAut.conj p * φ) : φ p = p := by
  have h1 : MulAut.conj (φ p) = MulAut.conj p := by
    rw [← mulAut_conj_conj, h]
    group
  exact conj_injective_psl h1

theorem exists_Gamma (h2 : (2 : F) ≠ 0) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R') {x x' : SL(4, F)}
    (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1)
    (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F)) {k : SL(4, F)} (hkR : k ∈ R)
    (hkk : proj 4 F k * proj 4 F k = proj 4 F x) {φ : MulAut (projectiveSL 4 F)}
    (hφ : ∀ r ∈ R, φ (proj 4 F r) = proj 4 F r) (hφ' : ∀ r ∈ R', φ (proj 4 F r) = proj 4 F r)
    (hφ2 : φ * φ = MulAut.conj (proj 4 F x)) :
    ∃ Γ : GL (Fin 4) F, MulAut.conj (proj 4 F k) * φ =
        conjAut 4 F Γ * conjAut 4 F (dGL 1) * (conjAut 4 F Γ)⁻¹ ∧
      proj 4 F x = conjAut 4 F Γ (proj 4 F (x0 F)) := by
  obtain ⟨g, hRg, hR'g, hxg, hkg⟩ := twin_std_k h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc hkR hkk
  set c : MulAut (projectiveSL 4 F) := MulAut.conj (proj 4 F g) with hcdef
  have hcp : ∀ s : SL(4, F), c (proj 4 F s) = proj 4 F (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set α : MulAut (projectiveSL 4 F) := c⁻¹ * φ * c with hα
  have hfixα : ∀ (S S0 : Subgroup SL(4, F)), S = S0.map (MulAut.conj g).toMonoidHom →
      (∀ r ∈ S, φ (proj 4 F r) = proj 4 F r) → ∀ r ∈ S0, α (proj 4 F r) = proj 4 F r := by
    intro S S0 hS hSfix r hr
    have hmem : g * r * g⁻¹ ∈ S := by
      rw [hS]
      exact ⟨r, hr, rfl⟩
    show (c⁻¹) (φ (c (proj 4 F r))) = proj 4 F r
    rw [hcp, hSfix _ hmem, ← hcp]
    simp
  have hfix0 := hfixα R (R0 F) hRg hφ
  have hfix2 := hfixα R' (R0' F) hR'g hφ'
  have hα2 : α * α = MulAut.conj (proj 4 F (x0 F)) := by
    have h1 : α * α = c⁻¹ * (φ * φ) * c := by rw [hα]; group
    have hconj : MulAut.conj (proj 4 F (g * x0 F * g⁻¹)) =
        c * MulAut.conj (proj 4 F (x0 F)) * c⁻¹ := by
      rw [hcdef]
      simp only [map_mul, map_inv]
    rw [h1, hφ2, hxg, hconj]
    group
  obtain ⟨A, a, b, ha, hb, hab, hA, hαA⟩ := autSq_data h2 α hfix0 hfix2 hα2
  obtain ⟨U, hUx, hUconj⟩ := exists_U h2 ha hb hab A hA
  have hUfix : conjAut 4 F U (proj 4 F (x0 F)) = proj 4 F (x0 F) := by
    apply fixes_of_comm
    rw [← OuterL4.conjAut_toGL, ← map_mul, ← map_mul, hUx]
  have hΓ : conjAut 4 F (Matrix.SpecialLinearGroup.toGL g * U) = c * conjAut 4 F U := by
    rw [map_mul, hcdef, OuterL4.conjAut_toGL]
  refine ⟨Matrix.SpecialLinearGroup.toGL g * U, ?_, ?_⟩
  · have hφc : φ = c * α * c⁻¹ := by rw [hα]; group
    have hπk : MulAut.conj (proj 4 F k) = c * conjAut 4 F (Matrix.SpecialLinearGroup.toGL
        (blockSL F 4 2 0 (by norm_num) r0)) * c⁻¹ := by
      rw [hkg, hcdef, OuterL4.conjAut_toGL]
      simp only [map_mul, map_inv]
    have hmid : conjAut 4 F (Matrix.SpecialLinearGroup.toGL
        (blockSL F 4 2 0 (by norm_num) r0)) * conjAut 4 F A =
        conjAut 4 F U * conjAut 4 F (dGL 1) * (conjAut 4 F U)⁻¹ := by
      rw [← map_mul]
      exact hUconj
    rw [hπk, hφc, hαA, hΓ]
    calc c * conjAut 4 F (Matrix.SpecialLinearGroup.toGL (blockSL F 4 2 0 (by norm_num) r0)) *
          c⁻¹ * (c * conjAut 4 F A * c⁻¹) =
        c * (conjAut 4 F (Matrix.SpecialLinearGroup.toGL (blockSL F 4 2 0 (by norm_num) r0)) *
          conjAut 4 F A) * c⁻¹ := by group
      _ = c * (conjAut 4 F U * conjAut 4 F (dGL 1) * (conjAut 4 F U)⁻¹) * c⁻¹ := by rw [hmid]
      _ = c * conjAut 4 F U * conjAut 4 F (dGL 1) * (c * conjAut 4 F U)⁻¹ := by group
  · rw [hxg, hΓ]
    show proj 4 F (g * x0 F * g⁻¹) = (c * conjAut 4 F U) (proj 4 F (x0 F))
    rw [MulAut.mul_apply, hUfix, hcp]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4
