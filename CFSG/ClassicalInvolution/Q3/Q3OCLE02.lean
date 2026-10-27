module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3OCL

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

section Aut

variable {F : Type} [Field F]

theorem sq_eq_one_of_card_three [Finite F] (hF : Nat.card F = 3) {a : F} (ha : a ≠ 0) :
    a * a = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.card_eq_fintype_card, hF] at h
  simpa [pow_two] using h

theorem aut_fix_blocks_sq3 [Finite F] (h2 : (2 : F) ≠ 0) (hF : Nat.card F = 3)
    (α : MulAut (projectiveSL 4 F))
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, α (proj 4 F r) = proj 4 F r)
    (hfix' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, α (proj 4 F r) = proj 4 F r) :
    α * α = 1 := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    subst hαeq
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := aut_fix_blocks_zero h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one]
    have ha2 := sq_eq_one_of_card_three hF ha
    have hb2 := sq_eq_one_of_card_three hF hb
    have hAA : A * A = 1 := by
      apply Units.ext
      rw [Units.val_mul, hM, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, ha2, hb2]
    calc conjAut 4 F A * conjAut 4 F A = conjAut 4 F (A * A) := (map_mul _ _ _).symm
      _ = 1 := by rw [hAA, map_one]
  · rw [pow_one] at hαeq
    subst hαeq
    obtain ⟨hσ, m, n, hm, hn, hM⟩ := aut_fix_blocks_one h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one]
    exact sq_of_antidiag A m n hm hn hM

theorem psl4_autSq3 [Finite F] (h2 : (2 : F) ≠ 0) (hF : Nat.card F = 3)
    {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R') {x x' : SL(4, F)}
    (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1)
    (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F)) (φ : MulAut (projectiveSL 4 F))
    (hφ : ∀ r ∈ R, φ (proj 4 F r) = proj 4 F r) (hφ' : ∀ r ∈ R', φ (proj 4 F r) = proj 4 F r) :
    φ * φ = 1 := by
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  set c : MulAut (projectiveSL 4 F) := MulAut.conj (proj 4 F g) with hcdef
  have hcp : ∀ s : SL(4, F), c (proj 4 F s) = proj 4 F (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set α : MulAut (projectiveSL 4 F) := c⁻¹ * φ * c with hα
  have hαp : ∀ s : SL(4, F), α (proj 4 F s) = (c⁻¹) (φ (c (proj 4 F s))) := fun s => rfl
  have hfixα : ∀ (S : Subgroup SL(4, F)), (∀ r ∈ S.map (MulAut.conj g).toMonoidHom,
      φ (proj 4 F r) = proj 4 F r) → ∀ r ∈ S, α (proj 4 F r) = proj 4 F r := by
    intro S hS r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hαp, hcp, hS _ hmem, ← hcp]
    simp
  have hfix0 := hfixα (blockSL F 4 2 0 (by norm_num)).range (hRg ▸ hφ)
  have hfix2 := hfixα (blockSL F 4 2 2 (by norm_num)).range (hR'g ▸ hφ')
  have hsq : φ * φ = c * (α * α) * c⁻¹ := by rw [hα]; group
  rw [hsq, aut_fix_blocks_sq3 h2 hF α hfix0 hfix2]
  group

end Aut

end CFSG.ClassicalInvolution.Q3.Q3OCL
