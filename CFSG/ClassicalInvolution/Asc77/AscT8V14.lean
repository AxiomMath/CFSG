module

public import CFSG.ClassicalInvolution.Asc77.AscT8V12
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups commutatorElement

namespace T8V

section SL4

variable {F : Type} [Field F]

theorem sq_of_diag_sharp (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F)) (A : GL (Fin 4) F)
    (a b : F) (ha : a ≠ 0)
    (hM : (A : Matrix (Fin 4) (Fin 4) F) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b])
    (h4 : conjAut 4 F A * conjAut 4 F A * (conjAut 4 F A * conjAut 4 F A) = 1) :
    conjAut 4 F A * conjAut 4 F A = 1 := by
  have h4' := four_ne_zero h2
  have hD : conjAut 4 F A * conjAut 4 F A = conjAut 4 F (A * A) := (map_mul _ _ _).symm
  rw [hD] at h4 ⊢
  have hDD : conjAut 4 F (A * A * (A * A)) = 1 := by rw [map_mul]; exact h4
  have hrel := exact_rel_conj h4' (A * A * (A * A)) (r := u02 1) (by rw [hDD]; rfl) (trace_u02 1)
  have hMM : ((A * A * (A * A) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![a ^ 4, 0, 0, 0; 0, a ^ 4, 0, 0; 0, 0, b ^ 4, 0; 0, 0, 0, b ^ 4] := by
    simp only [Units.val_mul, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  rw [hMM] at hrel
  have e := congrFun (congrFun hrel 0) 2
  simp [u02, Matrix.mul_apply, Fin.sum_univ_four] at e
  have e' : (b ^ 2 - a ^ 2) * (b ^ 2 + a ^ 2) = 0 := by linear_combination e
  have hAA : ((A * A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![a ^ 2, 0, 0, 0; 0, a ^ 2, 0, 0; 0, 0, b ^ 2, 0; 0, 0, 0, b ^ 2] := by
    simp only [Units.val_mul, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  rcases mul_eq_zero.mp e' with h | h
  · have hb2 : b ^ 2 = a ^ 2 := by linear_combination h
    rw [conjAut_eq_of_smul (A * A) 1 (a ^ 2) (pow_ne_zero 2 ha) ?_, map_one]
    rw [hAA, hb2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · exfalso
    apply hneg
    refine ⟨b / a, ?_⟩
    field_simp
    linear_combination -h

theorem aut_fix_blocks_sharp [Finite F] (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F))
    (α : MulAut (projectiveSL 4 F))
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, α (proj 4 F r) = proj 4 F r)
    (hfix' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, α (proj 4 F r) = proj 4 F r)
    (hα4 : α * α * (α * α) = 1) : α * α = 1 := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    subst hαeq
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := aut_fix_blocks_zero h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one] at hα4 ⊢
    exact sq_of_diag_sharp h2 hneg A a b ha hM hα4
  · rw [pow_one] at hαeq
    subst hαeq
    obtain ⟨hσ, m, n, hm, hn, hM⟩ := aut_fix_blocks_one h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one]
    exact sq_of_antidiag A m n hm hn hM

theorem psl4_autVac_sharp [Finite F] (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F))
    {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R') {x x' : SL(4, F)}
    (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1)
    (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F)) (φ : MulAut (projectiveSL 4 F))
    (hφ : ∀ r ∈ R, φ (proj 4 F r) = proj 4 F r) (hφ' : ∀ r ∈ R', φ (proj 4 F r) = proj 4 F r)
    (hφ4 : φ * φ * (φ * φ) = 1) : φ * φ = 1 := by
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
  have hα4 : α * α * (α * α) = 1 := by
    calc α * α * (α * α) = c⁻¹ * (φ * φ * (φ * φ)) * c := by rw [hα]; group
      _ = 1 := by rw [hφ4]; group
  have hfix0 := hfixα (blockSL F 4 2 0 (by norm_num)).range (hRg ▸ hφ)
  have hfix2 := hfixα (blockSL F 4 2 2 (by norm_num)).range (hR'g ▸ hφ')
  have hsq : φ * φ = c * (α * α) * c⁻¹ := by rw [hα]; group
  rw [hsq, aut_fix_blocks_sharp h2 hneg α hfix0 hfix2 hα4]
  group

theorem e4_sl4_sigma [Finite F] (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F)) {X : Type}
    [Group X] (ψ : SL(4, F) →* X) {R R' : Subgroup SL(4, F)} {y y' : SL(4, F)}
    (hP : E4Pair ψ R R' y y') (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) :
    ∀ σ : MulAut X, (∀ r ∈ R, σ (ψ r) = ψ r) → (∀ r ∈ R', σ (ψ r) = ψ r) →
      σ * σ * (σ * σ) = 1 → σ * σ = 1 := by
  intro σ hσ hσ' hσ4
  have hπk : (proj 4 F).ker = Subgroup.center SL(4, F) :=
    (ker_proj (n := 4) (K := F)).trans (scalars_eq_center 4 F)
  refine sq_eq_one_of_autVac hP.perf ψ hP.surj hP.ker (proj 4 F) (proj_surjective 4 F) hπk ?_ σ hσ
    hσ' hσ4
  intro φ hφ hφ' hφ4
  have hc : y' * y⁻¹ ∈ Subgroup.center SL(4, F) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  exact psl4_autVac_sharp h2 hneg hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2 hP.hy'1 hc φ
    hφ hφ' hφ4

theorem e4_sl4_inner [Finite F] (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F)) {X : Type}
    [Group X] (ψ : SL(4, F) →* X) {R R' : Subgroup SL(4, F)} {y y' : SL(4, F)}
    (hP : E4Pair ψ R R' y y') (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) :
    ∀ s : SL(4, F), (∀ r ∈ R, s * r = r * s) → (∀ r ∈ R', s * r = r * s) →
      ∀ k ∈ ψ.ker, s * s ≠ y * y' * k := by
  intro s hs hs' k hk hsk
  have hc : y' * y⁻¹ ∈ Subgroup.center SL(4, F) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, hRg, hR'g, -⟩ := twin_std h2 hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2
    hP.hy'1 hc
  have hcomm : ∀ (L S₁ : Subgroup SL(4, F)),
      S₁ = L.map (MulAut.conj g).toMonoidHom → (∀ r ∈ S₁, s * r = r * s) →
      ∀ r ∈ L, (g⁻¹ * s * g) * r = r * (g⁻¹ * s * g) := by
    intro L S₁ hS₁ hS r hr
    have hmem : g * r * g⁻¹ ∈ S₁ := by
      rw [hS₁]
      exact ⟨r, hr, rfl⟩
    have h := hS _ hmem
    calc (g⁻¹ * s * g) * r = g⁻¹ * (s * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * s) * g := by rw [h]
      _ = r * (g⁻¹ * s * g) := by group
  have hc0 := hcomm _ R hRg hs
  have hc2 := hcomm _ R' hR'g hs'
  generalize hs₀ : g⁻¹ * s * g = s₀ at hc0 hc2
  have hfixof : ∀ r : SL(4, F), s₀ * r = r * s₀ →
      (conjAut 4 F (Matrix.SpecialLinearGroup.toGL s₀) * fieldAut 4 F (RingEquiv.refl F))
        (proj 4 F r) = proj 4 F r := by
    intro r hr
    rw [show fieldAut 4 F (RingEquiv.refl F) = 1 from map_one _, mul_one, conjAut_toGL]
    show proj 4 F s₀ * proj 4 F r * (proj 4 F s₀)⁻¹ = proj 4 F r
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    calc s₀ * r * s₀⁻¹ = (r * s₀) * s₀⁻¹ := by rw [hr]
      _ = r := by group
  obtain ⟨-, a, b, ha, hb, hM⟩ := aut_fix_blocks_zero h2 (Matrix.SpecialLinearGroup.toGL s₀)
    (RingEquiv.refl F) (fun r hr => by
      obtain ⟨A, rfl⟩ := hr
      exact hfixof _ (hc0 _ ⟨A, rfl⟩))
    (fun r hr => by
      obtain ⟨A, rfl⟩ := hr
      exact hfixof _ (hc2 _ ⟨A, rfl⟩))
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hM
  have hcen : s * s ∈ Subgroup.center SL(4, F) := hsk ▸ Subgroup.mul_mem _ hP.cen (hP.ker hk)
  have hss0 : s₀ * s₀ = s * s := by
    have h1 := Subgroup.mem_center_iff.mp hcen g⁻¹
    calc s₀ * s₀ = g⁻¹ * (s * s) * g := by rw [← hs₀]; group
      _ = (s * s) * g⁻¹ * g := by rw [h1]
      _ = s * s := by group
  obtain ⟨r, hr4, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  have hmat : ((s * s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      !![a * a, 0, 0, 0; 0, a * a, 0, 0; 0, 0, b * b, 0; 0, 0, 0, b * b] := by
    rw [← hss0, Matrix.SpecialLinearGroup.coe_mul, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have e0 := congrFun (congrFun (hrs.trans hmat) 0) 0
  have e2 := congrFun (congrFun (hrs.trans hmat) 2) 2
  simp [Matrix.scalar_apply] at e0 e2
  have hdet : a * a * (b * b) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe s₀
    rw [hM] at this
    simpa [Matrix.det_succ_row_zero, Fin.sum_univ_succ, mul_assoc] using this
  have hrr : r * r = 1 := by
    calc r * r = (a * a) * (b * b) := congrArg₂ (· * ·) e0 e2
      _ = 1 := hdet
  rcases mul_self_eq_one_iff.mp hrr with h1 | h1
  ·
    have hs1 : s * s = 1 := by
      apply Subtype.ext
      rw [← hrs, h1]
      simp [Matrix.scalar_apply]
    rw [hs1] at hsk
    exact hP.nontwin (by rw [eq_inv_of_mul_eq_one_left hsk.symm]; exact ψ.ker.inv_mem hk)
  · exact hneg ⟨a, by rw [← e0, h1]⟩

end SL4

end T8V
end CFSG.ClassicalInvolution.Asc77
