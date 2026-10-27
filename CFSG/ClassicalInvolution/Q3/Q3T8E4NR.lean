module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.E4NR3

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups commutatorElement

section Assemble

variable {S X : Type} [Group S] [Group X]

theorem comm_of_map_comm_gen3 (ψ : S →* X) (hker : ψ.ker ≤ Subgroup.center S)
    (hk3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 → z = 1) {R : Subgroup S} (hR : ModelFacts.Gen3 R) {s : S}
    (hs : ∀ r ∈ R, ψ s * ψ r = ψ r * ψ s) : ∀ r ∈ R, s * r = r * s := by
  have h := E4G3.fix_of_gen3 ψ hker hk3 (MulAut.conj s).toMonoidHom hR (fun y hy => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    have := hs y hy
    calc ψ s * ψ y * (ψ s)⁻¹ = (ψ y * ψ s) * (ψ s)⁻¹ := by rw [this]
      _ = ψ y := by group)
  intro r hr
  have h1 := h r hr
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  calc s * r = (s * r * s⁻¹) * s := by group
    _ = r * s := by rw [h1]

structure E4Pair3N (ψ : S →* X) (R R' : Subgroup S) (y y' : S) : Prop extends
    E4G3.E4Pair3 ψ R R' y y' where
  nontwin : y * y' ∉ ψ.ker
  nc : ψ y ∉ Subgroup.center X

theorem e4_assemble3 {ψ : S →* X} {R R' : Subgroup S} {y y' : S} (hP : E4Pair3N ψ R R' y y')
    (hR : ModelFacts.Gen3 R) (hR' : ModelFacts.Gen3 R')
    (hσ1 : ∀ σ : MulAut X, (∀ r ∈ R, σ (ψ r) = ψ r) → (∀ r ∈ R', σ (ψ r) = ψ r) →
      σ * σ * (σ * σ) = 1 → σ * σ = 1)
    (he1 : ∀ s : S, (∀ r ∈ R, s * r = r * s) → (∀ r ∈ R', s * r = r * s) →
      ∀ k ∈ ψ.ker, s * s ≠ y * y' * k)
    (hA0 : oddCoreOf (R.map ψ) = ⊥) (hB0 : oddCoreOf (R'.map ψ) = ⊥) :
    (∀ σ : MulAut X, (∀ k ∈ R.map ψ, σ k * k⁻¹ ∈ oddCoreOf (R.map ψ)) →
      (∀ k ∈ R'.map ψ, σ k * k⁻¹ ∈ oddCoreOf (R'.map ψ)) → σ * σ ≠ MulAut.conj (ψ y)) ∧
    (∀ e : X, (∀ k ∈ R.map ψ, ⁅e, k⁆ ∈ oddCoreOf (R.map ψ)) →
      (∀ k ∈ R'.map ψ, ⁅e, k⁆ ∈ oddCoreOf (R'.map ψ)) → e * e ≠ ψ y * ψ y') := by
  refine ⟨fun σ h1 h2 hsq => ?_, fun e h1 h2 hsq => ?_⟩
  · have hfixR : ∀ r ∈ R, σ (ψ r) = ψ r := by
      intro r hr
      have := h1 (ψ r) (Subgroup.mem_map_of_mem ψ hr)
      rw [hA0, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    have hfixR' : ∀ r ∈ R', σ (ψ r) = ψ r := by
      intro r hr
      have := h2 (ψ r) (Subgroup.mem_map_of_mem ψ hr)
      rw [hB0, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    have hσ4 : σ * σ * (σ * σ) = 1 := by
      rw [hsq, ← map_mul, ← map_mul ψ y y, hP.hy2, map_one, map_one]
    have h3 := hσ1 σ hfixR hfixR' hσ4
    rw [hsq] at h3
    apply hP.nc
    rw [Subgroup.mem_center_iff]
    intro z
    have h4 := congrArg (fun τ : MulAut X => τ z) h3
    simp only [MulAut.conj_apply, MulAut.one_apply] at h4
    calc z * ψ y = (ψ y * z * (ψ y)⁻¹) * ψ y := by rw [h4]
      _ = ψ y * z := by group
  · obtain ⟨s, rfl⟩ := hP.surj e
    have hcR : ∀ r ∈ R, ψ s * ψ r = ψ r * ψ s := by
      intro r hr
      have := h1 (ψ r) (Subgroup.mem_map_of_mem ψ hr)
      rw [hA0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hcR' : ∀ r ∈ R', ψ s * ψ r = ψ r * ψ s := by
      intro r hr
      have := h2 (ψ r) (Subgroup.mem_map_of_mem ψ hr)
      rw [hB0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hs1 := comm_of_map_comm_gen3 ψ hP.ker hP.ker3 hR hcR
    have hs2 := comm_of_map_comm_gen3 ψ hP.ker hP.ker3 hR' hcR'
    have hk : (y * y')⁻¹ * (s * s) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hsq]
      group
    exact he1 s hs1 hs2 _ hk (by group)

end Assemble


section SL4

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.Asc77.T8V

variable {F : Type} [Field F]

theorem e4_sl4_sigma3 [Finite F] (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F)) {X : Type}
    [Group X] (ψ : SL(4, F) →* X) {R R' : Subgroup SL(4, F)} {y y' : SL(4, F)}
    (hP : E4Pair3N ψ R R' y y') (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
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

theorem e4_sl4_inner3 [Finite F] (h2 : (2 : F) ≠ 0) (hneg : ¬ IsSquare (-1 : F)) {X : Type}
    [Group X] (ψ : SL(4, F) →* X) {R R' : Subgroup SL(4, F)} {y y' : SL(4, F)}
    (hP : E4Pair3N ψ R R' y y') (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
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
    rw [show fieldAut 4 F (RingEquiv.refl F) = 1 from map_one _, mul_one,
      CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4.conjAut_toGL]
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

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.E4NR3
