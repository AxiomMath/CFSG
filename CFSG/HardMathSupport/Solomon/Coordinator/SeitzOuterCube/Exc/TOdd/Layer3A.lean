module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.L1
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.L2
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.L3
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.LayerFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.Shape
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxMain

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Seitz CFSG.Open TauCeti CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec4.E27
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement


variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem pow_three_of_conj_mem (P : D4ParOdd ℓ f X σ) {E : Subgroup (MulAut (C0 σ))}
    (hE : IsElemAbelian 3 E) {x : C0 σ} (hx : MulAut.conj x ∈ E) : x ^ 3 = 1 := by
  apply conj_injective_odd P
  rw [map_pow, map_one]
  exact hE.2 _ hx

theorem layer_le_closure_fixed_A0_odd (P : D4ParOdd ℓ f X σ) {E : Subgroup (MulAut (C0 σ))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27) {x : C0 σ}
    (hx : MulAut.conj x ∈ E) (hx1 : x ≠ 1) (hxA : x ∈ A0sub σ) :
    layerSub σ x ≤ Subgroup.closure {l | l ∈ layerSub σ x ∧ ∃ y ∈ E,
      y ∉ Subgroup.zpowers (MulAut.conj x : MulAut (C0 σ)) ∧ y l = l} := by
  haveI : Finite (C0 σ) := finite_C0
  have hx3 : x ^ 3 = 1 := pow_three_of_conj_mem P hE hx
  have hxX : IsClassX σ x := ⟨hx3, hx1, 1, by simpa using (Subgroup.mem_inf.1 hxA).1⟩
  have hinj := conj_injective_odd P
  have hτx : tauAut σ x = x := (Subgroup.mem_inf.1 hxA).2
  have hshape := shape_of_mem_E_odd P hE
  obtain ⟨hxD, hZ3c⟩ := classX_layer_odd P hxX
  obtain ⟨hH, hC⟩ := layer_facts_odd' P hxX
  have hZD : ∀ w ∈ layerSub σ x, (∀ d ∈ layerSub σ x, w * d = d * w) →
      w ∈ Subgroup.zpowers x := fun w hw hwc => hZ3c w hw (hC w hw hwc) hwc
  have hH' : ∃ y ∈ layerSub σ x, ∃ p ∈ layerSub σ x,
      p * y * p⁻¹ * y⁻¹ ≠ 1 ∧ (p * y * p⁻¹ * y⁻¹) ^ 3 = 1 ∧
        ∀ d ∈ layerSub σ x, (p * y * p⁻¹ * y⁻¹) * d = d * (p * y * p⁻¹ * y⁻¹) := by
    obtain ⟨y, hy, p, hp, u, -, hu1, hu3, huc, hup⟩ := hH
    exact ⟨y, hy, p, hp, by rw [hup]; exact hu1, by rw [hup]; exact hu3,
      by rw [hup]; exact huc⟩
  obtain ⟨hZab, hZ3⟩ := layer_center_facts_odd P hxX hxD hZD hH'
  rcases P.mod_three with hq1 | hq2
  · have hτD := tau_fixes_layer_linear_odd P hq1 hxX hxA (layer_card_linear_odd P hq1 hxX)
    obtain ⟨F, _, _, h4, h3, e, hact⟩ := layer_linear_model_odd P hq1 hxX
    refine layer_closure_of_plane (C := cenX σ x) (D := layerSub σ x) hinj (tauAut σ) x hx3 hx1
      hτx rfl rfl hE hx hcard hshape hτD hZab hZ3 hZD
      (fun φ => ∃ M : Matrix.GeneralLinearGroup (Fin 3) F, IsConjBy φ M) e ?_
      (planeThm_linear h4 h3)
    intro g hg φ hφ
    obtain ⟨N, hN⟩ := hact g hg
    refine ⟨N, fun t => ?_⟩
    have hd : g * ((e.symm t : layerSub σ x) : C0 σ) * g⁻¹ ∈ layerSub σ x :=
      layer_conj_mem (cenX σ x) hg (e.symm t).2
    have h1 := hφ (e.symm t) ⟨_, hd⟩ rfl
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    have h2 := hN (e.symm t) ⟨_, hd⟩ rfl
    rw [MulEquiv.apply_symm_apply] at h2
    exact h2
  · have hτD := tau_fixes_layer_unitary_odd P hq2 hxX hxA (layer_card_unitary_odd P hq2 hxX)
    obtain ⟨F, _, hF, e, hact⟩ := layer_unitary_model_odd P hq2 hxX
    have hq : 2 < ℓ ^ f := lt_of_lt_of_le (by norm_num) P.five_le
    refine layer_closure_of_plane (C := cenX σ x) (D := layerSub σ x) hinj (tauAut σ) x hx3 hx1
      hτx rfl rfl hE hx hcard hshape hτD hZab hZ3 hZD
      (fun φ => φ ∈ (CFSG.RankThree.PartTwo.KFacts.suConj hF).range) e ?_
      (planeThm_unitary hF hq2 hq)
    intro g hg φ hφ
    obtain ⟨A, hA⟩ := hact g hg
    refine ⟨A, ?_⟩
    ext t
    have hd : g * ((e.symm t : layerSub σ x) : C0 σ) * g⁻¹ ∈ layerSub σ x :=
      layer_conj_mem (cenX σ x) hg (e.symm t).2
    have h1 := hφ (e.symm t) ⟨_, hd⟩ rfl
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 := hA (e.symm t) ⟨_, hd⟩ rfl
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h1, h2]

theorem layer_le_closure_fixed_odd (P : D4ParOdd ℓ f X σ) {E : Subgroup (MulAut (C0 σ))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27) {x : C0 σ}
    (hx : MulAut.conj x ∈ E) (hx1 : x ≠ 1) (hxX : IsClassX σ x) :
    layerSub σ x ≤ Subgroup.closure {l | l ∈ layerSub σ x ∧ ∃ y ∈ E,
      y ∉ Subgroup.zpowers (MulAut.conj x : MulAut (C0 σ)) ∧ y l = l} := by
  haveI : Finite (C0 σ) := finite_C0
  obtain ⟨hx3, -, g₀, hg₀⟩ := hxX
  have hx₁3 : (g₀ * x * g₀⁻¹) ^ 3 = 1 := by
    rw [← MulAut.conj_apply, ← map_pow, hx3, map_one]
  have hx₁1 : g₀ * x * g₀⁻¹ ≠ 1 := fun h1 =>
    hx1 ((MulAut.conj g₀).injective (by rw [MulAut.conj_apply, h1, map_one]))
  obtain ⟨g₁, -, hg₁⟩ := exists_conj_A0_odd P hg₀ hx₁3 hx₁1
  set h : C0 σ := g₁ * g₀ with hh
  have hxh : h * x * h⁻¹ ∈ A0sub σ := by
    have : h * x * h⁻¹ = g₁ * (g₀ * x * g₀⁻¹) * g₁⁻¹ := by rw [hh]; group
    rw [this]
    exact hg₁
  set φ : MulAut (C0 σ) := MulAut.conj h with hφ
  set E' : Subgroup (MulAut (C0 σ)) := E.map (MulAut.congr φ).toMonoidHom with hE'
  have hE'ab : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE _
  have hE'card : Nat.card E' = 27 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]
  have hx'E : MulAut.conj (h * x * h⁻¹) ∈ E' :=
    ⟨MulAut.conj x, hx, CFSG.RankThree.PartTwo.Sec4.E27.congr_conj_conj h x⟩
  have hx'1 : h * x * h⁻¹ ≠ 1 := fun h1 =>
    hx1 ((MulAut.conj h).injective (by rw [MulAut.conj_apply, h1, map_one]))
  have key := layer_le_closure_fixed_A0_odd P hE'ab hE'card hx'E hx'1 hxh
  have hback := stepOK_map (MulAut.conj h⁻¹) key
  have ha := layer_map_conj σ h x
  have hb : E'.map (MulAut.congr (MulAut.conj h⁻¹)).toMonoidHom = E := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have : (MulAut.congr (MulAut.conj h⁻¹)) ((MulAut.congr φ) y) = y := by
        rw [hφ, congr_apply_eq, congr_apply_eq]
        simp [map_inv]
        group
      show (MulAut.congr (MulAut.conj h⁻¹)) ((MulAut.congr φ) y) ∈ E
      rw [this]
      exact hy
    · intro hz
      refine ⟨(MulAut.congr φ) z, ⟨z, hz, rfl⟩, ?_⟩
      show (MulAut.congr (MulAut.conj h⁻¹)) ((MulAut.congr φ) z) = z
      rw [hφ, congr_apply_eq, congr_apply_eq]
      simp [map_inv]
      group
  have hc : (MulAut.congr (MulAut.conj h⁻¹)) (MulAut.conj (h * x * h⁻¹)) = MulAut.conj x := by
    rw [CFSG.RankThree.PartTwo.Sec4.E27.congr_conj_conj]
    congr 1
    group
  rw [ha, hb, hc] at hback
  exact hback

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
