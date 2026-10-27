module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped Matrix MatrixGroups

section FrameCommutant

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

private theorem transv01 (c : F) :
    ((Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] :=
  Frame.coe_transvection_zero_one c

private theorem transv10 (c : F) :
    ((Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] :=
  Frame.coe_transvection_one_zero c

theorem eq_zero_of_forall_mul_eq {X : Matrix (Fin 2) (Fin 2) F}
    (h : ∀ A : SL(2, F), (A : Matrix (Fin 2) (Fin 2) F) * X = X) : X = 0 := by
  have h1 := h (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1)
  have h2 := h (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1)
  rw [transv01] at h1
  rw [transv10] at h2
  ext i j
  fin_cases i <;> fin_cases j
  · have := congrFun (congrFun h2 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    simpa using this
  · have := congrFun (congrFun h2 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    simpa using this
  · have := congrFun (congrFun h1 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    simpa using this
  · have := congrFun (congrFun h1 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    simpa using this

theorem mulLeft_comm_of_transvections {T : Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F}
    (h1 : ∀ Y, T (!![1, 1; 0, 1] * Y) = !![1, 1; 0, 1] * T Y)
    (h2 : ∀ Y, T (!![1, 0; 1, 1] * Y) = !![1, 0; 1, 1] * T Y) (M Y : Matrix (Fin 2) (Fin 2) F) :
    T (M * Y) = M * T Y := by
  have e12 : ∀ Y, T (!![0, 1; 0, 0] * Y) = !![0, 1; 0, 0] * T Y := fun Y => by
    have := h1 Y
    have h3 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * Y = Y + !![0, 1; 0, 0] * Y := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have h4 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * T Y = T Y + !![0, 1; 0, 0] * T Y := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    rw [h3, map_add, h4] at this
    exact add_left_cancel this
  have e21 : ∀ Y, T (!![0, 0; 1, 0] * Y) = !![0, 0; 1, 0] * T Y := fun Y => by
    have := h2 Y
    have h3 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * Y = Y + !![0, 0; 1, 0] * Y := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring
    have h4 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * T Y = T Y + !![0, 0; 1, 0] * T Y := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring
    rw [h3, map_add, h4] at this
    exact add_left_cancel this
  have e11 : ∀ Y, T (!![1, 0; 0, 0] * Y) = !![1, 0; 0, 0] * T Y := fun Y => by
    have h3 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) * Y =
        !![0, 1; 0, 0] * (!![0, 0; 1, 0] * Y) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have h4 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) * T Y =
        !![0, 1; 0, 0] * (!![0, 0; 1, 0] * T Y) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    rw [h3, h4, e12, e21]
  have e22 : ∀ Y, T (!![0, 0; 0, 1] * Y) = !![0, 0; 0, 1] * T Y := fun Y => by
    have h3 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) * Y =
        !![0, 0; 1, 0] * (!![0, 1; 0, 0] * Y) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    have h4 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) * T Y =
        !![0, 0; 1, 0] * (!![0, 1; 0, 0] * T Y) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    rw [h3, h4, e21, e12]
  have hM : M = M 0 0 • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) +
      M 0 1 • !![0, 1; 0, 0] + M 1 0 • !![0, 0; 1, 0] + M 1 1 • !![0, 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  conv_lhs => rw [hM]
  conv_rhs => rw [hM]
  simp only [add_mul, smul_mul_assoc, map_add, map_smul, e11, e12, e21, e22]

theorem exists_mulRight_of_commute_La (fr : Frame Q) (g : V →ₗ[F] V)
    (hg : ∀ (A : SL(2, F)) x, g (fr.La A x) = fr.La A (g x)) :
    ∃ h : Matrix (Fin 2) (Fin 2) F, (∀ Y, g (fr.incl Y) = fr.incl (Y * h)) ∧
      ∀ x, fr.coords x = 0 → fr.coords (g x) = 0 := by
  have hperp : ∀ x, fr.coords x = 0 → fr.coords (g x) = 0 := by
    intro x hx
    apply eq_zero_of_forall_mul_eq
    intro A
    rw [← Frame.coords_La, ← hg A x, Frame.La_apply_of_coords_eq_zero fr A hx]
  let T : Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F := fr.coords ∘ₗ g ∘ₗ fr.incl
  have hT : ∀ (A : SL(2, F)) Y, T ((A : Matrix (Fin 2) (Fin 2) F) * Y) =
      (A : Matrix (Fin 2) (Fin 2) F) * T Y := fun A Y => by
    change fr.coords (g (fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * Y))) =
      (A : Matrix (Fin 2) (Fin 2) F) * fr.coords (g (fr.incl Y))
    rw [← Frame.La_apply_incl, hg, Frame.coords_La]
  have hT1 : ∀ Y, T (!![1, 1; 0, 1] * Y) = !![1, 1; 0, 1] * T Y := fun Y => by
    have := hT (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1) Y
    rwa [transv01] at this
  have hT2 : ∀ Y, T (!![1, 0; 1, 1] * Y) = !![1, 0; 1, 1] * T Y := fun Y => by
    have := hT (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1) Y
    rwa [transv10] at this
  have hL := mulLeft_comm_of_transvections hT1 hT2
  have hTY : ∀ Y, T Y = Y * T 1 := fun Y => by
    have := hL Y 1
    rwa [mul_one] at this
  let P : Matrix (Fin 2) (Fin 2) F →ₗ[F] V := g ∘ₗ fr.incl - fr.incl ∘ₗ T
  have hP : ∀ Y, P Y = g (fr.incl Y) - fr.incl (T Y) := fun Y => rfl
  have hPc : ∀ Y, fr.coords (P Y) = 0 := fun Y => by
    rw [hP, map_sub, Frame.coords_incl]
    change fr.coords (g (fr.incl Y)) - T Y = 0
    exact sub_self _
  have hPA : ∀ (A : SL(2, F)) Y, P ((A : Matrix (Fin 2) (Fin 2) F) * Y) = P Y := fun A Y => by
    rw [hP, hP, ← Frame.La_apply_incl, hg, hT A Y, ← Frame.La_apply_incl]
    have h1 : g (fr.incl Y) = fr.incl (T Y) + P Y := by rw [hP]; abel
    rw [h1, map_add, Frame.La_apply_incl, Frame.La_apply_of_coords_eq_zero fr A (hPc Y)]
    abel
  have hP1 : ∀ Y, P (!![1, 1; 0, 1] * Y) = P Y := fun Y => by
    have := hPA (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1) Y
    rwa [transv01] at this
  have hP2 : ∀ Y, P (!![1, 0; 1, 1] * Y) = P Y := fun Y => by
    have := hPA (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1) Y
    rwa [transv10] at this
  have p12 : ∀ Y, P (!![0, 1; 0, 0] * Y) = 0 := fun Y => by
    have := hP1 Y
    have h3 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * Y = Y + !![0, 1; 0, 0] * Y := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    rw [h3, map_add] at this
    exact add_eq_left.mp this
  have p21 : ∀ Y, P (!![0, 0; 1, 0] * Y) = 0 := fun Y => by
    have := hP2 Y
    have h3 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * Y = Y + !![0, 0; 1, 0] * Y := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring
    rw [h3, map_add] at this
    exact add_eq_left.mp this
  have p11 : ∀ Y, P (!![1, 0; 0, 0] * Y) = 0 := fun Y => by
    have h3 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) * Y =
        !![0, 1; 0, 0] * (!![0, 0; 1, 0] * Y) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    rw [h3, p12]
  have p22 : ∀ Y, P (!![0, 0; 0, 1] * Y) = 0 := fun Y => by
    have h3 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) * Y =
        !![0, 0; 1, 0] * (!![0, 1; 0, 0] * Y) := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    rw [h3, p21]
  have hP0 : ∀ Y, P Y = 0 := fun Y => by
    have hM : Y = Y 0 0 • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) +
        Y 0 1 • !![0, 1; 0, 0] + Y 1 0 • !![0, 0; 1, 0] + Y 1 1 • !![0, 0; 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have h1 := p11 1
    have h2 := p12 1
    have h3 := p21 1
    have h4 := p22 1
    rw [mul_one] at h1 h2 h3 h4
    rw [hM, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, h2, h3, h4]
    simp
  refine ⟨T 1, fun Y => ?_, hperp⟩
  have := hP0 Y
  rw [hP, sub_eq_zero] at this
  rw [this, hTY Y]

theorem exists_smul_one_of_commute {h : Matrix (Fin 2) (Fin 2) F}
    (h1 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * h = h * !![1, 1; 0, 1])
    (h2 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * h = h * !![1, 0; 1, 1]) :
    ∃ c : F, h = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  refine ⟨h 0 0, ?_⟩
  have a1 := congrFun (congrFun h1 0) 0
  have a2 := congrFun (congrFun h1 0) 1
  have b1 := congrFun (congrFun h2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 b1
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa using b1
  · simpa using a1
  · simp
    linear_combination a2

theorem swap_La_incl (fr : Frame Q) (B : SL(2, F)) (Y : Matrix (Fin 2) (Fin 2) F) :
    fr.swap.La B (fr.incl Y) =
      fr.incl (Y * sigmaLin (B : Matrix (Fin 2) (Fin 2) F)) := by
  rw [Frame.La_swap_apply, Frame.embLin_apply, Frame.coords_incl]
  change fr.incl Y + fr.incl (Y * sigmaLin (B : Matrix (Fin 2) (Fin 2) F) - Y) = _
  rw [map_sub]
  abel

theorem exists_scalar_of_commute_La_swap (fr : Frame Q) (G : V →ₗ[F] V)
    (hG : ∀ (A : SL(2, F)) x, G (fr.La A x) = fr.La A (G x))
    (hG' : ∀ (B : SL(2, F)) x, G (fr.swap.La B x) = fr.swap.La B (G x)) :
    ∃ c : F, ∀ Y, G (fr.incl Y) = c • fr.incl Y := by
  obtain ⟨h, hh, -⟩ := exists_mulRight_of_commute_La fr G hG
  have hcomm : ∀ B : SL(2, F), sigmaLin (B : Matrix (Fin 2) (Fin 2) F) * h =
      h * sigmaLin (B : Matrix (Fin 2) (Fin 2) F) := fun B => by
    have h1 := hG' B (fr.incl 1)
    rw [swap_La_incl, hh, hh, swap_La_incl] at h1
    simpa using fr.incl_injective h1
  have c1 := hcomm (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (-1))
  have c2 := hcomm (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (-1))
  rw [transv10] at c1
  rw [transv01] at c2
  have e1 : sigmaLin (!![1, 0; -1, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]
  have e2 : sigmaLin (!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]
  rw [e1] at c1
  rw [e2] at c2
  obtain ⟨c, hc⟩ := exists_smul_one_of_commute c1 c2
  refine ⟨c, fun Y => ?_⟩
  rw [hh, hc, mul_smul_comm, mul_one, map_smul]

section Weights

variable {m : ℕ} (Fr : HypFrame Q m)

theorem polar_eq_zero_of_eigen {τ : V ≃ₗ[F] V} (hτ : ∀ x, Q (τ x) = Q x) {y v : V} {a b : F}
    (hy : τ y = a • y) (hv : τ v = b • v) (h : a * b ≠ 1) : polar Q y v = 0 := by
  have h1 : polar Q (τ y) (τ v) = polar Q y v := by
    simp only [QuadraticMap.polar, ← map_add, hτ]
  rw [hy, hv, polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
  have h2 : (a * b - 1) * polar Q y v = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr h)

theorem eq_smul_vec_of_polar_eq_zero
    (hspan : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x = 0) {x : V} (i : Fin m) (s : Bool)
    (hx : ∀ a r, (a, r) ≠ (i, !s) → polar Q x (Fr.vec a r) = 0) :
    x = polar Q x (Fr.vec i (!s)) • Fr.vec i s := by
  have key := hspan (x - polar Q x (Fr.vec i (!s)) • Fr.vec i s) (fun a r => by
    rw [polar_sub_left, polar_smul_left, Fr.polar_vec_vec, smul_eq_mul]
    by_cases h : i = a ∧ s = !r
    · obtain ⟨h1, h2⟩ := h
      subst h1
      have hr : r = !s := by rw [h2]; simp
      subst hr
      simp
    · have hne : (a, r) ≠ (i, !s) := fun hh => h ⟨(Prod.ext_iff.mp hh).1.symm, by
        have hr : r = !s := (Prod.ext_iff.mp hh).2
        rw [hr]; simp⟩
      rw [ite_eq_right h, mul_zero, sub_zero, hx a r hne])
  exact sub_eq_zero.mp key

end Weights

section Rho

theorem zpow_eq_one_iff_of_abs_le {u : F} (hu1 : u ≠ 1) (hu2 : u ≠ -1) {w : ℤ}
    (hw : -2 ≤ w ∧ w ≤ 2) : u ^ w = 1 ↔ w = 0 := by
  have hsq : u ^ 2 ≠ 1 := fun h => by
    have : (u - 1) * (u + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact hu1 (sub_eq_zero.mp h)
    · exact hu2 (eq_neg_of_add_eq_zero_left h)
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := hw
    interval_cases w
    · exact absurd (by simpa using h) hsq
    · exact absurd (by simpa using h) hu1
    · rfl
    · exact absurd (by simpa using h) hu1
    · exact absurd (by simpa using h) hsq
  · rintro rfl
    simp

theorem zpow_ne_neg_one {u : F} (h2 : (2 : F) ≠ 0) (hu2 : u ≠ -1) {w : ℤ}
    (hw : -1 ≤ w ∧ w ≤ 1) : u ^ w ≠ -1 := by
  obtain ⟨hw1, hw2⟩ := hw
  interval_cases w
  · intro h
    have : u⁻¹ = -1 := by simpa using h
    exact hu2 (by simpa using congrArg (·⁻¹) this)
  · simp only [zpow_zero]
    intro h
    exact h2 (by linear_combination h)
  · simpa using hu2

end Rho

section Torus

variable {m : ℕ} (Fr : HypFrame Q m)

theorem torus_vec {a b : Fin m} (hab : a ≠ b) (u : Fˣ) (n : Fin m) (r : Bool) :
    spinAction Q (Fr.longTorus hab true false u) (Fr.vec n r) =
      ((u : F) ^ longCoroot a b true false n r) • Fr.vec n r := by
  rw [Fr.spinAction_longTorus_vec, Units.val_zpow_eq_zpow_val]

theorem longCoroot_bounds {a b : Fin m} (hab : a ≠ b) (n : Fin m) (r : Bool) :
    -1 ≤ longCoroot a b true false n r ∧ longCoroot a b true false n r ≤ 1 := by
  by_cases h1 : n = a
  · subst h1
    simp [longCoroot, hab]
    split_ifs <;> omega
  · by_cases h2 : n = b
    · subst h2
      simp [longCoroot, h1]
      split_ifs <;> omega
    · simp [longCoroot, h1, h2]

theorem polar_vec_ne_zero (i : Fin m) (s : Bool) : Fr.vec i s ≠ 0 := fun h => by
  have := Fr.polar_vec_not i s
  rw [h, polar_zero_left] at this
  exact zero_ne_one this

theorem eta_eq_one (hspan : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x = 0)
    (h2 : (2 : F) ≠ 0) (g : V →ₗ[F] V) (hg : Function.Injective g) {u : Fˣ}
    (hu2 : (u : F) ≠ -1) {a b : Fin m} (hab : a ≠ b) {η : F} (hη : η = 1 ∨ η = -1)
    (hcomm : ∀ x, g (spinAction Q (Fr.longTorus hab true false u) x) =
      η • spinAction Q (Fr.longTorus hab true false u) (g x))
    {j : Fin m} (hja : j ≠ a) (hjb : j ≠ b) : η = 1 := by
  rcases hη with rfl | rfl
  · rfl
  exfalso
  set T := spinAction Q (Fr.longTorus hab true false u) with hT
  have hv0 : T (Fr.vec j true) = Fr.vec j true := by
    rw [hT, torus_vec Fr hab u j true]
    simp [longCoroot, hja, hjb]
  have h1 := hcomm (Fr.vec j true)
  rw [hv0, neg_one_smul] at h1
  have hy : T (g (Fr.vec j true)) = (-1 : F) • g (Fr.vec j true) := by
    rw [neg_one_smul]
    have := congrArg Neg.neg h1
    rw [neg_neg] at this
    exact this.symm
  have hy0 : g (Fr.vec j true) = 0 := by
    apply hspan
    intro n r
    refine polar_eq_zero_of_eigen (τ := T) (fun x => map_spinAction Q _ x) hy
      (torus_vec Fr hab u n r) ?_
    have := zpow_ne_neg_one h2 hu2 (longCoroot_bounds hab n r)
    intro h
    exact this (by linear_combination -h)
  have : Fr.vec j true = 0 := hg (by rw [hy0, map_zero])
  exact polar_vec_ne_zero Fr j true this

theorem polar_g_vec_eq_zero (g : V →ₗ[F] V) {u : Fˣ} (hu1 : (u : F) ≠ 1) (hu2 : (u : F) ≠ -1)
    {a b : Fin m} (hab : a ≠ b)
    (hcomm : ∀ x, g (spinAction Q (Fr.longTorus hab true false u) x) =
      spinAction Q (Fr.longTorus hab true false u) (g x)) (s : Bool) (n : Fin m) (r : Bool)
    (hw : longCoroot a b true false n r + longCoroot a b true false a s ≠ 0) :
    polar Q (g (Fr.vec a s)) (Fr.vec n r) = 0 := by
  set T := spinAction Q (Fr.longTorus hab true false u) with hT
  have hy : T (g (Fr.vec a s)) = ((u : F) ^ longCoroot a b true false a s) • g (Fr.vec a s) := by
    rw [← hcomm, hT, torus_vec Fr hab u a s, map_smul]
  refine polar_eq_zero_of_eigen (τ := T) (fun x => map_spinAction Q _ x) hy
    (torus_vec Fr hab u n r) ?_
  intro h
  rw [← zpow_add₀ u.ne_zero] at h
  have hb1 := longCoroot_bounds hab a s
  have hb2 := longCoroot_bounds hab n r
  have := (zpow_eq_one_iff_of_abs_le hu1 hu2 (w := longCoroot a b true false a s +
    longCoroot a b true false n r) (by omega)).mp h
  exact hw (by omega)

theorem exists_smul_vec_of_two_tori (hspan : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x = 0)
    (h2 : (2 : F) ≠ 0) (g : V →ₗ[F] V) (hg : Function.Injective g) {u : Fˣ}
    (hu1 : (u : F) ≠ 1) (hu2 : (u : F) ≠ -1) {i k k' j : Fin m} (hik : i ≠ k) (hik' : i ≠ k')
    (hkk' : k ≠ k') (hji : j ≠ i) (hjk : j ≠ k) (hjk' : j ≠ k')
    (hc : ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x, g (spinAction Q (Fr.longTorus hik true false u) x) =
      η • spinAction Q (Fr.longTorus hik true false u) (g x))
    (hc' : ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x, g (spinAction Q (Fr.longTorus hik' true false u) x) =
      η • spinAction Q (Fr.longTorus hik' true false u) (g x)) (s : Bool) :
    ∃ c : F, g (Fr.vec i s) = c • Fr.vec i s := by
  obtain ⟨η, hη, hcomm⟩ := hc
  obtain ⟨η', hη', hcomm'⟩ := hc'
  have e1 := eta_eq_one Fr hspan h2 g hg hu2 hik hη hcomm hji hjk
  have e2 := eta_eq_one Fr hspan h2 g hg hu2 hik' hη' hcomm' hji hjk'
  subst e1 e2
  simp only [one_smul] at hcomm hcomm'
  have hx : ∀ n r, (n, r) ≠ (i, !s) → polar Q (g (Fr.vec i s)) (Fr.vec n r) = 0 := by
    intro n r hnr
    by_contra hne
    have w1 : longCoroot i k true false n r + longCoroot i k true false i s = 0 := by
      by_contra h
      exact hne (polar_g_vec_eq_zero Fr g hu1 hu2 hik hcomm s n r h)
    have w2 : longCoroot i k' true false n r + longCoroot i k' true false i s = 0 := by
      by_contra h
      exact hne (polar_g_vec_eq_zero Fr g hu1 hu2 hik' hcomm' s n r h)
    by_cases hn : n = i
    · subst hn
      apply hnr
      cases r <;> cases s <;> simp [longCoroot, hik] at w1 ⊢
    · by_cases hnk : n = k
      · subst hnk
        cases r <;> cases s <;> simp [longCoroot, hik', hkk', hn] at w2
      · simp [longCoroot, hn, hnk, hik] at w1
        cases s <;> simp at w1
  exact ⟨_, eq_smul_vec_of_polar_eq_zero Fr hspan i s hx⟩

end Torus

section Diag

theorem exists_sl2_diag (h2 : (2 : F) ≠ 0) {h : Matrix (Fin 2) (Fin 2) F} {c₀ : F}
    (hc₀ : c₀ ≠ 0) (hsq : h * h = (c₀ * c₀) • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ (S : SL(2, F)) (d₁ d₂ : F), (d₁ = c₀ ∨ d₁ = -c₀) ∧ (d₂ = c₀ ∨ d₂ = -c₀) ∧
      h * (S : Matrix (Fin 2) (Fin 2) F) = (S : Matrix (Fin 2) (Fin 2) F) * !![d₁, 0; 0, d₂] := by
  have e1 := congrFun (congrFun hsq 0) 0
  have e2 := congrFun (congrFun hsq 0) 1
  have e3 := congrFun (congrFun hsq 1) 0
  have e4 := congrFun (congrFun hsq 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3 e4
  have hh : h = !![h 0 0, h 0 1; h 1 0, h 1 1] := Matrix.eta_fin_two h
  set a := h 0 0
  set b := h 0 1
  set c := h 1 0
  set d := h 1 1
  have hdet1 : ∀ x y z w : F, x * w - y * z = 1 → ((!![x, y; z, w] : Matrix (Fin 2) (Fin 2) F)).det = 1 :=
    fun x y z w h => by simpa [Matrix.det_fin_two] using h
  by_cases hs : a + d = 0
  ·
    have hd : d = -a := by linear_combination hs
    by_cases hb : b = 0
    ·
      have ha2 : a * a = c₀ * c₀ := by rw [hb] at e1; linear_combination e1
      have ha : a = c₀ ∨ a = -c₀ := mul_self_eq_mul_self_iff.mp ha2
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0] at ha2
        exact hc₀ (mul_self_eq_zero.mp (by linear_combination -ha2))
      have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha0
      refine ⟨⟨!![1, 0; c / (2 * a), 1], hdet1 _ _ _ _ (by simp)⟩, a, -a, ha, ?_, ?_⟩
      · rcases ha with ha | ha
        · right; rw [ha]
        · left; rw [ha]; ring
      · rw [hh, hd, hb]
        ext i j
        fin_cases i <;> fin_cases j
        all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
        all_goals field_simp
        all_goals ring
    ·
      have hκ : (-(2 * b * c₀)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h2 hb) hc₀)
      have hbc : a * a + b * c = c₀ * c₀ := e1
      refine ⟨⟨!![b * (-(2 * b * c₀))⁻¹, b; (c₀ - a) * (-(2 * b * c₀))⁻¹, -c₀ - a],
        hdet1 _ _ _ _ ?_⟩, c₀, -c₀, Or.inl rfl, Or.inr rfl, ?_⟩
      · field_simp
        ring
      · rw [hh, hd]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          field_simp <;> first | ring1 | linear_combination hbc | linear_combination (-1 : F) * hbc
  ·
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e2
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e3
      exact (mul_eq_zero.mp this).resolve_right hs
    have ha2 : a * a = c₀ * c₀ := by rw [hb, hc] at e1; linear_combination e1
    have hd2 : d * d = c₀ * c₀ := by rw [hb, hc] at e4; linear_combination e4
    have had : a = d := by
      rcases mul_self_eq_mul_self_iff.mp ha2 with h1 | h1 <;>
        rcases mul_self_eq_mul_self_iff.mp hd2 with h3 | h3
      · rw [h1, h3]
      · exfalso; exact hs (by rw [h1, h3]; ring)
      · exfalso; exact hs (by rw [h1, h3]; ring)
      · rw [h1, h3]
    refine ⟨1, a, a, mul_self_eq_mul_self_iff.mp ha2, mul_self_eq_mul_self_iff.mp ha2, ?_⟩
    rw [hh, hb, hc, ← had]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end Diag

section Eigenframe

variable {m : ℕ} (Fr : HypFrame Q m) {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

abbrev firstFrame : Frame Q := Fr.toFrame h01 s₀ t₀

theorem incl_firstFrame (X : Matrix (Fin 2) (Fin 2) F) :
    (firstFrame Fr h01 s₀ t₀).incl X = X 0 0 • Fr.vec i₀ s₀ + X 1 1 • Fr.vec i₀ (!s₀) +
      (-X 0 1) • Fr.vec i₁ t₀ + X 1 0 • Fr.vec i₁ (!t₀) := rfl

theorem coords_firstFrame_vec {i : Fin m} (hi0 : i ≠ i₀) (hi1 : i ≠ i₁) (r : Bool) :
    (firstFrame Fr h01 s₀ t₀).coords (Fr.vec i r) = 0 := by
  rw [Frame.coords_apply]
  have e0 : ∀ r', polar Q (Fr.vec i r) (Fr.vec i₀ r') = 0 := fun r' => by
    rw [Fr.polar_vec_of_ne hi0]
  have e1 : ∀ r', polar Q (Fr.vec i r) (Fr.vec i₁ r') = 0 := fun r' => by
    rw [Fr.polar_vec_of_ne hi1]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [firstFrame, HypFrame.toFrame, e0, e1]

theorem swap_toFrame : (Fr.toFrame h01 s₀ t₀).swap = Fr.toFrame h01 s₀ (!t₀) := by
  cases t₀ <;> rfl

theorem swap_coords_firstFrame_vec {i : Fin m} (hi0 : i ≠ i₀) (hi1 : i ≠ i₁) (r : Bool) :
    (firstFrame Fr h01 s₀ t₀).swap.coords (Fr.vec i r) = 0 := by
  rw [Frame.coords_swap, coords_firstFrame_vec Fr h01 s₀ t₀ hi0 hi1, map_zero]

theorem exists_two_others (hm : 5 ≤ m) (i₀ i₁ i : Fin m) :
    ∃ k k' : Fin m, k ≠ i₀ ∧ k ≠ i₁ ∧ k ≠ i ∧ k' ≠ i₀ ∧ k' ≠ i₁ ∧ k' ≠ i ∧ k ≠ k' := by
  classical
  have hcard : 1 < (Finset.univ \ {i₀, i₁, i}).card := by
    have h1 : (Finset.univ : Finset (Fin m)).card = m := by simp
    have h2 : ({i₀, i₁, i} : Finset (Fin m)).card ≤ 3 := by
      refine (Finset.card_insert_le _ _).trans ?_
      have := (Finset.card_insert_le i₁ ({i} : Finset (Fin m)))
      simp at this ⊢
      omega
    have h3 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin m)) {i₀, i₁, i}
    have h4 : ((Finset.univ : Finset (Fin m)) ∩ {i₀, i₁, i}).card ≤ 3 := by
      refine (Finset.card_le_card (Finset.inter_subset_right)).trans h2
    omega
  obtain ⟨k, hk, k', hk', hkk'⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hk hk'
  exact ⟨k, k', hk.1, hk.2.1, hk.2.2, hk'.1, hk'.2.1, hk'.2.2, hkk'⟩

theorem exists_eigenframe (hm : 5 ≤ m)
    (hspan : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x = 0) (h2 : (2 : F) ≠ 0)
    (g : V →ₗ[F] V) (hg : Function.Injective g) {μ : F} (hμ : ∀ x, Q (g x) = μ * Q x)
    {u : Fˣ} (hu1 : (u : F) ≠ 1) (hu2 : (u : F) ≠ -1)
    (hI1 : ∀ (A : SL(2, F)) x,
      g ((firstFrame Fr h01 s₀ t₀).La A x) = (firstFrame Fr h01 s₀ t₀).La A (g x))
    (hI2 : ∀ (i k : Fin m) (hik : i ≠ k), i ≠ i₀ → i ≠ i₁ → k ≠ i₀ → k ≠ i₁ →
      ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x,
        g (spinAction Q (Fr.longTorus hik true false u) x) =
          η • spinAction Q (Fr.longTorus hik true false u) (g x))
    (hI3 : ∀ (B : SL(2, F)) x,
      g (g ((firstFrame Fr h01 s₀ t₀).swap.La B x)) =
        (firstFrame Fr h01 s₀ t₀).swap.La B (g (g x)))
    {i₂ : Fin m} (hi20 : i₂ ≠ i₀) (hi21 : i₂ ≠ i₁)
    (hI4 : ∀ x, g (g (eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) x)) =
      eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) (g (g x))) :
    ∃ (B : SL(2, F)) (lam : Fin m → Bool → F),
      (∀ i s, (firstFrame Fr h01 s₀ t₀).swap.La B
        (g (((firstFrame Fr h01 s₀ t₀).swap.La B).symm (Fr.vec i s))) = lam i s • Fr.vec i s) ∧
      ∀ i, lam i true * lam i false = μ := by
  classical
  set fr := firstFrame Fr h01 s₀ t₀ with hfr
  obtain ⟨h, hh, -⟩ := exists_mulRight_of_commute_La fr g hI1
  have v00 : Fr.vec i₀ s₀ = fr.incl !![1, 0; 0, 0] := by rw [hfr, incl_firstFrame]; simp
  have v01 : Fr.vec i₀ (!s₀) = fr.incl !![0, 0; 0, 1] := by rw [hfr, incl_firstFrame]; simp
  have v10 : Fr.vec i₁ (!t₀) = fr.incl !![0, 0; 1, 0] := by rw [hfr, incl_firstFrame]; simp
  have v11 : Fr.vec i₁ t₀ = fr.incl !![0, -1; 0, 0] := by rw [hfr, incl_firstFrame]; simp
  have hmul : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ s, ∃ c : F, g (Fr.vec i s) = c • Fr.vec i s := by
    intro i hi0 hi1 s
    obtain ⟨k, k', hk0, hk1, hki, hk'0, hk'1, hk'i, hkk'⟩ := exists_two_others hm i₀ i₁ i
    exact exists_smul_vec_of_two_tori Fr hspan h2 g hg hu1 hu2 hki.symm hk'i.symm hkk'
      hi0.symm hk0.symm hk'0.symm (hI2 i k hki.symm hi0 hi1 hk0 hk1)
      (hI2 i k' hk'i.symm hi0 hi1 hk'0 hk'1) s
  choose! ci hci using hmul
  obtain ⟨c₁, hc₁⟩ := exists_scalar_of_commute_La_swap fr (g ∘ₗ g)
    (fun A x => by simp only [LinearMap.comp_apply]; rw [hI1, hI1])
    (fun B x => hI3 B x)
  have hsq : h * h = c₁ • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 := hc₁ 1
    simp only [LinearMap.comp_apply] at h1
    rw [hh, hh, ← map_smul] at h1
    have := fr.incl_injective h1
    simpa using this
  have hE : eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) (Fr.vec i₂ true) =
      Fr.vec i₂ true + Fr.vec i₁ (!t₀) := by
    rw [eichler_apply (Fr.map_vec i₂ false) (Fr.polar_vec_of_ne hi21 false (!t₀))]
    simp [Fr.polar_vec_vec, hi21]
  have ha : ∀ s, g (g (Fr.vec i₂ s)) = (ci i₂ s * ci i₂ s) • Fr.vec i₂ s := fun s => by
    rw [hci i₂ hi20 hi21 s, map_smul, hci i₂ hi20 hi21 s, smul_smul]
  have hc₁a : c₁ = ci i₂ true * ci i₂ true := by
    have h1 := hI4 (Fr.vec i₂ true)
    rw [hE, map_add, map_add, ha true, map_smul, hE, smul_add] at h1
    have h3 : g (g (Fr.vec i₁ (!t₀))) = (ci i₂ true * ci i₂ true) • Fr.vec i₁ (!t₀) :=
      add_left_cancel h1
    have h4 := hc₁ !![0, 0; 1, 0]
    rw [← v10] at h4
    simp only [LinearMap.comp_apply] at h4
    rw [h3] at h4
    have h5 : (ci i₂ true * ci i₂ true - c₁) • Fr.vec i₁ (!t₀) = 0 := by
      rw [sub_smul, h4, sub_self]
    exact (sub_eq_zero.mp
      ((smul_eq_zero.mp h5).resolve_right (polar_vec_ne_zero Fr i₁ (!t₀)))).symm
  have ha0 : ci i₂ true ≠ 0 := by
    intro h0
    have : g (Fr.vec i₂ true) = 0 := by rw [hci i₂ hi20 hi21 true, h0, zero_smul]
    exact polar_vec_ne_zero Fr i₂ true (hg (by rw [this, map_zero]))
  obtain ⟨S, d₁, d₂, hd₁, hd₂, hS⟩ := exists_sl2_diag h2 ha0 (by rw [hsq, hc₁a])
  let B : SL(2, F) := ⟨sigmaLin (S : Matrix (Fin 2) (Fin 2) F), by rw [det_sigmaLin]; exact S.2⟩
  have hBσ : sigmaLin (B : Matrix (Fin 2) (Fin 2) F) = (S : Matrix (Fin 2) (Fin 2) F) :=
    sigmaLin_sigmaLin _
  have hρ : ∀ Y, fr.swap.La B (fr.incl Y) = fr.incl (Y * (S : Matrix (Fin 2) (Fin 2) F)) :=
    fun Y => by rw [swap_La_incl, hBσ]
  have hρ' : ∀ Y, (fr.swap.La B).symm (fr.incl Y) =
      fr.incl (Y * ((S⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) := fun Y => by
    rw [LinearEquiv.symm_apply_eq, hρ, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  have hplane : ∀ (Y₀ : Matrix (Fin 2) (Fin 2) F) (d : F),
      Y₀ * !![d₁, 0; 0, d₂] = d • Y₀ →
        fr.swap.La B (g ((fr.swap.La B).symm (fr.incl Y₀))) = d • fr.incl Y₀ := by
    intro Y₀ d hY
    rw [hρ', hh, hρ]
    have : Y₀ * ((S⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * h * (S : Matrix (Fin 2) (Fin 2) F) =
        d • Y₀ := by
      rw [Matrix.mul_assoc _ h, hS, ← Matrix.mul_assoc, Matrix.mul_assoc Y₀,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.mul_one, hY]
    rw [this, map_smul]
  have hρiso : ∀ x, Q (fr.swap.La B x) = Q x := fun x =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (fr.swap.La_mem_orthogonalGroup B) x
  have hρfix : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ r, fr.swap.La B (Fr.vec i r) = Fr.vec i r :=
    fun i hi0 hi1 r => Frame.La_apply_of_coords_eq_zero fr.swap B
      (by rw [hfr]; exact swap_coords_firstFrame_vec Fr h01 s₀ t₀ hi0 hi1 r)
  have hex : ∀ i s, ∃ l : F, fr.swap.La B (g ((fr.swap.La B).symm (Fr.vec i s))) = l • Fr.vec i s := by
    intro i s
    by_cases hi0 : i = i₀
    · subst hi0
      rcases Bool.eq_or_eq_not s s₀ with hs | hs
      · exact ⟨d₁, by
          rw [hs, v00]
          refine hplane _ _ ?_
          ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
      · exact ⟨d₂, by
          rw [hs, v01]
          refine hplane _ _ ?_
          ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    · by_cases hi1 : i = i₁
      · subst hi1
        rcases Bool.eq_or_eq_not s t₀ with hs | hs
        · exact ⟨d₂, by
            rw [hs, v11]
            refine hplane _ _ ?_
            ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
        · exact ⟨d₁, by
            rw [hs, v10]
            refine hplane _ _ ?_
            ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
      · refine ⟨ci i s, ?_⟩
        have e1 : (fr.swap.La B).symm (Fr.vec i s) = Fr.vec i s :=
          (LinearEquiv.symm_apply_eq (fr.swap.La B)).mpr (hρfix i hi0 hi1 s).symm
        rw [e1, hci i hi0 hi1 s, map_smul, hρfix i hi0 hi1 s]
  choose lam hlam using hex
  refine ⟨B, lam, hlam, fun i => ?_⟩
  have hQsymm : ∀ x, Q ((fr.swap.La B).symm x) = Q x := fun x => by
    rw [← hρiso ((fr.swap.La B).symm x), LinearEquiv.apply_symm_apply]
  let G : V →ₗ[F] V := (fr.swap.La B).toLinearMap ∘ₗ g ∘ₗ (fr.swap.La B).symm.toLinearMap
  have hG : ∀ x, G x = fr.swap.La B (g ((fr.swap.La B).symm x)) := fun x => rfl
  have hQG : ∀ x, Q (G x) = μ * Q x := fun x => by rw [hG, hρiso, hμ, hQsymm]
  have hpG : ∀ x y, polar Q (G x) (G y) = μ * polar Q x y := fun x y => by
    simp only [QuadraticMap.polar, ← map_add, hQG, mul_sub]
  have := hpG (Fr.vec i true) (Fr.vec i false)
  rw [hG, hG, hlam, hlam, polar_smul_left, polar_smul_right] at this
  have h1 := Fr.polar_vec_not i true
  simp only [Bool.not_true] at h1
  rw [h1] at this
  simpa using this

end Eigenframe

end FrameCommutant

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
