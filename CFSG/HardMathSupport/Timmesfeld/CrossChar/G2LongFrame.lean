module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUG2

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups Matrix

abbrev G2Model (R : Type*) [CommRing R] : Type _ :=
  Matrix (Fin 3) (Fin 3) R × (Fin 3 → R) × (Fin 3 → R)

instance : DecidableEq (G2Model ℤ) :=
  inferInstanceAs (DecidableEq ((Fin 3 → Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ)))

@[expose] def g2FrameData : ℕ → G2Model ℤ
  | 0 => (Matrix.diagonal ![-1, 1, 0], 0, 0)
  | 1 => (Matrix.diagonal ![-1, 2, -1], 0, 0)
  | 2 => (Matrix.single 0 1 1, 0, 0)
  | 3 => (0, Pi.single 1 1, 0)
  | 4 => (-Matrix.single 1 0 1, 0, 0)
  | 5 => (Matrix.single 1 2 1, 0, 0)
  | 6 => (0, Pi.single 0 1, 0)
  | 7 => (0, 0, -Pi.single 1 1)
  | 8 => (Matrix.single 2 1 1, 0, 0)
  | 9 => (Matrix.single 0 2 1, 0, 0)
  | 10 => (0, 0, -Pi.single 2 1)
  | 11 => (0, 0, Pi.single 0 1)
  | 12 => (-Matrix.single 2 0 1, 0, 0)
  | 13 => (0, Pi.single 2 1, 0)
  | _ => 0

@[expose] def g2FrameSum (l : List (ℕ × ℤ)) : G2Model ℤ :=
  (l.map fun x => x.2 • g2FrameData x.1).sum

@[expose] def g2Coef1 {R : Type*} [CommRing R] (i j : Fin 3) (y : G2Model R) : G2Model R :=
  (Matrix.single i j 1 * y.1 - y.1 * Matrix.single i j 1, (Matrix.single i j 1).mulVec y.2.1,
    -(Matrix.single j i 1).mulVec y.2.2)

@[expose] def g2Coef2 {R : Type*} [CommRing R] (i j : Fin 3) (y : G2Model R) : G2Model R :=
  (-(Matrix.single i j 1 * y.1 * Matrix.single i j 1), 0, 0)

@[expose] def g2LongPos : Fin 3 → Fin 3 → ℕ
  | 0, 1 => 0
  | 0, 2 => 7
  | 1, 0 => 2
  | 1, 2 => 3
  | 2, 0 => 10
  | 2, 1 => 6
  | _, _ => 0

@[expose] def g2Weight : Fin 3 → Fin Tag.G2.rank → ℤ := ![![1, 1], ![0, 1], ![-1, -2]]

@[expose] def g2Sigma (i j : Fin 3) : Fin Tag.G2.rank → ℤ := g2Weight i - g2Weight j

set_option maxRecDepth 100000 in
theorem g2Frame_check : ∀ i j : Fin 3, i ≠ j → ∀ p < 14,
    g2FrameSum (RootOps.colOf (RootOps.entries .G2 (g2LongPos i j) 1) p) =
        g2Coef1 i j (g2FrameData p) ∧
      g2FrameSum (RootOps.colOf (RootOps.entries .G2 (g2LongPos i j) 2) p) =
        g2Coef2 i j (g2FrameData p) ∧
      g2FrameSum (RootOps.colOf (RootOps.entries .G2 (g2LongPos i j) 3) p) = 0 ∧
      ∀ k ∈ [1, 2, 3], ∀ x ∈ RootOps.colOf (RootOps.entries .G2 (g2LongPos i j) k) p, x.1 < 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem g2LongPos_spec : ∀ i j : Fin 3, i ≠ j →
    g2LongPos i j < Tag.G2.rootCertificate.roots.length ∧
      Tag.G2.rootCertificate.root (g2LongPos i j) = g2Sigma i j := by
  decide +kernel

@[expose] def g2PsiCoord {R : Type*} [CommRing R] (p : ℕ) (y : G2Model R) : R :=
  match p with
  | 0 => y.1 1 1 + 2 * y.1 2 2
  | 1 => -y.1 2 2
  | 2 => y.1 0 1
  | 3 => y.2.1 1
  | 4 => -y.1 1 0
  | 5 => y.1 1 2
  | 6 => y.2.1 0
  | 7 => -y.2.2 1
  | 8 => y.1 2 1
  | 9 => y.1 0 2
  | 10 => -y.2.2 2
  | 11 => y.2.2 0
  | 12 => -y.1 2 0
  | 13 => y.2.1 2
  | _ => 0

theorem g2PsiCoord_data : ∀ p < 14, ∀ q < 14,
    g2PsiCoord p (g2FrameData q) = if p = q then 1 else 0 := by
  decide +kernel

theorem trace_g2FrameData : ∀ q < 14, Matrix.trace (g2FrameData q).1 = 0 := by
  decide +kernel

section Field

variable {L : Type} [Field L]

@[expose] def g2Cast (x : G2Model ℤ) : G2Model L :=
  (x.1.map (Int.castRingHom L), fun k => (x.2.1 k : L), fun k => (x.2.2 k : L))

theorem g2Cast_add (x y : G2Model ℤ) : (g2Cast (x + y) : G2Model L) = g2Cast x + g2Cast y := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext r s
    simp [g2Cast]
  · funext k
    simp [g2Cast]
  · funext k
    simp [g2Cast]

theorem g2Cast_zero : (g2Cast 0 : G2Model L) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext r s
    simp [g2Cast]
  · funext k
    simp [g2Cast]
  · funext k
    simp [g2Cast]

theorem g2Cast_zsmul (z : ℤ) (x : G2Model ℤ) :
    (g2Cast (z • x) : G2Model L) = (z : L) • g2Cast x := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext r s
    change (Int.castRingHom L) (z * x.1 r s) = (z : L) * (Int.castRingHom L) (x.1 r s)
    rw [map_mul, eq_intCast]
  · funext k
    simp [g2Cast]
  · funext k
    simp [g2Cast]

theorem g2Cast_coef1 (i j : Fin 3) (x : G2Model ℤ) :
    (g2Cast (g2Coef1 i j x) : G2Model L) = g2Coef1 i j (g2Cast x) := by
  have hE : ∀ a b : Fin 3, (Matrix.single a b (1 : ℤ)).map (Int.castRingHom L) =
      Matrix.single a b 1 := fun a b => by rw [Matrix.map_single, map_one]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (Matrix.single i j 1 * x.1 - x.1 * Matrix.single i j 1).map (Int.castRingHom L) = _
    rw [Matrix.map_sub _ (map_sub (Int.castRingHom L)), Matrix.map_mul, Matrix.map_mul, hE]
    rfl
  · funext k
    change (Int.castRingHom L) ((Matrix.single i j 1).mulVec x.2.1 k) = _
    rw [RingHom.map_mulVec, hE]
    rfl
  · funext k
    change (Int.castRingHom L) (-(Matrix.single j i 1).mulVec x.2.2 k) = _
    rw [map_neg, RingHom.map_mulVec, hE]
    rfl

theorem g2Cast_coef2 (i j : Fin 3) (x : G2Model ℤ) :
    (g2Cast (g2Coef2 i j x) : G2Model L) = g2Coef2 i j (g2Cast x) := by
  have hE : ∀ a b : Fin 3, (Matrix.single a b (1 : ℤ)).map (Int.castRingHom L) =
      Matrix.single a b 1 := fun a b => by rw [Matrix.map_single, map_one]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (-(Matrix.single i j 1 * x.1 * Matrix.single i j 1)).map (Int.castRingHom L) = _
    rw [Matrix.map_neg _ (map_neg (Int.castRingHom L)), Matrix.map_mul, Matrix.map_mul, hE]
    rfl
  · funext k
    simp [g2Cast, g2Coef2]
  · funext k
    simp [g2Cast, g2Coef2]

theorem g2PsiCoord_cast (p : ℕ) (x : G2Model ℤ) :
    g2PsiCoord p (g2Cast x : G2Model L) = ((g2PsiCoord p x : ℤ) : L) := by
  rcases p with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | p <;>
    simp [g2PsiCoord, g2Cast]

theorem dim_G2 : RootOps.dim Tag.G2 = 14 := by decide

@[expose] def g2FramePhi : RootModule Tag.G2 L →ₗ[L] G2Model L :=
  ∑ p ∈ Finset.range 14, (RootOps.posCoord Tag.G2 L p).smulRight (g2Cast (g2FrameData p))

theorem g2FramePhi_posVec {q : ℕ} (hq : q < 14) :
    g2FramePhi (RootOps.posVec Tag.G2 L q) = g2Cast (g2FrameData q) := by
  have hq' : q < RootOps.dim Tag.G2 := by rw [dim_G2]; exact hq
  simp only [g2FramePhi, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rw [Finset.sum_eq_single q (fun p _ hp => by
      rw [RootOps.posCoord_posVec hq', ite_eq_right hp, zero_smul])
    (fun h => absurd (Finset.mem_range.2 hq) h), RootOps.posCoord_posVec hq', ite_eq_left rfl,
    one_smul]

theorem g2FramePhi_vecOf (l : List (ℕ × ℤ)) (hl : ∀ x ∈ l, x.1 < 14) :
    g2FramePhi (RootOps.vecOf Tag.G2 L l) = g2Cast (g2FrameSum l) := by
  induction l with
  | nil =>
    rw [RootOps.vecOf_nil, map_zero]
    exact g2Cast_zero.symm
  | cons x l ih =>
    rw [RootOps.vecOf_cons, map_add, map_smul, g2FramePhi_posVec (hl x List.mem_cons_self),
      ih fun y hy => hl y (List.mem_cons_of_mem _ hy)]
    simp only [g2FrameSum, List.map_cons, List.sum_cons]
    rw [g2Cast_add, g2Cast_zsmul]

@[expose] def g2PsiCoordL (p : ℕ) : G2Model L →ₗ[L] L where
  toFun := g2PsiCoord p
  map_add' y y' := by
    rcases p with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | p <;>
      (simp [g2PsiCoord]; try ring)
  map_smul' c y := by
    rcases p with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | p <;>
      (simp [g2PsiCoord]; try ring)

@[expose] def g2FramePsi : G2Model L →ₗ[L] RootModule Tag.G2 L :=
  ∑ p ∈ Finset.range 14, (g2PsiCoordL p).smulRight (RootOps.posVec Tag.G2 L p)

theorem g2FramePsi_cast {q : ℕ} (hq : q < 14) :
    g2FramePsi (g2Cast (g2FrameData q) : G2Model L) = RootOps.posVec Tag.G2 L q := by
  simp only [g2FramePsi, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rw [Finset.sum_eq_single q (fun p hp hpq => by
      change g2PsiCoord p (g2Cast (g2FrameData q)) • _ = _
      rw [g2PsiCoord_cast, g2PsiCoord_data p (Finset.mem_range.1 hp) q hq, ite_eq_right hpq,
        Int.cast_zero, zero_smul])
    (fun h => absurd (Finset.mem_range.2 hq) h)]
  change g2PsiCoord q (g2Cast (g2FrameData q)) • _ = _
  rw [g2PsiCoord_cast, g2PsiCoord_data q hq q hq, ite_eq_left rfl, Int.cast_one, one_smul]

theorem ext_posVec_G2 {M : Type*} [AddCommGroup M] [Module L M]
    {f g : RootModule Tag.G2 L →ₗ[L] M}
    (h : ∀ p, p < 14 → f (RootOps.posVec Tag.G2 L p) = g (RootOps.posVec Tag.G2 L p)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  obtain ⟨p, hp, rfl⟩ := RootOps.posLabel_surjective b
  have hp' : p < 14 := by rw [← dim_G2]; exact hp
  simpa [RootOps.posVec_eq_single hp] using h p hp'

theorem g2FramePsi_phi (x : RootModule Tag.G2 L) : g2FramePsi (g2FramePhi x) = x := by
  have h : g2FramePsi ∘ₗ g2FramePhi = (LinearMap.id : Module.End L (RootModule Tag.G2 L)) :=
    ext_posVec_G2 fun p hp => by
      rw [LinearMap.comp_apply, g2FramePhi_posVec hp, g2FramePsi_cast hp, LinearMap.id_apply]
  exact congrArg (fun f => f x) h

theorem trace_g2FramePhi (x : RootModule Tag.G2 L) : Matrix.trace (g2FramePhi x).1 = 0 := by
  have h : (Matrix.traceLinearMap (Fin 3) L L ∘ₗ LinearMap.fst L _ _) ∘ₗ g2FramePhi = 0 :=
    ext_posVec_G2 fun p hp => by
      rw [LinearMap.comp_apply, g2FramePhi_posVec hp, LinearMap.zero_apply]
      change Matrix.trace ((g2FrameData p).1.map (Int.castRingHom L)) = 0
      have h0 := trace_g2FrameData p hp
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply] at h0 ⊢
      rw [← map_sum, h0, map_zero]
  exact congrArg (fun f => f x) h

theorem g2FramePhi_psi (y : G2Model L) (hy : Matrix.trace y.1 = 0) :
    g2FramePhi (g2FramePsi y) = y := by
  have h1 : g2FramePsi y =
      ∑ p ∈ Finset.range 14, g2PsiCoord p y • RootOps.posVec Tag.G2 L p := by
    simp only [g2FramePsi, LinearMap.sum_apply, LinearMap.smulRight_apply]
    rfl
  rw [h1, map_sum]
  rw [Finset.sum_congr rfl fun p hp => by
    rw [map_smul, g2FramePhi_posVec (Finset.mem_range.1 hp)]]
  obtain ⟨m, v, w⟩ := y
  rw [Matrix.trace_fin_three] at hy
  simp only at hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext r s
    fin_cases r <;> fin_cases s <;>
      simp [g2PsiCoord, g2Cast, g2FrameData, Matrix.diagonal, Matrix.single] <;>
      first | ring1 | linear_combination hy | linear_combination -hy
  · funext k
    fin_cases k <;> simp [g2PsiCoord, g2Cast, g2FrameData, Pi.single_apply]
  · funext k
    fin_cases k <;> simp [g2PsiCoord, g2Cast, g2FrameData, Pi.single_apply]

@[expose] def g2Rho (X : SL(3, L)) : Module.End L (G2Model L) :=
  ((LinearMap.mulLeft L (X : Matrix (Fin 3) (Fin 3) L)).comp
      (LinearMap.mulRight L ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L))).prodMap
    ((Matrix.mulVecLin (X : Matrix (Fin 3) (Fin 3) L)).prodMap
      (Matrix.mulVecLin ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)ᵀ))

theorem g2Rho_apply (X : SL(3, L)) (y : G2Model L) :
    g2Rho X y = ((X : Matrix (Fin 3) (Fin 3) L) * y.1 *
        ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L),
      (X : Matrix (Fin 3) (Fin 3) L) *ᵥ y.2.1,
      ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)ᵀ *ᵥ y.2.2) := by
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  change (X : Matrix (Fin 3) (Fin 3) L) * (y.1 * ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)) = _
  rw [mul_assoc]

theorem g2Rho_mul (X Y : SL(3, L)) : g2Rho (X * Y) = g2Rho X * g2Rho Y := by
  refine LinearMap.ext fun y => ?_
  rw [Module.End.mul_apply, g2Rho_apply, g2Rho_apply, g2Rho_apply, mul_inv_rev]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec, Matrix.transpose_mul,
    mul_assoc]

theorem g2Rho_one : g2Rho (1 : SL(3, L)) = 1 := by
  refine LinearMap.ext fun y => ?_
  rw [g2Rho_apply, inv_one]
  simp

theorem trace_g2Rho (X : SL(3, L)) (y : G2Model L) :
    Matrix.trace (g2Rho X y).1 = Matrix.trace y.1 := by
  rw [g2Rho_apply]
  change Matrix.trace ((X : Matrix (Fin 3) (Fin 3) L) * y.1 *
    ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)) = _
  rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mul]

@[expose] def g2FrameEnd (X : SL(3, L)) : Module.End L (RootModule Tag.G2 L) :=
  g2FramePsi ∘ₗ g2Rho X ∘ₗ g2FramePhi

theorem g2FrameEnd_apply (X : SL(3, L)) (x : RootModule Tag.G2 L) :
    g2FrameEnd X x = g2FramePsi (g2Rho X (g2FramePhi x)) := by
  simp only [g2FrameEnd, LinearMap.comp_apply]

theorem g2FrameEnd_one : g2FrameEnd (1 : SL(3, L)) = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [g2FrameEnd_apply, g2Rho_one, Module.End.one_apply, g2FramePsi_phi, Module.End.one_apply]

theorem g2FrameEnd_mul (X Y : SL(3, L)) : g2FrameEnd (X * Y) = g2FrameEnd X * g2FrameEnd Y := by
  refine LinearMap.ext fun x => ?_
  have htr : Matrix.trace (g2Rho Y (g2FramePhi x)).1 = 0 := by
    rw [trace_g2Rho]
    exact trace_g2FramePhi x
  rw [Module.End.mul_apply, g2FrameEnd_apply, g2FrameEnd_apply, g2FrameEnd_apply,
    g2FramePhi_psi _ htr, g2Rho_mul, Module.End.mul_apply]

@[expose] def g2FrameHom : SL(3, L) →* Module.End L (RootModule Tag.G2 L) where
  toFun := g2FrameEnd
  map_one' := g2FrameEnd_one
  map_mul' := g2FrameEnd_mul

variable (L) in
@[expose] def g2Frame : SL(3, L) →* ModGL Tag.G2 L :=
  (Units.map g2FrameHom).comp (toUnits : SL(3, L) ≃* (SL(3, L))ˣ).toMonoidHom

theorem coe_g2Frame (X : SL(3, L)) :
    ((g2Frame L X : ModGL Tag.G2 L) : Module.End L (RootModule Tag.G2 L)) = g2FrameEnd X :=
  rfl

theorem g2Rho_transvection {i j : Fin 3} (hij : i ≠ j) (t : L) (y : G2Model L) :
    g2Rho (Matrix.SpecialLinearGroup.transvection hij t) y =
      y + t • g2Coef1 i j y + t ^ 2 • g2Coef2 i j y := by
  rw [g2Rho_apply, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  have e1 : Matrix.single i j t = t • Matrix.single i j (1 : L) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have e2 : Matrix.single i j (-t) = (-t) • Matrix.single i j (1 : L) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  obtain ⟨m, v, w⟩ := y
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (1 + Matrix.single i j t) * m * (1 + Matrix.single i j (-t)) =
      m + t • (Matrix.single i j 1 * m - m * Matrix.single i j 1) +
        t ^ 2 • (-(Matrix.single i j 1 * m * Matrix.single i j 1))
    rw [e1, e2]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, Matrix.mul_smul, smul_sub,
      smul_neg, smul_smul]
    module
  · change (1 + Matrix.single i j t) *ᵥ v = v + t • (Matrix.single i j 1 *ᵥ v) + t ^ 2 • 0
    rw [e1, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, smul_zero, add_zero]
  · change (1 + Matrix.single i j (-t))ᵀ *ᵥ w = w + t • (-(Matrix.single j i 1 *ᵥ w)) + t ^ 2 • 0
    rw [e2, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
      Matrix.transpose_single, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      smul_zero, add_zero, smul_neg, neg_smul]

end Field

section Frame

variable
  {L : Type} [Field L]

theorem isRoot_g2Sigma {i j : Fin 3} (hij : i ≠ j) : IsRoot Tag.G2 (g2Sigma i j) := by
  have h := g2LongPos_spec i j hij
  rw [← h.2]
  exact CFSG.LieType.Chevalley.RootWalk.isRoot_rootCertificate_root h.1

theorem g2FramePhi_elt {i j : Fin 3} (hij : i ≠ j) (t : L) :
    g2FramePhi ∘ₗ (rootOperatorFamily Tag.G2).elt L ⟨g2Sigma i j, isRoot_g2Sigma hij⟩ t =
      g2Rho (Matrix.SpecialLinearGroup.transvection hij t) ∘ₗ g2FramePhi := by
  have hpos : RootOps.rootPos (⟨g2Sigma i j, isRoot_g2Sigma hij⟩ : Root Tag.G2) = g2LongPos i j :=
    RootOps.rootPos_eq (g2LongPos_spec i j hij).1 (g2LongPos_spec i j hij).2
  refine ext_posVec_G2 fun p hp => ?_
  have hp' : p < RootOps.dim Tag.G2 := by rw [dim_G2]; exact hp
  obtain ⟨c1, c2, c3, hval⟩ := g2Frame_check i j hij p hp
  have hD : ∀ k, 1 ≤ k → k ≤ 3 →
      (rootOperatorFamily Tag.G2).D L ⟨g2Sigma i j, isRoot_g2Sigma hij⟩ k
        (RootOps.posVec Tag.G2 L p) =
      RootOps.vecOf Tag.G2 L (RootOps.colOf (RootOps.entries .G2 (g2LongPos i j) k) p) := by
    intro k hk1 hk3
    change RootOps.dataD Tag.G2 L _ k _ = _
    rw [RootOps.dataD, ite_eq_right (by omega), ite_eq_left hk3, hpos,
      RootOps.entriesOp_posVec _ hp']
  have hD0 : (rootOperatorFamily Tag.G2).D L ⟨g2Sigma i j, isRoot_g2Sigma hij⟩ 0 = 1 :=
    (rootOperatorFamily Tag.G2).D_zero L _
  rw [LinearMap.comp_apply, LinearMap.comp_apply, g2FramePhi_posVec hp, g2Rho_transvection,
    RootOperatorFamily.elt]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hD0, pow_zero, one_smul,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [hD 1 le_rfl (by norm_num), hD 2 (by norm_num) (by norm_num), hD 3 (by norm_num) le_rfl]
  simp only [map_add, map_smul, g2FramePhi_posVec hp]
  rw [g2FramePhi_vecOf _ (hval 1 (by simp)), g2FramePhi_vecOf _ (hval 2 (by simp)),
    g2FramePhi_vecOf _ (hval 3 (by simp)), c1, c2, c3, g2Cast_coef1, g2Cast_coef2, g2Cast_zero,
    smul_zero, add_zero, pow_one]

theorem g2Frame_transvection {i j : Fin 3} (hij : i ≠ j) (t : L) :
    g2Frame L (Matrix.SpecialLinearGroup.transvection hij t) =
      (rootOperatorFamily Tag.G2).eltUnit L ⟨g2Sigma i j, isRoot_g2Sigma hij⟩ t := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [coe_g2Frame, RootOperatorFamily.coe_eltUnit, g2FrameEnd_apply]
  have h := LinearMap.congr_fun (g2FramePhi_elt hij t) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [← h, g2FramePsi_phi]

theorem g2Frame_transvection_pinned {i j : Fin 3} (hij : i ≠ j) (t : L) :
    g2Frame L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.G2 L (g2Sigma i j)
        (((rootOperatorFamily Tag.G2).pinnedFamilySign (g2Sigma i j) : L) * t) := by
  rw [(rootOperatorFamily Tag.G2).pinnedX_eq_eltUnit L (isRoot_g2Sigma hij), ← mul_assoc,
    (rootOperatorFamily Tag.G2).pinnedFamilySign_mul_self L, one_mul, g2Frame_transvection]

theorem g2Sigma_neg (i j : Fin 3) : g2Sigma j i = -g2Sigma i j := by
  simp only [g2Sigma, neg_sub]

theorem g2Sigma_add (i j k : Fin 3) : g2Sigma i j + g2Sigma j k = g2Sigma i k := by
  simp only [g2Sigma, sub_add_sub_cancel]

theorem g2Frame_isSLFrame : IsSLFrame (g2Frame L) g2Sigma where
  isRoot i j hij := isRoot_g2Sigma hij
  neg := g2Sigma_neg
  add := g2Sigma_add
  transv i j hij := by
    have hs := (rootOperatorFamily Tag.G2).pinnedFamilySign_mul_self L (g2Sigma i j)
    refine ⟨Units.mk0 _ (left_ne_zero_of_mul_eq_one hs), fun t => ?_⟩
    rw [Units.val_mk0, g2Frame_transvection_pinned]
  range := by
    have hs : ∀ i j : Fin 3, ((rootOperatorFamily Tag.G2).pinnedFamilySign (g2Sigma i j) : L) *
        ((rootOperatorFamily Tag.G2).pinnedFamilySign (g2Sigma i j) : L) = 1 := fun i j =>
      (rootOperatorFamily Tag.G2).pinnedFamilySign_mul_self L _
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation,
        MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨X, ⟨i, j, hij, c, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, g2Frame_transvection_pinned]
      exact (le_iSup₂ (f := fun α (_ : α ∈ frameRoots g2Sigma) => rootSubgroup Tag.G2 L α)
        (g2Sigma i j) ⟨i, j, hij, rfl⟩) (Subgroup.subset_closure ⟨_, rfl⟩)
    · refine iSup₂_le fun α hα => ?_
      obtain ⟨i, j, hij, rfl⟩ := hα
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      refine ⟨Matrix.SpecialLinearGroup.transvection hij
        (((rootOperatorFamily Tag.G2).pinnedFamilySign (g2Sigma i j) : L) * c), ?_⟩
      rw [g2Frame_transvection_pinned, ← mul_assoc, hs, one_mul]

set_option maxRecDepth 100000 in
theorem g2Sigma_long : ∀ i j : Fin 3, i ≠ j → iform (g2Sigma i j) (g2Sigma i j) = 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem g2_long_sigma : ∀ l ∈ Tag.G2.artifactRoots,
    iform (toVec Tag.G2.rank l) (toVec Tag.G2.rank l) = 6 →
      ∃ i j : Fin 3, i ≠ j ∧ toVec Tag.G2.rank l = g2Sigma i j := by
  decide +kernel

theorem frameRoots_g2Sigma : frameRoots g2Sigma = g2LongRoots := by
  ext γ
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨isRoot_g2Sigma hij, g2Sigma_long i j hij⟩
  · rintro ⟨hγ, h6⟩
    have hmem := isRoot_iff_mem_artifactRoots.1 hγ
    obtain ⟨i, j, hij, h⟩ := g2_long_sigma _ hmem (by rw [toVec_ofFn_G2]; exact h6)
    rw [toVec_ofFn_G2] at h
    exact ⟨i, j, hij, h⟩

end Frame

theorem g2LongA2Frame_proved :
    G2LongA2Frame :=
  fun L _ _ => ⟨g2Frame L, g2Sigma, g2Frame_isSLFrame, frameRoots_g2Sigma⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
