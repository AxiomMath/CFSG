module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks
public import CFSG.HardMathSupport.Timmesfeld.Torality.A2Block
public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2
public import CFSG.RankThree.Lattice.SteinbergBIRoots
public import CFSG.Timmesfeld.RankTwo.ModelG2Comm

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section G2Long

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups Matrix

abbrev G2LModel (R : Type*) [CommRing R] : Type _ :=
  Matrix (Fin 3) (Fin 3) R × (Fin 3 → R) × (Fin 3 → R)

instance : DecidableEq (G2LModel ℤ) :=
  inferInstanceAs (DecidableEq ((Fin 3 → Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ)))

@[expose] def g2LData : ℕ → G2LModel ℤ
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

@[expose] def g2LSum (l : List (ℕ × ℤ)) : G2LModel ℤ :=
  (l.map fun x => x.2 • g2LData x.1).sum

@[expose] def g2LCoef1 {R : Type*} [CommRing R] (i j : Fin 3) (y : G2LModel R) : G2LModel R :=
  (Matrix.single i j 1 * y.1 - y.1 * Matrix.single i j 1, (Matrix.single i j 1).mulVec y.2.1,
    -(Matrix.single j i 1).mulVec y.2.2)

@[expose] def g2LCoef2 {R : Type*} [CommRing R] (i j : Fin 3) (y : G2LModel R) : G2LModel R :=
  (-(Matrix.single i j 1 * y.1 * Matrix.single i j 1), 0, 0)

@[expose] def g2LPos : Fin 3 → Fin 3 → ℕ
  | 0, 1 => 0
  | 0, 2 => 7
  | 1, 0 => 2
  | 1, 2 => 3
  | 2, 0 => 10
  | 2, 1 => 6
  | _, _ => 0

@[expose] def g2LWeight : Fin 3 → Fin Tag.G2.rank → ℤ := ![![1, 1], ![0, 1], ![-1, -2]]

@[expose] def g2LSigma (i j : Fin 3) : Fin Tag.G2.rank → ℤ := g2LWeight i - g2LWeight j

set_option maxRecDepth 100000 in
theorem g2L_check : ∀ i j : Fin 3, i ≠ j → ∀ p < 14,
    g2LSum (RootOps.colOf (RootOps.entries .G2 (g2LPos i j) 1) p) =
        g2LCoef1 i j (g2LData p) ∧
      g2LSum (RootOps.colOf (RootOps.entries .G2 (g2LPos i j) 2) p) =
        g2LCoef2 i j (g2LData p) ∧
      g2LSum (RootOps.colOf (RootOps.entries .G2 (g2LPos i j) 3) p) = 0 ∧
      ∀ k ∈ [1, 2, 3], ∀ x ∈ RootOps.colOf (RootOps.entries .G2 (g2LPos i j) k) p, x.1 < 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem g2LPos_spec : ∀ i j : Fin 3, i ≠ j →
    g2LPos i j < Tag.G2.rootCertificate.roots.length ∧
      Tag.G2.rootCertificate.root (g2LPos i j) = g2LSigma i j := by
  decide +kernel

@[expose] def g2LPsiCoord {R : Type*} [CommRing R] (p : ℕ) (y : G2LModel R) : R :=
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

theorem g2LPsiCoord_data : ∀ p < 14, ∀ q < 14,
    g2LPsiCoord p (g2LData q) = if p = q then 1 else 0 := by
  decide +kernel

theorem trace_g2LData : ∀ q < 14, Matrix.trace (g2LData q).1 = 0 := by
  decide +kernel

section Field

variable {L : Type} [Field L]

@[expose] def g2LCast (x : G2LModel ℤ) : G2LModel L :=
  (x.1.map (Int.castRingHom L), fun k => (x.2.1 k : L), fun k => (x.2.2 k : L))

theorem g2LCast_add (x y : G2LModel ℤ) :
    (g2LCast (x + y) : G2LModel L) = g2LCast x + g2LCast y := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext r s
    simp [g2LCast]
  · funext k
    simp [g2LCast]
  · funext k
    simp [g2LCast]

theorem g2LCast_zero : (g2LCast 0 : G2LModel L) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext r s
    simp [g2LCast]
  · funext k
    simp [g2LCast]
  · funext k
    simp [g2LCast]

theorem g2LCast_zsmul (z : ℤ) (x : G2LModel ℤ) :
    (g2LCast (z • x) : G2LModel L) = (z : L) • g2LCast x := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext r s
    change (Int.castRingHom L) (z * x.1 r s) = (z : L) * (Int.castRingHom L) (x.1 r s)
    rw [map_mul, eq_intCast]
  · funext k
    simp [g2LCast]
  · funext k
    simp [g2LCast]

theorem g2LCast_coef1 (i j : Fin 3) (x : G2LModel ℤ) :
    (g2LCast (g2LCoef1 i j x) : G2LModel L) = g2LCoef1 i j (g2LCast x) := by
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

theorem g2LCast_coef2 (i j : Fin 3) (x : G2LModel ℤ) :
    (g2LCast (g2LCoef2 i j x) : G2LModel L) = g2LCoef2 i j (g2LCast x) := by
  have hE : ∀ a b : Fin 3, (Matrix.single a b (1 : ℤ)).map (Int.castRingHom L) =
      Matrix.single a b 1 := fun a b => by rw [Matrix.map_single, map_one]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (-(Matrix.single i j 1 * x.1 * Matrix.single i j 1)).map (Int.castRingHom L) = _
    rw [Matrix.map_neg _ (map_neg (Int.castRingHom L)), Matrix.map_mul, Matrix.map_mul, hE]
    rfl
  · funext k
    simp [g2LCast, g2LCoef2]
  · funext k
    simp [g2LCast, g2LCoef2]

theorem g2LPsiCoord_cast (p : ℕ) (x : G2LModel ℤ) :
    g2LPsiCoord p (g2LCast x : G2LModel L) = ((g2LPsiCoord p x : ℤ) : L) := by
  rcases p with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | p <;>
    simp [g2LPsiCoord, g2LCast]

theorem dim_G2L : RootOps.dim Tag.G2 = 14 := by decide

@[expose] def g2LPhi : RootModule Tag.G2 L →ₗ[L] G2LModel L :=
  ∑ p ∈ Finset.range 14, (RootOps.posCoord Tag.G2 L p).smulRight (g2LCast (g2LData p))

theorem g2LPhi_posVec {q : ℕ} (hq : q < 14) :
    g2LPhi (RootOps.posVec Tag.G2 L q) = g2LCast (g2LData q) := by
  have hq' : q < RootOps.dim Tag.G2 := by rw [dim_G2L]; exact hq
  simp only [g2LPhi, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rw [Finset.sum_eq_single q (fun p _ hp => by
      rw [RootOps.posCoord_posVec hq', ite_eq_right hp, zero_smul])
    (fun h => absurd (Finset.mem_range.2 hq) h), RootOps.posCoord_posVec hq', ite_eq_left rfl,
    one_smul]

theorem g2LPhi_vecOf (l : List (ℕ × ℤ)) (hl : ∀ x ∈ l, x.1 < 14) :
    g2LPhi (RootOps.vecOf Tag.G2 L l) = g2LCast (g2LSum l) := by
  induction l with
  | nil =>
    rw [RootOps.vecOf_nil, map_zero]
    exact g2LCast_zero.symm
  | cons x l ih =>
    rw [RootOps.vecOf_cons, map_add, map_smul, g2LPhi_posVec (hl x List.mem_cons_self),
      ih fun y hy => hl y (List.mem_cons_of_mem _ hy)]
    simp only [g2LSum, List.map_cons, List.sum_cons]
    rw [g2LCast_add, g2LCast_zsmul]

@[expose] def g2LPsiCoordL (p : ℕ) : G2LModel L →ₗ[L] L where
  toFun := g2LPsiCoord p
  map_add' y y' := by
    rcases p with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | p <;>
      (simp [g2LPsiCoord]; try ring)
  map_smul' c y := by
    rcases p with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | p <;>
      (simp [g2LPsiCoord]; try ring)

@[expose] def g2LPsi : G2LModel L →ₗ[L] RootModule Tag.G2 L :=
  ∑ p ∈ Finset.range 14, (g2LPsiCoordL p).smulRight (RootOps.posVec Tag.G2 L p)

theorem g2LPsi_cast {q : ℕ} (hq : q < 14) :
    g2LPsi (g2LCast (g2LData q) : G2LModel L) = RootOps.posVec Tag.G2 L q := by
  simp only [g2LPsi, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rw [Finset.sum_eq_single q (fun p hp hpq => by
      change g2LPsiCoord p (g2LCast (g2LData q)) • _ = _
      rw [g2LPsiCoord_cast, g2LPsiCoord_data p (Finset.mem_range.1 hp) q hq, ite_eq_right hpq,
        Int.cast_zero, zero_smul])
    (fun h => absurd (Finset.mem_range.2 hq) h)]
  change g2LPsiCoord q (g2LCast (g2LData q)) • _ = _
  rw [g2LPsiCoord_cast, g2LPsiCoord_data q hq q hq, ite_eq_left rfl, Int.cast_one, one_smul]

theorem ext_posVec_G2L {M : Type*} [AddCommGroup M] [Module L M]
    {f g : RootModule Tag.G2 L →ₗ[L] M}
    (h : ∀ p, p < 14 → f (RootOps.posVec Tag.G2 L p) = g (RootOps.posVec Tag.G2 L p)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  obtain ⟨p, hp, rfl⟩ := RootOps.posLabel_surjective b
  have hp' : p < 14 := by rw [← dim_G2L]; exact hp
  simpa [RootOps.posVec_eq_single hp] using h p hp'

theorem g2LPsi_phi (x : RootModule Tag.G2 L) : g2LPsi (g2LPhi x) = x := by
  have h : g2LPsi ∘ₗ g2LPhi = (LinearMap.id : Module.End L (RootModule Tag.G2 L)) :=
    ext_posVec_G2L fun p hp => by
      rw [LinearMap.comp_apply, g2LPhi_posVec hp, g2LPsi_cast hp, LinearMap.id_apply]
  exact congrArg (fun f => f x) h

theorem trace_g2LPhi (x : RootModule Tag.G2 L) : Matrix.trace (g2LPhi x).1 = 0 := by
  have h : (Matrix.traceLinearMap (Fin 3) L L ∘ₗ LinearMap.fst L _ _) ∘ₗ g2LPhi = 0 :=
    ext_posVec_G2L fun p hp => by
      rw [LinearMap.comp_apply, g2LPhi_posVec hp, LinearMap.zero_apply]
      change Matrix.trace ((g2LData p).1.map (Int.castRingHom L)) = 0
      have h0 := trace_g2LData p hp
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply] at h0 ⊢
      rw [← map_sum, h0, map_zero]
  exact congrArg (fun f => f x) h

theorem g2LPhi_psi (y : G2LModel L) (hy : Matrix.trace y.1 = 0) :
    g2LPhi (g2LPsi y) = y := by
  have h1 : g2LPsi y =
      ∑ p ∈ Finset.range 14, g2LPsiCoord p y • RootOps.posVec Tag.G2 L p := by
    simp only [g2LPsi, LinearMap.sum_apply, LinearMap.smulRight_apply]
    rfl
  rw [h1, map_sum]
  rw [Finset.sum_congr rfl fun p hp => by
    rw [map_smul, g2LPhi_posVec (Finset.mem_range.1 hp)]]
  obtain ⟨m, v, w⟩ := y
  rw [Matrix.trace_fin_three] at hy
  simp only at hy
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext r s
    fin_cases r <;> fin_cases s <;>
      simp [g2LPsiCoord, g2LCast, g2LData, Matrix.diagonal, Matrix.single] <;>
      first | ring1 | linear_combination hy | linear_combination -hy
  · funext k
    fin_cases k <;> simp [g2LPsiCoord, g2LCast, g2LData, Pi.single_apply]
  · funext k
    fin_cases k <;> simp [g2LPsiCoord, g2LCast, g2LData, Pi.single_apply]

@[expose] def g2LRho (X : SL(3, L)) : Module.End L (G2LModel L) :=
  ((LinearMap.mulLeft L (X : Matrix (Fin 3) (Fin 3) L)).comp
      (LinearMap.mulRight L ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L))).prodMap
    ((Matrix.mulVecLin (X : Matrix (Fin 3) (Fin 3) L)).prodMap
      (Matrix.mulVecLin ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)ᵀ))

theorem g2LRho_apply (X : SL(3, L)) (y : G2LModel L) :
    g2LRho X y = ((X : Matrix (Fin 3) (Fin 3) L) * y.1 *
        ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L),
      (X : Matrix (Fin 3) (Fin 3) L) *ᵥ y.2.1,
      ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)ᵀ *ᵥ y.2.2) := by
  refine Prod.ext ?_ (Prod.ext rfl rfl)
  change (X : Matrix (Fin 3) (Fin 3) L) * (y.1 * ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)) = _
  rw [mul_assoc]

theorem g2LRho_mul (X Y : SL(3, L)) : g2LRho (X * Y) = g2LRho X * g2LRho Y := by
  refine LinearMap.ext fun y => ?_
  rw [Module.End.mul_apply, g2LRho_apply, g2LRho_apply, g2LRho_apply, mul_inv_rev]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec, Matrix.transpose_mul,
    mul_assoc]

theorem g2LRho_one : g2LRho (1 : SL(3, L)) = 1 := by
  refine LinearMap.ext fun y => ?_
  rw [g2LRho_apply, inv_one]
  simp

theorem trace_g2LRho (X : SL(3, L)) (y : G2LModel L) :
    Matrix.trace (g2LRho X y).1 = Matrix.trace y.1 := by
  rw [g2LRho_apply]
  change Matrix.trace ((X : Matrix (Fin 3) (Fin 3) L) * y.1 *
    ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)) = _
  rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mul]

@[expose] def g2LEnd (X : SL(3, L)) : Module.End L (RootModule Tag.G2 L) :=
  g2LPsi ∘ₗ g2LRho X ∘ₗ g2LPhi

theorem g2LEnd_apply (X : SL(3, L)) (x : RootModule Tag.G2 L) :
    g2LEnd X x = g2LPsi (g2LRho X (g2LPhi x)) := by
  simp only [g2LEnd, LinearMap.comp_apply]

theorem g2LEnd_one : g2LEnd (1 : SL(3, L)) = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [g2LEnd_apply, g2LRho_one, Module.End.one_apply, g2LPsi_phi, Module.End.one_apply]

theorem g2LEnd_mul (X Y : SL(3, L)) : g2LEnd (X * Y) = g2LEnd X * g2LEnd Y := by
  refine LinearMap.ext fun x => ?_
  have htr : Matrix.trace (g2LRho Y (g2LPhi x)).1 = 0 := by
    rw [trace_g2LRho]
    exact trace_g2LPhi x
  rw [Module.End.mul_apply, g2LEnd_apply, g2LEnd_apply, g2LEnd_apply,
    g2LPhi_psi _ htr, g2LRho_mul, Module.End.mul_apply]

@[expose] def g2LHom : SL(3, L) →* Module.End L (RootModule Tag.G2 L) where
  toFun := g2LEnd
  map_one' := g2LEnd_one
  map_mul' := g2LEnd_mul

variable (L) in
@[expose] def g2L : SL(3, L) →* ModGL Tag.G2 L :=
  (Units.map g2LHom).comp (toUnits : SL(3, L) ≃* (SL(3, L))ˣ).toMonoidHom

theorem coe_g2L (X : SL(3, L)) :
    ((g2L L X : ModGL Tag.G2 L) : Module.End L (RootModule Tag.G2 L)) = g2LEnd X :=
  rfl

theorem g2LRho_transvection {i j : Fin 3} (hij : i ≠ j) (t : L) (y : G2LModel L) :
    g2LRho (Matrix.SpecialLinearGroup.transvection hij t) y =
      y + t • g2LCoef1 i j y + t ^ 2 • g2LCoef2 i j y := by
  rw [g2LRho_apply, Matrix.SpecialLinearGroup.transvection_inv,
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

theorem isRoot_g2LSigma {i j : Fin 3} (hij : i ≠ j) : IsRoot Tag.G2 (g2LSigma i j) := by
  have h := g2LPos_spec i j hij
  rw [← h.2]
  exact CFSG.LieType.Chevalley.RootWalk.isRoot_rootCertificate_root h.1

theorem g2LPhi_elt {i j : Fin 3} (hij : i ≠ j) (t : L) :
    g2LPhi ∘ₗ (rootOperatorFamily Tag.G2).elt L ⟨g2LSigma i j, isRoot_g2LSigma hij⟩ t =
      g2LRho (Matrix.SpecialLinearGroup.transvection hij t) ∘ₗ g2LPhi := by
  have hpos : RootOps.rootPos (⟨g2LSigma i j, isRoot_g2LSigma hij⟩ : Root Tag.G2) = g2LPos i j :=
    RootOps.rootPos_eq (g2LPos_spec i j hij).1 (g2LPos_spec i j hij).2
  refine ext_posVec_G2L fun p hp => ?_
  have hp' : p < RootOps.dim Tag.G2 := by rw [dim_G2L]; exact hp
  obtain ⟨c1, c2, c3, hval⟩ := g2L_check i j hij p hp
  have hD : ∀ k, 1 ≤ k → k ≤ 3 →
      (rootOperatorFamily Tag.G2).D L ⟨g2LSigma i j, isRoot_g2LSigma hij⟩ k
        (RootOps.posVec Tag.G2 L p) =
      RootOps.vecOf Tag.G2 L (RootOps.colOf (RootOps.entries .G2 (g2LPos i j) k) p) := by
    intro k hk1 hk3
    change RootOps.dataD Tag.G2 L _ k _ = _
    rw [RootOps.dataD, ite_eq_right (by omega), ite_eq_left hk3, hpos,
      RootOps.entriesOp_posVec _ hp']
  have hD0 : (rootOperatorFamily Tag.G2).D L ⟨g2LSigma i j, isRoot_g2LSigma hij⟩ 0 = 1 :=
    (rootOperatorFamily Tag.G2).D_zero L _
  rw [LinearMap.comp_apply, LinearMap.comp_apply, g2LPhi_posVec hp, g2LRho_transvection,
    RootOperatorFamily.elt]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hD0, pow_zero, one_smul,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [hD 1 le_rfl (by norm_num), hD 2 (by norm_num) (by norm_num), hD 3 (by norm_num) le_rfl]
  simp only [map_add, map_smul, g2LPhi_posVec hp]
  rw [g2LPhi_vecOf _ (hval 1 (by simp)), g2LPhi_vecOf _ (hval 2 (by simp)),
    g2LPhi_vecOf _ (hval 3 (by simp)), c1, c2, c3, g2LCast_coef1, g2LCast_coef2, g2LCast_zero,
    smul_zero, add_zero, pow_one]

theorem g2L_transvection {i j : Fin 3} (hij : i ≠ j) (t : L) :
    g2L L (Matrix.SpecialLinearGroup.transvection hij t) =
      (rootOperatorFamily Tag.G2).eltUnit L ⟨g2LSigma i j, isRoot_g2LSigma hij⟩ t := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [coe_g2L, RootOperatorFamily.coe_eltUnit, g2LEnd_apply]
  have h := LinearMap.congr_fun (g2LPhi_elt hij t) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [← h, g2LPsi_phi]

theorem g2L_transvection_pinned {i j : Fin 3} (hij : i ≠ j) (t : L) :
    g2L L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.G2 L (g2LSigma i j)
        (((rootOperatorFamily Tag.G2).pinnedFamilySign (g2LSigma i j) : L) * t) := by
  rw [(rootOperatorFamily Tag.G2).pinnedX_eq_eltUnit L (isRoot_g2LSigma hij), ← mul_assoc,
    (rootOperatorFamily Tag.G2).pinnedFamilySign_mul_self L, one_mul, g2L_transvection]

theorem g2LSigma_neg (i j : Fin 3) : g2LSigma j i = -g2LSigma i j := by
  simp only [g2LSigma, neg_sub]

theorem g2LSigma_add (i j k : Fin 3) : g2LSigma i j + g2LSigma j k = g2LSigma i k := by
  simp only [g2LSigma, sub_add_sub_cancel]

theorem eq_one_of_mulVec_single {X : Matrix (Fin 3) (Fin 3) L}
    (h0 : X.mulVec (Pi.single 0 1) = Pi.single 0 1) (h1 : X.mulVec (Pi.single 1 1) = Pi.single 1 1)
    (h2 : X.mulVec (Pi.single 2 1) = Pi.single 2 1) : X = 1 := by
  ext i j
  fin_cases j
  · have := congrFun h0 i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply, Matrix.one_apply]
      using this
  · have := congrFun h1 i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply, Matrix.one_apply]
      using this
  · have := congrFun h2 i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply, Matrix.one_apply]
      using this

theorem g2L_injective : Function.Injective (g2L L) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  have hEnd : ∀ x, g2LEnd X x = x := by
    intro x
    have h := congrArg (fun g : ModGL Tag.G2 L =>
      (g : Module.End L (RootModule Tag.G2 L)) x) hX
    simpa [coe_g2L] using h
  have key : ∀ p < 14, g2LRho X (g2LCast (g2LData p)) = g2LCast (g2LData p) := by
    intro p hp
    have h1 := congrArg g2LPhi (hEnd (RootOps.posVec Tag.G2 L p))
    rw [g2LEnd_apply, g2LPhi_psi _ ((trace_g2LRho X _).trans (trace_g2LPhi _)),
      g2LPhi_posVec hp] at h1
    exact h1
  have col : ∀ p < 14, ∀ k : Fin 3, (g2LData p).2.1 = Pi.single k 1 →
      (X : Matrix (Fin 3) (Fin 3) L).mulVec (Pi.single k 1) = Pi.single k 1 := by
    intro p hp k hk
    have h1 := congrArg (fun y : G2LModel L => y.2.1) (key p hp)
    rw [g2LRho_apply] at h1
    simp only [g2LCast, hk] at h1
    have hcast : (fun j : Fin 3 => (((Pi.single k (1 : ℤ) : Fin 3 → ℤ) j : ℤ) : L)) =
        (Pi.single k 1 : Fin 3 → L) := by
      funext j
      by_cases hj : j = k <;> simp [Pi.single_apply, hj]
    rw [hcast] at h1
    exact h1
  have hX1 : (X : Matrix (Fin 3) (Fin 3) L) = 1 :=
    eq_one_of_mulVec_single (col 6 (by norm_num) 0 rfl) (col 3 (by norm_num) 1 rfl)
      (col 13 (by norm_num) 2 rfl)
  exact Subtype.ext (by simpa using hX1)

section Diag

open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def g2LDiag (b : Fin Tag.G2.rank → Lˣ) : Fin 3 → Lˣ :=
  ![b 0 * b 1, b 1, (b 0 * b 1 ^ 2)⁻¹]

theorem g2LDiag_det (b : Fin Tag.G2.rank → Lˣ) :
    ((g2LDiag b 0 : Lˣ) : L) * (g2LDiag b 1 : Lˣ) * (g2LDiag b 2 : Lˣ) = 1 := by
  simp only [g2LDiag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val]
  have h0 := (b 0).ne_zero
  have h1 := (b 1).ne_zero
  field_simp

@[expose] def g2LVec (x y : ℤ) : Fin Tag.G2.rank → ℤ := ![x, y]

@[expose] def g2LWt : ℕ → Fin Tag.G2.rank → ℤ
  | 2 => g2LVec 1 0
  | 3 => g2LVec 0 1
  | 4 => g2LVec (-1) 0
  | 5 => g2LVec 1 3
  | 6 => g2LVec 1 1
  | 7 => g2LVec 0 (-1)
  | 8 => g2LVec (-1) (-3)
  | 9 => g2LVec 2 3
  | 10 => g2LVec 1 2
  | 11 => g2LVec (-1) (-1)
  | 12 => g2LVec (-2) (-3)
  | 13 => g2LVec (-1) (-2)
  | _ => 0

theorem g2LRho_diag (d : Fin 3 → Lˣ) (h : (d 0 : L) * d 1 * d 2 = 1) (y : G2LModel L) :
    g2LRho (diagSL3 d h) y =
      (Matrix.of fun i j => (d i : L) * y.1 i j * ((d j)⁻¹ : Lˣ), fun i => (d i : L) * y.2.1 i,
        fun i => ((d i)⁻¹ : Lˣ) * y.2.2 i) := by
  rw [g2LRho_apply, diagSL3_inv, coe_diagSL3, coe_diagSL3]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, mul_assoc]
  · funext i
    simp only [Matrix.mulVec_diagonal]
  · funext i
    simp only [Matrix.diagonal_transpose, Matrix.mulVec_diagonal]

theorem g2LRho_diag_mat (d : Fin 3 → Lˣ) (h : (d 0 : L) * d 1 * d 2 = 1) (a b : Fin 3) (z : L) :
    g2LRho (diagSL3 d h) ((Matrix.single a b z, 0, 0) : G2LModel L) =
      ((d a : L) * ((d b)⁻¹ : Lˣ)) • ((Matrix.single a b z, 0, 0) : G2LModel L) := by
  rw [g2LRho_diag]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    simp only [Matrix.of_apply, Matrix.single_apply, Prod.smul_mk, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [and_self, if_true]
      ring
    · simp [hij]
  · funext i
    simp
  · funext i
    simp

theorem g2LRho_diag_cartan (d : Fin 3 → Lˣ) (h : (d 0 : L) * d 1 * d 2 = 1) (v : Fin 3 → L) :
    g2LRho (diagSL3 d h) ((Matrix.diagonal v, 0, 0) : G2LModel L) =
      ((Matrix.diagonal v, 0, 0) : G2LModel L) := by
  rw [g2LRho_diag]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq]
      field_simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  · funext i
    simp
  · funext i
    simp

theorem g2LRho_diag_vec (d : Fin 3 → Lˣ) (h : (d 0 : L) * d 1 * d 2 = 1) (k : Fin 3) (z : L) :
    g2LRho (diagSL3 d h) ((0, Pi.single k z, 0) : G2LModel L) =
      (d k : L) • ((0, Pi.single k z, 0) : G2LModel L) := by
  rw [g2LRho_diag]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    simp
  · funext i
    by_cases hik : i = k
    · subst hik
      simp
    · simp [Pi.single_apply, hik]
  · funext i
    simp

theorem g2LRho_diag_dual (d : Fin 3 → Lˣ) (h : (d 0 : L) * d 1 * d 2 = 1) (k : Fin 3) (z : L) :
    g2LRho (diagSL3 d h) ((0, 0, Pi.single k z) : G2LModel L) =
      (((d k)⁻¹ : Lˣ) : L) • ((0, 0, Pi.single k z) : G2LModel L) := by
  rw [g2LRho_diag]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i j
    simp
  · funext i
    simp
  · funext i
    by_cases hik : i = k
    · subst hik
      simp
    · simp [Pi.single_apply, hik]

theorem g2LCast_mat (M : Matrix (Fin 3) (Fin 3) ℤ) :
    (g2LCast ((M, 0, 0) : G2LModel ℤ) : G2LModel L) = (M.map (Int.castRingHom L), 0, 0) := by
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> funext k <;> simp [g2LCast]

theorem g2LCast_vec (v : Fin 3 → ℤ) :
    (g2LCast ((0, v, 0) : G2LModel ℤ) : G2LModel L) = (0, fun k => (v k : L), 0) := by
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · ext i j
    simp [g2LCast]
  · funext k
    simp [g2LCast]

theorem g2LCast_dual (v : Fin 3 → ℤ) :
    (g2LCast ((0, 0, v) : G2LModel ℤ) : G2LModel L) = (0, 0, fun k => (v k : L)) := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · ext i j
    simp [g2LCast]
  · funext k
    simp [g2LCast]

theorem map_single_cast (a b : Fin 3) :
    (Matrix.single a b (1 : ℤ)).map (Int.castRingHom L) = Matrix.single a b (1 : L) := by
  rw [Matrix.map_single, map_one]

theorem map_diagonal_cast (v : Fin 3 → ℤ) :
    (Matrix.diagonal v).map (Int.castRingHom L) = Matrix.diagonal fun i => (v i : L) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem vec_single_cast (k : Fin 3) :
    (fun j : Fin 3 => (((Pi.single k (1 : ℤ) : Fin 3 → ℤ) j : ℤ) : L)) =
      (Pi.single k 1 : Fin 3 → L) := by
  funext j
  by_cases hj : j = k <;> simp [Pi.single_apply, hj]

theorem g2LCast_mat_single (a b : Fin 3) :
    (g2LCast ((Matrix.single a b 1, 0, 0) : G2LModel ℤ) : G2LModel L) =
      (Matrix.single a b (1 : L), 0, 0) := by
  rw [g2LCast_mat, map_single_cast]

theorem g2LCast_mat_neg_single (a b : Fin 3) :
    (g2LCast ((-Matrix.single a b 1, 0, 0) : G2LModel ℤ) : G2LModel L) =
      (Matrix.single a b (-1 : L), 0, 0) := by
  rw [g2LCast_mat]
  refine Prod.ext ?_ rfl
  ext i j
  by_cases hij : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hij
    simp
  · simp [Matrix.single_apply, hij]

theorem g2LCast_vec_single (k : Fin 3) :
    (g2LCast ((0, Pi.single k 1, 0) : G2LModel ℤ) : G2LModel L) = (0, Pi.single k (1 : L), 0) := by
  rw [g2LCast_vec, vec_single_cast]

theorem g2LCast_dual_single (k : Fin 3) :
    (g2LCast ((0, 0, Pi.single k 1) : G2LModel ℤ) : G2LModel L) = (0, 0, Pi.single k (1 : L)) := by
  rw [g2LCast_dual, vec_single_cast]

theorem g2LCast_dual_neg_single (k : Fin 3) :
    (g2LCast ((0, 0, -Pi.single k 1) : G2LModel ℤ) : G2LModel L) =
      (0, 0, Pi.single k (-1 : L)) := by
  rw [g2LCast_dual]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext j
  by_cases hj : j = k
  · subst hj
    simp
  · simp [Pi.single_apply, hj]

theorem rootChar_g2LVec (b : Fin Tag.G2.rank → Lˣ) (x y : ℤ) :
    rootChar b (g2LVec x y) = b 0 ^ x * b 1 ^ y :=
  Fin.prod_univ_two (fun i => b i ^ (g2LVec x y) i)

theorem g2LRho_diag_data (b : Fin Tag.G2.rank → Lˣ) : ∀ p < 14,
    g2LRho (diagSL3 (g2LDiag b) (g2LDiag_det b)) (g2LCast (g2LData p)) =
      ((rootChar b (g2LWt p) : Lˣ) : L) • g2LCast (g2LData p) := by
  intro p hp
  have h0 := (b 0).ne_zero
  have h1 := (b 1).ne_zero
  interval_cases p
  · have e : g2LData 0 = ((Matrix.diagonal ![-1, 1, 0], 0, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 0 = 0 := rfl
    rw [e, g2LCast_mat, map_diagonal_cast, g2LRho_diag_cartan, w, rootChar_zero, Units.val_one,
      one_smul]
  · have e : g2LData 1 = ((Matrix.diagonal ![-1, 2, -1], 0, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 1 = 0 := rfl
    rw [e, g2LCast_mat, map_diagonal_cast, g2LRho_diag_cartan, w, rootChar_zero, Units.val_one,
      one_smul]
  · have e : g2LData 2 = ((Matrix.single 0 1 1, 0, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 2 = g2LVec 1 0 := rfl
    rw [e, g2LCast_mat_single, g2LRho_diag_mat, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 3 = ((0, Pi.single 1 1, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 3 = g2LVec 0 1 := rfl
    rw [e, g2LCast_vec_single, g2LRho_diag_vec, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 4 = ((-Matrix.single 1 0 1, 0, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 4 = g2LVec (-1) (0) := rfl
    rw [e, g2LCast_mat_neg_single, g2LRho_diag_mat, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 5 = ((Matrix.single 1 2 1, 0, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 5 = g2LVec 1 3 := rfl
    rw [e, g2LCast_mat_single, g2LRho_diag_mat, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 6 = ((0, Pi.single 0 1, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 6 = g2LVec 1 1 := rfl
    rw [e, g2LCast_vec_single, g2LRho_diag_vec, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 7 = ((0, 0, -Pi.single 1 1) : G2LModel ℤ) := rfl
    have w : g2LWt 7 = g2LVec (0) (-1) := rfl
    rw [e, g2LCast_dual_neg_single, g2LRho_diag_dual, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 8 = ((Matrix.single 2 1 1, 0, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 8 = g2LVec (-1) (-3) := rfl
    rw [e, g2LCast_mat_single, g2LRho_diag_mat, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 9 = ((Matrix.single 0 2 1, 0, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 9 = g2LVec 2 3 := rfl
    rw [e, g2LCast_mat_single, g2LRho_diag_mat, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 10 = ((0, 0, -Pi.single 2 1) : G2LModel ℤ) := rfl
    have w : g2LWt 10 = g2LVec 1 2 := rfl
    rw [e, g2LCast_dual_neg_single, g2LRho_diag_dual, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 11 = ((0, 0, Pi.single 0 1) : G2LModel ℤ) := rfl
    have w : g2LWt 11 = g2LVec (-1) (-1) := rfl
    rw [e, g2LCast_dual_single, g2LRho_diag_dual, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 12 = ((-Matrix.single 2 0 1, 0, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 12 = g2LVec (-2) (-3) := rfl
    rw [e, g2LCast_mat_neg_single, g2LRho_diag_mat, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp
  · have e : g2LData 13 = ((0, Pi.single 2 1, 0) : G2LModel ℤ) := rfl
    have w : g2LWt 13 = g2LVec (-1) (-2) := rfl
    rw [e, g2LCast_vec_single, g2LRho_diag_vec, w]
    congr 1
    simp [g2LDiag, rootChar_g2LVec] <;> field_simp

theorem g2LWt_root : ∀ p < 14, Tag.G2.rank ≤ p →
    Tag.G2.rootCertificate.root (p - Tag.G2.rank) = g2LWt p := by
  decide +kernel

theorem rootDiag_posVec_G2 (b : Fin Tag.G2.rank → Lˣ) : ∀ p < 14,
    rootDiag b (RootOps.posVec Tag.G2 L p) =
      ((rootChar b (g2LWt p) : Lˣ) : L) • RootOps.posVec Tag.G2 L p := by
  intro p hp
  by_cases h : p < Tag.G2.rank
  · have hp2 : p < 2 := h
    have hw : g2LWt p = 0 := by interval_cases p <;> rfl
    rw [RootOps.posVec, dif_pos h, rootDiag_hVec, hw, rootChar_zero, Units.val_one, one_smul]
  · have hr : Tag.G2.rank = 2 := rfl
    have hlen : Tag.G2.rootCertificate.roots.length = 12 := rfl
    rw [RootOps.posVec, dif_neg h, rootDiag_rootVec b (RootWalk.isRoot_rootCertificate_root
      (show p - Tag.G2.rank < Tag.G2.rootCertificate.roots.length by omega)),
      g2LWt_root p hp (not_lt.1 h)]

theorem g2L_diag_eq (b : Fin Tag.G2.rank → Lˣ) :
    g2L L (diagSL3 (g2LDiag b) (g2LDiag_det b)) = rootDiagUnit Tag.G2 b := by
  refine Units.ext ?_
  rw [coe_g2L]
  change g2LEnd _ = rootDiag b
  refine ext_posVec_G2L fun p hp => ?_
  rw [g2LEnd_apply, g2LPhi_posVec hp, g2LRho_diag_data b p hp, map_smul, g2LPsi_cast hp]
  exact (rootDiag_posVec_G2 b p hp).symm

theorem g2L_diag [IsAlgClosed L] (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    g2L L A ∈ torusGroup Tag.G2 L := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h1 : (A : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 := fun h => by
    rw [h, mul_zero, zero_mul] at hdet
    exact zero_ne_one hdet
  have h2 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 ≠ 0 := fun h => by
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  set b : Fin Tag.G2.rank → Lˣ :=
    ![Units.mk0 ((A : Matrix (Fin 3) (Fin 3) L) 0 0 / (A : Matrix (Fin 3) (Fin 3) L) 1 1)
      (div_ne_zero h0 h1), Units.mk0 ((A : Matrix (Fin 3) (Fin 3) L) 1 1) h1] with hb
  have hA' : A = diagSL3 (g2LDiag b) (g2LDiag_det b) := by
    refine Subtype.ext ?_
    rw [coe_diagSL3, hdiag]
    congr 1
    funext i
    fin_cases i
    · simp [g2LDiag, hb]
      field_simp
    · simp [g2LDiag, hb]
    · simp [g2LDiag, hb]
      field_simp
      linear_combination hdet
  rw [hA', g2L_diag_eq]
  exact rootDiagUnit_mem_torusGroup b

end Diag

theorem g2L_isA2Frame [IsAlgClosed L] :
    CFSG.RankThree.PartOne.KF4.IsA2Frame (g2L L) g2LSigma where
  injective := g2L_injective
  isRoot i j hij := isRoot_g2LSigma hij
  neg := g2LSigma_neg
  add := g2LSigma_add
  transv i j hij := by
    have hs := (rootOperatorFamily Tag.G2).pinnedFamilySign_mul_self L (g2LSigma i j)
    refine ⟨Units.mk0 _ (left_ne_zero_of_mul_eq_one hs), fun t => ?_⟩
    rw [Units.val_mk0, g2L_transvection_pinned]
  range := by
    have hs : ∀ i j : Fin 3, ((rootOperatorFamily Tag.G2).pinnedFamilySign (g2LSigma i j) : L) *
        ((rootOperatorFamily Tag.G2).pinnedFamilySign (g2LSigma i j) : L) = 1 := fun i j =>
      (rootOperatorFamily Tag.G2).pinnedFamilySign_mul_self L _
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation,
        MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨X, ⟨i, j, hij, c, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, g2L_transvection_pinned]
      exact (le_iSup₂ (f := fun α (_ : α ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = g2LSigma i j}) =>
        rootSubgroup Tag.G2 L α) (g2LSigma i j) ⟨i, j, hij, rfl⟩)
        (Subgroup.subset_closure ⟨_, rfl⟩)
    · refine iSup₂_le fun α hα => ?_
      obtain ⟨i, j, hij, rfl⟩ := hα
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      refine ⟨Matrix.SpecialLinearGroup.transvection hij
        (((rootOperatorFamily Tag.G2).pinnedFamilySign (g2LSigma i j) : L) * c), ?_⟩
      rw [g2L_transvection_pinned, ← mul_assoc, hs, one_mul]
  diag A hA := g2L_diag A hA

end Frame

end G2Long

section G2Pairs

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def g2PairWord (l : List ℕ) : List (Fin Tag.G2.rank) :=
  l.map fun n => (⟨n % 2, Nat.mod_lt n (by decide)⟩ : Fin 2)

@[expose] def g2LongPairWords : List (List ℤ × List ℕ) :=
  [([1, 3], []), ([-2, -3], [1, 0, 1, 0, 1])]

@[expose] def g2ShortPairWords : List (List ℤ × List ℕ) :=
  [([1, 1], []), ([-1, -2], [0, 1, 0, 1, 0])]

set_option maxRecDepth 100000 in
theorem g2LongPairWords_spec : ∀ ent ∈ g2LongPairWords,
    (g2PairWord ent.2).foldr (reflect Tag.G2) (g2LSigma 0 1) = g2LSigma 0 1 ∧
      (g2PairWord ent.2).foldr (reflect Tag.G2) (g2LSigma 1 2) = toVec Tag.G2.rank ent.1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem g2ShortPairWords_spec : ∀ ent ∈ g2ShortPairWords,
    (g2PairWord ent.2).foldr (reflect Tag.G2) (g2LWeight 1) = g2LWeight 1 ∧
      (g2PairWord ent.2).foldr (reflect Tag.G2) (g2LWeight 0) = toVec Tag.G2.rank ent.1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem g2LongPairWords_complete :
    ∀ l ∈ Tag.G2.artifactRoots,
      iform (g2LSigma 0 1) (toVec Tag.G2.rank l) = -3 →
        iform (toVec Tag.G2.rank l) (toVec Tag.G2.rank l) = 6 →
          l ∈ g2LongPairWords.map Prod.fst := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem g2ShortPairWords_complete :
    ∀ l ∈ Tag.G2.artifactRoots,
      iform (g2LWeight 1) (toVec Tag.G2.rank l) = -1 →
        iform (toVec Tag.G2.rank l) (toVec Tag.G2.rank l) = 2 →
          l ∈ g2ShortPairWords.map Prod.fst := by
  decide +kernel

theorem wordProd_smul_g2L (l : List (Fin Tag.G2.rank)) (v : Fin Tag.G2.rank → ℤ) :
    (coxeterSystem Tag.G2).wordProd l • v = l.foldr (reflect Tag.G2) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem g2LSigma_zero_one : g2LSigma 0 1 = Pi.single 0 1 := by decide +kernel

theorem g2LWeight_one : g2LWeight 1 = Pi.single 1 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem g2LSigma_long : ∀ i j : Fin 3, i ≠ j → iform (g2LSigma i j) (g2LSigma i j) = 6 := by
  decide +kernel

theorem iform_g2LWeight : ∀ i : Fin 3, iform (g2LWeight i) (g2LWeight i) = 2 := by
  decide +kernel

section


theorem exists_weyl_a2Pair_G2 {α β : Fin Tag.G2.rank → ℤ} (h : IsA2Pair α β) :
    (∃ v : WeylGroup Tag.G2, v • g2LSigma 0 1 = α ∧ v • g2LSigma 1 2 = β) ∨
      (∃ v : WeylGroup Tag.G2, v • g2LWeight 1 = α ∧ v • g2LWeight 0 = β) := by
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 h.isRoot_fst
  fin_cases j
  · left
    have hα : w • g2LSigma 0 1 = α := by rw [g2LSigma_zero_one]; exact hw
    have hn : iform α α = 6 := by rw [← hα, iform_smul]; exact g2LSigma_long 0 1 (by decide)
    set β' := w⁻¹ • β with hβ'
    have hβ'r : IsRoot Tag.G2 β' := IsRoot.smul h.isRoot_snd w⁻¹
    have hform : iform (g2LSigma 0 1) β' = -3 := by
      have e : iform (g2LSigma 0 1) β' = iform α β := by
        rw [← iform_smul w, hα, hβ', smul_inv_smul]
      have h2 := h.two_iform
      rw [hn] at h2
      rw [e]
      omega
    have hform' : iform β' β' = 6 := by rw [hβ', iform_smul, h.iform_snd, hn]
    obtain ⟨l, hl, hβ'l⟩ := isRoot_iff_exists_mem.1 hβ'r
    obtain ⟨ent, hent, hentl⟩ := List.mem_map.1 (g2LongPairWords_complete l hl
      (by rw [← hβ'l]; exact hform) (by rw [← hβ'l]; exact hform'))
    obtain ⟨h0, h2⟩ := g2LongPairWords_spec ent hent
    refine ⟨w * (coxeterSystem Tag.G2).wordProd (g2PairWord ent.2), ?_, ?_⟩
    · rw [mul_smul, wordProd_smul_g2L, h0, hα]
    · rw [mul_smul, wordProd_smul_g2L, h2, hentl, ← hβ'l, hβ', smul_inv_smul]
  · right
    have hα : w • g2LWeight 1 = α := by rw [g2LWeight_one]; exact hw
    have hn : iform α α = 2 := by rw [← hα, iform_smul]; exact iform_g2LWeight 1
    set β' := w⁻¹ • β with hβ'
    have hβ'r : IsRoot Tag.G2 β' := IsRoot.smul h.isRoot_snd w⁻¹
    have hform : iform (g2LWeight 1) β' = -1 := by
      have e : iform (g2LWeight 1) β' = iform α β := by
        rw [← iform_smul w, hα, hβ', smul_inv_smul]
      have h2 := h.two_iform
      rw [hn] at h2
      rw [e]
      omega
    have hform' : iform β' β' = 2 := by rw [hβ', iform_smul, h.iform_snd, hn]
    obtain ⟨l, hl, hβ'l⟩ := isRoot_iff_exists_mem.1 hβ'r
    obtain ⟨ent, hent, hentl⟩ := List.mem_map.1 (g2ShortPairWords_complete l hl
      (by rw [← hβ'l]; exact hform) (by rw [← hβ'l]; exact hform'))
    obtain ⟨h0, h2⟩ := g2ShortPairWords_spec ent hent
    refine ⟨w * (coxeterSystem Tag.G2).wordProd (g2PairWord ent.2), ?_, ?_⟩
    · rw [mul_smul, wordProd_smul_g2L, h0, hα]
    · rw [mul_smul, wordProd_smul_g2L, h2, hentl, ← hβ'l, hβ', smul_inv_smul]

end

end G2Pairs

section G2Span

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar

section

variable
  {L : Type} [Field L]

theorem coe_xPar_mem_rootSubgroup_G2 {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ) (x : L) :
    ((xPar (rootOperatorFamily Tag.G2) γ x : adjointGroup Tag.G2 L) : ModGL Tag.G2 L) ∈
      rootSubgroup Tag.G2 L γ := by
  have h := (rootOperatorFamily Tag.G2).pinnedX_eq_eltUnit L hγ
    (((rootOperatorFamily Tag.G2).pinnedFamilySign γ : L) * x)
  rw [← mul_assoc, (rootOperatorFamily Tag.G2).pinnedFamilySign_mul_self L, one_mul] at h
  rw [xPar_of_isRoot hγ, RootOperatorFamily.coe_eltElement, ← h]
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem rootSubgroup_le_rootSpan_of_comm {S : Set (Fin Tag.G2.rank → ℤ)} {a b g : ℕ} {N : ℤ}
    (ha : a < 12) (hb : b < 12) (hg : g < 12)
    (hrep : RootOps.repCheck Tag.G2 a b [(1, 1, g, N)] = true)
    (hN : (N : L) ≠ 0) (hSa : Tag.G2.rootCertificate.root a ∈ S)
    (hSb : Tag.G2.rootCertificate.root b ∈ S) :
    rootSubgroup Tag.G2 L (Tag.G2.rootCertificate.root g) ≤ rootSpan Tag.G2 L S := by
  have hrg : IsRoot Tag.G2 (Tag.G2.rootCertificate.root g) :=
    RootWalk.isRoot_rootCertificate_root hg
  have hra : IsRoot Tag.G2 (Tag.G2.rootCertificate.root a) :=
    RootWalk.isRoot_rootCertificate_root ha
  have hrb : IsRoot Tag.G2 (Tag.G2.rootCertificate.root b) :=
    RootWalk.isRoot_rootCertificate_root hb
  have hcomm := fun s t : L => CFSG.Timmesfeld.RankTwo.commutator_xPar_of_repCheck (K := L) hrep s t
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  have hx : pinnedX Tag.G2 L (Tag.G2.rootCertificate.root g) c =
      ((xPar (rootOperatorFamily Tag.G2) (Tag.G2.rootCertificate.root g)
        (((rootOperatorFamily Tag.G2).pinnedFamilySign (Tag.G2.rootCertificate.root g) : L) * c) :
        adjointGroup Tag.G2 L) : ModGL Tag.G2 L) := by
    rw [xPar_of_isRoot hrg, RootOperatorFamily.coe_eltElement,
      (rootOperatorFamily Tag.G2).pinnedX_eq_eltUnit L hrg]
  rw [SetLike.mem_coe, hx]
  set x : L := ((rootOperatorFamily Tag.G2).pinnedFamilySign (Tag.G2.rootCertificate.root g) : L) *
    c with hxdef
  have h1 := hcomm 1 (x / N)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one] at h1
  have h2 : (N : L) * (x / N) = x := by field_simp
  rw [h2] at h1
  rw [← h1, commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hA := coe_xPar_mem_rootSubgroup_G2 (L := L) hra 1
  have hB := coe_xPar_mem_rootSubgroup_G2 (L := L) hrb (x / N)
  have hA' : rootSubgroup Tag.G2 L (Tag.G2.rootCertificate.root a) ≤ rootSpan Tag.G2 L S :=
    le_iSup₂ (f := fun α (_ : α ∈ S) => rootSubgroup Tag.G2 L α) _ hSa
  have hB' : rootSubgroup Tag.G2 L (Tag.G2.rootCertificate.root b) ≤ rootSpan Tag.G2 L S :=
    le_iSup₂ (f := fun α (_ : α ∈ S) => rootSubgroup Tag.G2 L α) _ hSb
  exact mul_mem (mul_mem (mul_mem (hA' hA) (hB' hB)) (inv_mem (hA' hA))) (inv_mem (hB' hB))

set_option maxRecDepth 100000 in
theorem root_mem_a2Roots_short : ∀ k ∈ [1, 4, 5, 8, 9, 11],
    Tag.G2.rootCertificate.root k ∈ a2Roots (g2LWeight 1) (g2LWeight 0) := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff]; decide +kernel)

set_option maxRecDepth 100000 in
theorem rootSubgroup_g2LSigma_le (h3 : (3 : L) ≠ 0) (i j : Fin 3) (hij : i ≠ j) :
    rootSubgroup Tag.G2 L (g2LSigma i j) ≤
      rootSpan Tag.G2 L (a2Roots (g2LWeight 1) (g2LWeight 0)) := by
  rw [← (g2LPos_spec i j hij).2]
  have hS := root_mem_a2Roots_short
  have h3' : (((3 : ℤ) : ℤ) : L) ≠ 0 := by exact_mod_cast h3
  have h3'' : (((-3 : ℤ) : ℤ) : L) ≠ 0 := by simpa using h3
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact rootSubgroup_le_rootSpan_of_comm (a := 4) (b := 5) (g := 0) (N := 3) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel) h3' (hS 4 (by simp)) (hS 5 (by simp))
  · exact rootSubgroup_le_rootSpan_of_comm (a := 4) (b := 8) (g := 7) (N := 3) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel) h3' (hS 4 (by simp)) (hS 8 (by simp))
  · exact rootSubgroup_le_rootSpan_of_comm (a := 1) (b := 9) (g := 2) (N := 3) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel) h3' (hS 1 (by simp)) (hS 9 (by simp))
  · exact absurd rfl hij
  · exact rootSubgroup_le_rootSpan_of_comm (a := 1) (b := 8) (g := 3) (N := 3) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel) h3' (hS 1 (by simp)) (hS 8 (by simp))
  · exact rootSubgroup_le_rootSpan_of_comm (a := 9) (b := 11) (g := 10) (N := -3) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel) h3'' (hS 9 (by simp)) (hS 11 (by simp))
  · exact rootSubgroup_le_rootSpan_of_comm (a := 5) (b := 11) (g := 6) (N := -3) (by norm_num)
      (by norm_num) (by norm_num) (by decide +kernel) h3'' (hS 5 (by simp)) (hS 11 (by simp))
  · exact absurd rfl hij

end

end G2Span

section G2Block

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KE

set_option maxRecDepth 100000 in
theorem g2_long_sigma_of_norm : ∀ l ∈ Tag.G2.artifactRoots,
    iform (toVec Tag.G2.rank l) (toVec Tag.G2.rank l) = 6 →
      ∃ i j : Fin 3, i ≠ j ∧ toVec Tag.G2.rank l = g2LSigma i j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem g2_short_isA2Pair :
    IsA2Pair (τ := Tag.G2) (g2LWeight 1) (g2LWeight 0) where
  isRoot_fst := by
    have h := isRoot_toVec (τ := Tag.G2) (l := [0, 1]) (by decide +kernel)
    rwa [show toVec Tag.G2.rank [0, 1] = g2LWeight 1 by decide +kernel] at h
  isRoot_snd := by
    have h := isRoot_toVec (τ := Tag.G2) (l := [1, 1]) (by decide +kernel)
    rwa [show toVec Tag.G2.rank [1, 1] = g2LWeight 0 by decide +kernel] at h
  isRoot_add := by
    have h := isRoot_toVec (τ := Tag.G2) (l := [1, 2]) (by decide +kernel)
    rwa [show toVec Tag.G2.rank [1, 2] = g2LWeight 1 + g2LWeight 0 by decide +kernel] at h
  iform_snd := by decide +kernel
  two_iform := by decide +kernel

theorem image_smul_a2Roots (v : WeylGroup Tag.G2) (x y : Fin Tag.G2.rank → ℤ) :
    (fun γ => v • γ) '' a2Roots x y = a2Roots (v • x) (v • y) := by
  simp only [a2Roots, Set.image_insert_eq, Set.image_singleton, smul_neg, smul_add]

section

variable
  {L : Type} [Field L]

theorem rootSubgroup_long_le_short (h3 : (3 : L) ≠ 0) (v : WeylGroup Tag.G2)
    {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ) (hn : iform γ γ = 6) :
    rootSubgroup Tag.G2 L γ ≤
      rootSpan Tag.G2 L (a2Roots (v • g2LWeight 1) (v • g2LWeight 0)) := by
  obtain ⟨γ₀, rfl⟩ : ∃ γ₀, γ = v • γ₀ := ⟨v⁻¹ • γ, (smul_inv_smul v γ).symm⟩
  have hγ₀ : IsRoot Tag.G2 γ₀ := (isRoot_smul_iff v).1 hγ
  have hn₀ : iform γ₀ γ₀ = 6 := by rwa [iform_smul] at hn
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hγ₀
  obtain ⟨i, j, hij, hl'⟩ := g2_long_sigma_of_norm l hl hn₀
  have h1 := rootSubgroup_g2LSigma_le (L := L) h3 i j hij
  rw [← hl'] at h1
  rw [← map_conj_rootSubgroup (L := L) v hγ₀]
  refine (Subgroup.map_mono h1).trans ?_
  rw [map_conj_rootSpan v (a2Roots_isRoot g2_short_isA2Pair), image_smul_a2Roots]

theorem long_of_mem_a2Roots_frame (u : WeylGroup Tag.G2) {r : Fin Tag.G2.rank → ℤ}
    (hr : r ∈ a2Roots (u • g2LSigma 0 1) (u • g2LSigma 1 2)) :
    IsRoot Tag.G2 r ∧ iform r r = 6 := by
  have hroot : ∀ a b : Fin 3, a ≠ b → IsRoot Tag.G2 (u • g2LSigma a b) ∧
      iform (u • g2LSigma a b) (u • g2LSigma a b) = 6 := fun a b hab =>
    ⟨IsRoot.smul (isRoot_g2LSigma hab) u, by rw [iform_smul]; exact g2LSigma_long a b hab⟩
  have e02 : u • g2LSigma 0 1 + u • g2LSigma 1 2 = u • g2LSigma 0 2 := by
    rw [← smul_add, g2LSigma_add]
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hroot 0 1 (by decide)
  · have := hroot 1 0 (by decide)
    rwa [g2LSigma_neg 0 1, smul_neg] at this
  · exact hroot 1 2 (by decide)
  · have := hroot 2 1 (by decide)
    rwa [g2LSigma_neg 1 2, smul_neg] at this
  · rw [e02]
    exact hroot 0 2 (by decide)
  · have := hroot 2 0 (by decide)
    rwa [g2LSigma_neg 0 2, smul_neg, ← e02] at this

theorem g2_weyl_image_short (v : WeylGroup Tag.G2) :
    rootReflection ((v * simple Tag.G2 1) • g2LSigma 0 1) *
        rootReflection ((v * simple Tag.G2 1) • g2LSigma 1 2) =
      rootReflection (v • g2LWeight 1) * rootReflection (v • g2LWeight 0) := by
  have hS0 : simple Tag.G2 0 * simple Tag.G2 0 = 1 :=
    (coxeterSystem Tag.G2).simple_mul_simple_self 0
  have hS1 : simple Tag.G2 1 * simple Tag.G2 1 = 1 :=
    (coxeterSystem Tag.G2).simple_mul_simple_self 1
  have hS0i : (simple Tag.G2 0)⁻¹ = simple Tag.G2 0 := inv_eq_of_mul_eq_one_right hS0
  have hS1i : (simple Tag.G2 1)⁻¹ = simple Tag.G2 1 := inv_eq_of_mul_eq_one_right hS1
  have hr01 : IsRoot Tag.G2 (g2LSigma 0 1) := isRoot_g2LSigma (by decide)
  have hr12 : IsRoot Tag.G2 (g2LSigma 1 2) := isRoot_g2LSigma (by decide)
  have hw1 : IsRoot Tag.G2 (g2LWeight 1) := g2_short_isA2Pair.isRoot_fst
  have hw0 : IsRoot Tag.G2 (g2LWeight 0) := g2_short_isA2Pair.isRoot_snd
  have E2 : rootReflection (g2LSigma 0 1) = simple Tag.G2 0 := by
    rw [rootReflection_eq_conj (w := 1) (j := 0) (by rw [one_smul, g2LSigma_zero_one])]
    simp
  have E1 : rootReflection (g2LSigma 1 2) =
      simple Tag.G2 1 * simple Tag.G2 0 * simple Tag.G2 1 := by
    rw [rootReflection_eq_conj (w := simple Tag.G2 1) (j := 0)
      (by rw [simple_smul]; decide +kernel), hS1i]
  have E3 : rootReflection (g2LWeight 1) = simple Tag.G2 1 := by
    rw [rootReflection_eq_conj (w := 1) (j := 1) (by rw [one_smul, g2LWeight_one])]
    simp
  have E4 : rootReflection (g2LWeight 0) =
      simple Tag.G2 0 * simple Tag.G2 1 * simple Tag.G2 0 := by
    rw [rootReflection_eq_conj (w := simple Tag.G2 0) (j := 1)
      (by rw [simple_smul]; decide +kernel), hS0i]
  rw [rootReflection_smul_root _ hr01, rootReflection_smul_root _ hr12,
    rootReflection_smul_root _ hw1, rootReflection_smul_root _ hw0, E1, E2, E3, E4]
  have word : simple Tag.G2 1 * simple Tag.G2 0 * simple Tag.G2 1 *
      (simple Tag.G2 1 * (simple Tag.G2 1 * simple Tag.G2 0 * simple Tag.G2 1) *
        simple Tag.G2 1) =
      simple Tag.G2 1 * (simple Tag.G2 0 * simple Tag.G2 1 * simple Tag.G2 0) := by
    calc simple Tag.G2 1 * simple Tag.G2 0 * simple Tag.G2 1 *
          (simple Tag.G2 1 * (simple Tag.G2 1 * simple Tag.G2 0 * simple Tag.G2 1) *
            simple Tag.G2 1) =
        simple Tag.G2 1 * simple Tag.G2 0 * (simple Tag.G2 1 * simple Tag.G2 1) *
          (simple Tag.G2 1 * simple Tag.G2 0 * (simple Tag.G2 1 * simple Tag.G2 1)) := by
          simp only [mul_assoc]
      _ = _ := by rw [hS1]; simp only [mul_one, mul_assoc]
  have key : (v * simple Tag.G2 1) * simple Tag.G2 0 * (v * simple Tag.G2 1)⁻¹ *
      ((v * simple Tag.G2 1) * (simple Tag.G2 1 * simple Tag.G2 0 * simple Tag.G2 1) *
        (v * simple Tag.G2 1)⁻¹) =
      v * (simple Tag.G2 1 * simple Tag.G2 0 * simple Tag.G2 1 *
        (simple Tag.G2 1 * (simple Tag.G2 1 * simple Tag.G2 0 * simple Tag.G2 1) *
          simple Tag.G2 1)) * v⁻¹ := by
    rw [mul_inv_rev, hS1i]
    group
  rw [key, word]
  group

end

section


theorem a2BlockToral_G2 : A2BlockToral Tag.G2 := by
  intro L _ _ hL α β hpair
  have h3 : (3 : L) ≠ 0 := three_ne_zero_of_ringChar_ne_three hL
  rcases exists_weyl_a2Pair_G2 hpair with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩
  · have key := a2BlockAt_of_frame hL ((g2L_isA2Frame (L := L)).transport v)
    simp only [h1, h2] at key
    exact key
  · obtain ⟨m, hmS, hm, hmρ, hmt⟩ :=
      a2BlockAt_of_frame hL ((g2L_isA2Frame (L := L)).transport (v * simple Tag.G2 1))
    have hspan : rootSpan Tag.G2 L (a2Roots ((v * simple Tag.G2 1) • g2LSigma 0 1)
        ((v * simple Tag.G2 1) • g2LSigma 1 2)) ≤ rootSpan Tag.G2 L (a2Roots α β) := by
      refine iSup₂_le fun r hr => ?_
      obtain ⟨hr1, hr2⟩ := long_of_mem_a2Roots_frame (v * simple Tag.G2 1) hr
      rw [← h1, ← h2]
      exact rootSubgroup_long_le_short h3 v hr1 hr2
    refine ⟨m, hspan hmS, hm, ?_, fun t ht => ?_⟩
    · rw [hmρ, ← h1, ← h2]
      exact g2_weyl_image_short v
    · obtain ⟨y, hy, hyt⟩ := hmt t ht
      exact ⟨y, hspan hy, hyt⟩

end

end G2Block

section D4Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KF4
open scoped MatrixGroups


theorem d4L_chain_add : ∀ i j k : Fin 3, chainRoot d4ChainA2 i j + chainRoot d4ChainA2 j k =
    chainRoot d4ChainA2 i k := by
  decide +kernel

theorem d4LRep_bijective (L : Type) [Field L] : Function.Bijective (d4A2Rep L) :=
  ⟨d4A2Rep_injective, d4A2Rep_surjective⟩

@[expose] def d4LEquiv (L : Type) [Field L] :
    SL(3, L) ≃* subsystemGroup Tag.D4 L d4SuppA2 :=
  (MulEquiv.ofBijective (d4A2Rep L) (d4LRep_bijective L)).symm

@[expose] def d4LRho (L : Type) [Field L] : SL(3, L) →* ModGL Tag.D4 L :=
  (subsystemGroup Tag.D4 L d4SuppA2).subtype.comp (d4LEquiv L).toMonoidHom

variable {L : Type} [Field L]

theorem d4LRep_d4LEquiv (X : SL(3, L)) : d4A2Rep L (d4LEquiv L X) = X :=
  (MulEquiv.ofBijective (d4A2Rep L) (d4LRep_bijective L)).apply_symm_apply X

theorem d4LRho_d4LRep {g : ModGL Tag.D4 L} (hg : g ∈ subsystemGroup Tag.D4 L d4SuppA2) :
    d4LRho L (d4A2Rep L ⟨g, hg⟩) = g := by
  have h := (MulEquiv.ofBijective (d4A2Rep L) (d4LRep_bijective L)).symm_apply_apply
    (⟨g, hg⟩ : subsystemGroup Tag.D4 L d4SuppA2)
  exact congrArg Subtype.val h

theorem d4LRho_mem (X : SL(3, L)) : d4LRho L X ∈ subsystemGroup Tag.D4 L d4SuppA2 :=
  (d4LEquiv L X).2

theorem d4LMat_d4LRho (X : SL(3, L)) :
    d4A2Mat (d4LRho L X) = (X : Matrix (Fin 3) (Fin 3) L) :=
  congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) (d4LRep_d4LEquiv X)

theorem d4LRho_injective : Function.Injective (d4LRho L) := by
  intro X Y h
  apply Subtype.ext
  rw [← d4LMat_d4LRho X, ← d4LMat_d4LRho Y, h]

theorem d4LRho_range : (d4LRho L).range = subsystemGroup Tag.D4 L d4SuppA2 := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ d4LRho_mem X) fun g hg => ?_
  exact ⟨d4A2Rep L ⟨g, hg⟩, d4LRho_d4LRep hg⟩

theorem d4LRho_transvection (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, d4LRho L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.D4 L (chainRoot d4ChainA2 i j) ((ε : L) * t) := by
  obtain ⟨ε₀, hε₀, hfam⟩ := d4A2RootFamily_all (K := L) i j hij
  obtain ⟨ε, hε⟩ : ∃ ε : Lˣ, (ε : L) = (ε₀ : L) := by
    rcases hε₀ with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩
  have hεε : (ε : L) * (ε : L) = 1 := by
    rw [hε]
    rcases hε₀ with rfl | rfl <;> simp
  refine ⟨ε, fun s => ?_⟩
  have hmem := pinnedX_mem_d4A2Group (chainRootA2_mem_parabolicRoots hij) ((ε : L) * s)
  have hrep : d4A2Rep L ⟨pinnedX Tag.D4 L (chainRoot d4ChainA2 i j) ((ε : L) * s), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij s := by
    apply Subtype.ext
    rw [coe_d4A2Rep, hfam, CFSG.LinearGroups.coe_transvection, ← hε, ← mul_assoc, hεε, one_mul]
  rw [← hrep]
  exact d4LRho_d4LRep hmem

theorem d4LRho_diag (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    d4LRho L A ∈ torusGroup Tag.D4 L := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h01 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
  set ua : Lˣ := Units.mk0 _ h0 with hua
  set ub : Lˣ := Units.mk0 _ h01 with hub
  have hrep : d4A2Rep L ⟨d4A2TorusElt ua ub, d4A2TorusElt_mem ua ub⟩ = A := by
    apply Subtype.ext
    rw [coe_d4A2Rep, d4A2Mat_d4A2TorusElt, hdiag]
    have h22 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 =
        ((A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hJ : d4LRho L A = d4A2TorusElt ua ub := by
    rw [← hrep]
    exact d4LRho_d4LRep (d4A2TorusElt_mem ua ub)
  rw [hJ]
  have hmem : d4A2TorusElt ua ub ∈ subsystemGroup Tag.D4 L d4SuppA2 ⊓ torusGroup Tag.D4 L :=
    (D4_native_A2_root_subgroup_faithful_SL3 L).2.2.2.2.2.2.2.2.2.1 _ |>.2 ⟨ua, ub, rfl⟩
  exact hmem.2

theorem d4L_frame :
    IsA2Frame (d4LRho L) (fun i j => chainRoot d4ChainA2 i j) where
  injective := d4LRho_injective
  isRoot i j hij := (chainRootA2_mem_parabolicRoots hij).1
  neg i j := chainRoot_swap d4ChainA2 i j
  add i j k := d4L_chain_add i j k
  transv i j hij := d4LRho_transvection i j hij
  range := by
    rw [d4LRho_range, subsystemGroup_eq_rootSpan]
    congr 1
    rw [parabolicRoots_d4SuppA2]
    ext r
    constructor
    · intro hr
      obtain ⟨k, l, hkl, hr'⟩ : ∃ k l : Fin 3, k ≠ l ∧ chainRoot d4ChainA2 k l = r := by
        simp only [d4A2Sigma, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨0, 1, by decide, chainRootA2_values.1⟩
        · exact ⟨1, 0, by decide, chainRootA2_values.2.2.1⟩
        · exact ⟨1, 2, by decide, chainRootA2_values.2.1⟩
        · exact ⟨2, 1, by decide, chainRootA2_values.2.2.2⟩
        · exact ⟨0, 2, by decide, by rw [← d4L_chain_add 0 1 2, chainRootA2_values.1,
            chainRootA2_values.2.1]⟩
        · exact ⟨2, 0, by decide, by
            rw [chainRoot_swap d4ChainA2 0 2, ← d4L_chain_add 0 1 2, chainRootA2_values.1,
              chainRootA2_values.2.1]⟩
      exact ⟨k, l, hkl, hr'.symm⟩
    · rintro ⟨k, l, hkl, rfl⟩
      rcases chainRootA2_cases k l hkl with h | h | h | h | h | h <;> rw [h] <;>
        simp [d4A2Sigma]
  diag A hA := d4LRho_diag A hA


end D4Frame

section D4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)

@[expose] def d4PairWord (l : List ℕ) : List (Fin Tag.D4.rank) :=
  l.map fun n => (⟨n % 4, Nat.mod_lt n (by decide)⟩ : Fin 4)

@[expose] def d4RootWords : Fin 4 → List ℕ :=
  ![[], [2, 1, 0, 2], [0, 2], [2, 3, 0, 2]]

set_option maxRecDepth 100000 in
theorem d4RootWords_spec : ∀ j : Fin 4,
    (d4PairWord (d4RootWords j)).foldr (reflect Tag.D4) (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) =
      (Pi.single (j : Fin Tag.D4.rank) 1 : Fin Tag.D4.rank → ℤ) := by
  decide +kernel

@[expose] def d4PairWords : List (List ℤ × List ℕ) :=
  [([-1, -1, -1, -1], [2, 1, 0, 2, 3, 2, 1, 0, 2]),
    ([-1, -1, -1, 0], [3, 2, 1, 0, 2, 3, 2, 1, 0, 2]),
    ([-1, 0, -1, -1], [2, 1, 0, 2, 3, 2, 1, 0, 2, 1]),
    ([-1, 0, -1, 0], [3, 2, 1, 0, 2, 3, 2, 1, 0, 2, 1]),
    ([0, 0, 1, 0], []),
    ([0, 0, 1, 1], [3]),
    ([0, 1, 1, 0], [1]),
    ([0, 1, 1, 1], [3, 1])]

set_option maxRecDepth 100000 in
theorem d4PairWords_spec : ∀ ent ∈ d4PairWords,
    (d4PairWord ent.2).foldr (reflect Tag.D4) (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) =
        (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) ∧
      (d4PairWord ent.2).foldr (reflect Tag.D4) (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) =
        toVec Tag.D4.rank ent.1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem d4PairWords_complete :
    ∀ l ∈ Tag.D4.artifactRoots,
      iform (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) (toVec Tag.D4.rank l) = -1 →
        l ∈ d4PairWords.map Prod.fst := by
  decide +kernel

theorem wordProd_smul_d4L (l : List (Fin Tag.D4.rank)) (v : Fin Tag.D4.rank → ℤ) :
    (coxeterSystem Tag.D4).wordProd l • v = l.foldr (reflect Tag.D4) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

section


theorem iform_self_D4 {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) : iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  have h1 : Tag.D4.symmetrizer j j = 1 := by
    change (1 : Matrix (Fin 4) (Fin 4) ℤ) j j = 1
    exact Matrix.one_apply_eq j
  rw [hj, h1, mul_one]

theorem exists_weyl_a2Pair_D4 {α β : Fin Tag.D4.rank → ℤ} (h : IsA2Pair α β) :
    ∃ v : WeylGroup Tag.D4, v • (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) = α ∧
      v • (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) = β := by
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 h.isRoot_fst
  set t := (coxeterSystem Tag.D4).wordProd (d4PairWord (d4RootWords j)) with ht
  have htj : t • (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) = Pi.single j 1 := by
    rw [ht, wordProd_smul_d4L]
    exact d4RootWords_spec j
  set u := w * t with hu
  have hu0 : u • (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) = α := by rw [hu, mul_smul, htj, hw]
  set β' := u⁻¹ • β with hβ'
  have hβ'r : IsRoot Tag.D4 β' := IsRoot.smul h.isRoot_snd u⁻¹
  have hform : iform (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) β' = -1 := by
    have e : iform (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) β' = iform α β := by
      rw [← iform_smul u, hu0, hβ', smul_inv_smul]
    have h2 := h.two_iform
    rw [iform_self_D4 h.isRoot_fst] at h2
    rw [e]
    omega
  obtain ⟨l, hl, hβ'l⟩ := isRoot_iff_exists_mem.1 hβ'r
  obtain ⟨ent, hent, hentl⟩ := List.mem_map.1 (d4PairWords_complete l hl (hβ'l ▸ hform))
  obtain ⟨h0, h2⟩ := d4PairWords_spec ent hent
  refine ⟨u * (coxeterSystem Tag.D4).wordProd (d4PairWord ent.2), ?_, ?_⟩
  · rw [mul_smul, wordProd_smul_d4L, h0, hu0]
  · rw [mul_smul, wordProd_smul_d4L, h2, hentl, ← hβ'l, hβ', smul_inv_smul]

end


section


theorem a2BlockToral_D4 : A2BlockToral Tag.D4 := by
  intro L _ _ hL α β hpair
  obtain ⟨v, h1, h2⟩ := exists_weyl_a2Pair_D4 hpair
  have hfr := (d4L_frame (L := L)).transport v
  have key := a2BlockAt_of_frame hL hfr
  have e1 : v • chainRoot d4ChainA2 0 1 = α := by rw [(chainRootA2_values).1]; exact h1
  have e2 : v • chainRoot d4ChainA2 1 2 = β := by rw [(chainRootA2_values).2.1]; exact h2
  simp only [e1, e2] at key
  exact key

end

end D4

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
