module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Flip
public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

structure Triple (Q : QuadraticForm K V) where
  a : HypPair Q
  b : HypPair Q
  c : HypPair Q
  ab : a.Orth b
  ac : a.Orth c
  bc : b.Orth c

namespace Triple

variable (T : Triple Q)

@[expose] def e : Fin 3 → V := ![T.a.e, T.b.e, T.c.e]

@[expose] def f : Fin 3 → V := ![T.a.f, T.b.f, T.c.f]

theorem polar_ee (i j : Fin 3) : polar Q (T.e i) (T.e j) = 0 := by
  have h1 := T.ab.ee
  have h2 := T.ac.ee
  have h3 := T.bc.ee
  have h1' : polar Q T.b.e T.a.e = 0 := by rw [polar_comm]; exact h1
  have h2' : polar Q T.c.e T.a.e = 0 := by rw [polar_comm]; exact h2
  have h3' : polar Q T.c.e T.b.e = 0 := by rw [polar_comm]; exact h3
  fin_cases i <;> fin_cases j <;> simp [e, h1, h2, h3, h1', h2', h3', T.a.Q_e, T.b.Q_e, T.c.Q_e]

theorem polar_ff (i j : Fin 3) : polar Q (T.f i) (T.f j) = 0 := by
  have h1 := T.ab.ff
  have h2 := T.ac.ff
  have h3 := T.bc.ff
  have h1' : polar Q T.b.f T.a.f = 0 := by rw [polar_comm]; exact h1
  have h2' : polar Q T.c.f T.a.f = 0 := by rw [polar_comm]; exact h2
  have h3' : polar Q T.c.f T.b.f = 0 := by rw [polar_comm]; exact h3
  fin_cases i <;> fin_cases j <;> simp [f, h1, h2, h3, h1', h2', h3', T.a.Q_f, T.b.Q_f, T.c.Q_f]

theorem polar_ef (i j : Fin 3) : polar Q (T.e i) (T.f j) = if i = j then 1 else 0 := by
  have h1 := T.ab.ef
  have h2 := T.ac.ef
  have h3 := T.bc.ef
  have h1' : polar Q T.b.e T.a.f = 0 := by rw [polar_comm]; exact T.ab.fe
  have h2' : polar Q T.c.e T.a.f = 0 := by rw [polar_comm]; exact T.ac.fe
  have h3' : polar Q T.c.e T.b.f = 0 := by rw [polar_comm]; exact T.bc.fe
  fin_cases i <;> fin_cases j <;> simp [e, f, h1, h2, h3, h1', h2', h3', T.a.polar_ef,
    T.b.polar_ef, T.c.polar_ef]

theorem polar_fe (i j : Fin 3) : polar Q (T.f i) (T.e j) = if i = j then 1 else 0 := by
  rw [polar_comm, polar_ef]
  simp [eq_comm]

@[expose] def incl : ((Fin 3 → K) × (Fin 3 → K)) →ₗ[K] V where
  toFun z := z.1 0 • T.e 0 + z.1 1 • T.e 1 + z.1 2 • T.e 2 +
    (z.2 0 • T.f 0 + z.2 1 • T.f 1 + z.2 2 • T.f 2)
  map_add' z z' := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul]
    abel
  map_smul' c z := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add]

@[expose] def coords : V →ₗ[K] ((Fin 3 → K) × (Fin 3 → K)) where
  toFun x := (fun i => polar Q x (T.f i), fun i => polar Q x (T.e i))
  map_add' x y := by
    ext i <;> simp [polar_add_left]
  map_smul' c x := by
    ext i <;> simp

theorem coords_incl (z : (Fin 3 → K) × (Fin 3 → K)) : T.coords (T.incl z) = z := by
  obtain ⟨u, w⟩ := z
  ext i
  · fin_cases i <;> simp [coords, incl, polar_add_left, T.polar_ee, T.polar_ef, T.polar_fe,
      T.polar_ff]
  · fin_cases i <;> simp [coords, incl, polar_add_left, T.polar_ee, T.polar_ef, T.polar_fe,
      T.polar_ff]

@[expose] def embLin (S : Module.End K ((Fin 3 → K) × (Fin 3 → K))) : V →ₗ[K] V :=
  LinearMap.id + T.incl ∘ₗ (S - 1) ∘ₗ T.coords

theorem embLin_apply (S : Module.End K ((Fin 3 → K) × (Fin 3 → K))) (x : V) :
    T.embLin S x = x + T.incl (S (T.coords x) - T.coords x) := by
  simp [embLin]

theorem embLin_one : T.embLin 1 = 1 := by
  ext x
  simp [embLin_apply]

theorem embLin_mul (S S' : Module.End K ((Fin 3 → K) × (Fin 3 → K))) :
    T.embLin (S * S') = T.embLin S * T.embLin S' := by
  ext x
  simp only [embLin_apply, Module.End.mul_apply, map_add, coords_incl, map_sub]
  abel

theorem embLin_incl (S : Module.End K ((Fin 3 → K) × (Fin 3 → K)))
    (z : (Fin 3 → K) × (Fin 3 → K)) : T.embLin S (T.incl z) = T.incl (S z) := by
  rw [embLin_apply, coords_incl, map_sub]
  abel

theorem embLin_injective {S S' : Module.End K ((Fin 3 → K) × (Fin 3 → K))}
    (h : ∀ x, T.embLin S x = T.embLin S' x) : S = S' := by
  refine LinearMap.ext fun z => ?_
  have := h (T.incl z)
  rw [embLin_incl, embLin_incl] at this
  have := congrArg T.coords this
  rwa [coords_incl, coords_incl] at this

@[expose] noncomputable def embHom {G : Type*} [Group G]
    (ρ : G →* Module.End K ((Fin 3 → K) × (Fin 3 → K))) : G →* (V ≃ₗ[K] V) where
  toFun g := LinearEquiv.ofLinearMap (T.embLin (ρ g)) (T.embLin (ρ g⁻¹))
    (by
      rw [← Module.End.mul_eq_comp, ← embLin_mul, ← map_mul, mul_inv_cancel, map_one, embLin_one]
      rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← embLin_mul, ← map_mul, inv_mul_cancel, map_one, embLin_one]
      rfl)
  map_one' := by
    refine LinearEquiv.ext fun x => ?_
    simp [embLin_one]
  map_mul' g h := by
    refine LinearEquiv.ext fun x => ?_
    simp [embLin_mul]

theorem embHom_apply {G : Type*} [Group G] (ρ : G →* Module.End K ((Fin 3 → K) × (Fin 3 → K)))
    (g : G) (x : V) : T.embHom ρ g x = T.embLin (ρ g) x :=
  rfl

variable (K) in
@[expose] noncomputable def Tmap : SL(3, K) →* Module.End K ((Fin 3 → K) × (Fin 3 → K)) where
  toFun g := LinearMap.prodMap (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K))
    (Matrix.mulVecLin (((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ))
  map_one' := by
    ext z <;> simp
  map_mul' g h := by
    refine LinearMap.ext fun z => ?_
    rw [Module.End.mul_apply]
    simp only [LinearMap.prodMap_apply, Matrix.mulVecLin_apply, Matrix.SpecialLinearGroup.coe_mul,
      _root_.mul_inv_rev, Matrix.transpose_mul, Matrix.mulVec_mulVec]

@[expose] noncomputable def theta : SL(3, K) →* (V ≃ₗ[K] V) :=
  T.embHom (Tmap K)

theorem theta_apply (g : SL(3, K)) (x : V) :
    T.theta g x = x + T.incl (Tmap K g (T.coords x) - T.coords x) := by
  rw [theta, embHom_apply, embLin_apply]

theorem theta_injective : Function.Injective (T.theta (K := K)) := by
  intro g h hgh
  have h1 := T.embLin_injective (S := Tmap K g) (S' := Tmap K h)
    (fun x => LinearEquiv.congr_fun hgh x)
  apply Subtype.ext
  ext i j
  have h2 := congrArg (fun S => (S (Pi.single j 1, 0)).1 i) h1
  simpa [Tmap, Matrix.mulVec, dotProduct, Pi.single_apply] using h2

@[expose] def frame01 : Frame Q := ⟨T.a, T.b, T.ab⟩

@[expose] def frame12 : Frame Q := ⟨T.b, T.c, T.bc⟩

theorem blockMat_three_zero (A : Matrix (Fin 2) (Fin 2) K) :
    CFSG.ClassicalInvolution.Phan.blockMat 3 0 A =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.ClassicalInvolution.Phan.blockMat_apply]

theorem blockMat_three_one (A : Matrix (Fin 2) (Fin 2) K) :
    CFSG.ClassicalInvolution.Phan.blockMat 3 1 A =
      !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.ClassicalInvolution.Phan.blockMat_apply]

theorem Tmap_blockSL_zero (A : SL(2, K)) (z : (Fin 3 → K) × (Fin 3 → K)) :
    Tmap K (blockSL K 3 2 0 (by omega) A) z =
      (![(A : Matrix (Fin 2) (Fin 2) K) 0 0 * z.1 0 + (A : Matrix (Fin 2) (Fin 2) K) 0 1 * z.1 1,
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 * z.1 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1 * z.1 1,
        z.1 2],
       ![(A : Matrix (Fin 2) (Fin 2) K) 1 1 * z.2 0 - (A : Matrix (Fin 2) (Fin 2) K) 1 0 * z.2 1,
        -(A : Matrix (Fin 2) (Fin 2) K) 0 1 * z.2 0 + (A : Matrix (Fin 2) (Fin 2) K) 0 0 * z.2 1,
        z.2 2]) := by
  have hinv : ((blockSL K 3 2 0 (by omega) A)⁻¹ : SL(3, K)) =
      blockSL K 3 2 0 (by omega) A⁻¹ := (map_inv _ A).symm
  have h1 : Tmap K (blockSL K 3 2 0 (by omega) A) z =
      (Matrix.mulVec (CFSG.ClassicalInvolution.Phan.blockMat 3 0
          (A : Matrix (Fin 2) (Fin 2) K)) z.1,
        Matrix.mulVec (CFSG.ClassicalInvolution.Phan.blockMat 3 0
          ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))ᵀ z.2) := by
    simp only [Tmap, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.prodMap_apply,
      Matrix.mulVecLin_apply]
    rw [hinv, coe_blockSL, coe_blockSL]
  rw [h1, blockMat_three_zero, blockMat_three_zero]
  ext i <;> fin_cases i
  all_goals simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

theorem theta_blockSL_zero (A : SL(2, K)) :
    T.theta (blockSL K 3 2 0 (by omega) A) = T.frame01.swap.La A := by
  refine LinearEquiv.ext fun x => ?_
  rw [theta_apply, Tmap_blockSL_zero, Frame.La_apply]
  congr 1
  simp [incl, coords, Frame.incl_apply, Frame.coords_apply, Frame.swap, frame01, e, f,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]
  module

theorem Tmap_blockSL_one (A : SL(2, K)) (z : (Fin 3 → K) × (Fin 3 → K)) :
    Tmap K (blockSL K 3 2 1 (by omega) A) z =
      (![z.1 0,
        (A : Matrix (Fin 2) (Fin 2) K) 0 0 * z.1 1 + (A : Matrix (Fin 2) (Fin 2) K) 0 1 * z.1 2,
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 * z.1 1 + (A : Matrix (Fin 2) (Fin 2) K) 1 1 * z.1 2],
       ![z.2 0,
        (A : Matrix (Fin 2) (Fin 2) K) 1 1 * z.2 1 - (A : Matrix (Fin 2) (Fin 2) K) 1 0 * z.2 2,
        -(A : Matrix (Fin 2) (Fin 2) K) 0 1 * z.2 1 +
          (A : Matrix (Fin 2) (Fin 2) K) 0 0 * z.2 2]) := by
  have hinv : ((blockSL K 3 2 1 (by omega) A)⁻¹ : SL(3, K)) =
      blockSL K 3 2 1 (by omega) A⁻¹ := (map_inv _ A).symm
  have h1 : Tmap K (blockSL K 3 2 1 (by omega) A) z =
      (Matrix.mulVec (CFSG.ClassicalInvolution.Phan.blockMat 3 1
          (A : Matrix (Fin 2) (Fin 2) K)) z.1,
        Matrix.mulVec (CFSG.ClassicalInvolution.Phan.blockMat 3 1
          ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))ᵀ z.2) := by
    simp only [Tmap, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.prodMap_apply,
      Matrix.mulVecLin_apply]
    rw [hinv, coe_blockSL, coe_blockSL]
  rw [h1, blockMat_three_one, blockMat_three_one]
  ext i <;> fin_cases i
  all_goals simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

theorem theta_blockSL_one (A : SL(2, K)) :
    T.theta (blockSL K 3 2 1 (by omega) A) = T.frame12.swap.La A := by
  refine LinearEquiv.ext fun x => ?_
  rw [theta_apply, Tmap_blockSL_one, Frame.La_apply]
  congr 1
  simp [incl, coords, Frame.incl_apply, Frame.coords_apply, Frame.swap, frame12, e, f,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]
  module

theorem map_B12 : (B12 K).map T.theta = T.frame01.swap.La.range := by
  rw [B12, ← MonoidHom.range_comp]
  congr 1
  ext A : 1
  exact T.theta_blockSL_zero A

theorem map_B23 : (B23 K).map T.theta = T.frame12.swap.La.range := by
  rw [B23, ← MonoidHom.range_comp]
  congr 1
  ext A : 1
  exact T.theta_blockSL_one A

theorem range_theta :
    T.theta.range = T.frame01.swap.La.range ⊔ T.frame12.swap.La.range := by
  rw [← map_B12, ← map_B23, ← Subgroup.map_sup, MonoidHom.range_eq_map, ← B12_sup_B23 (K := K)]

@[expose] def frame02 : Frame Q := ⟨T.a, T.c, T.ac⟩

@[expose] noncomputable def outerElt (A : SL(2, K)) : SL(3, K) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) K) 0 0, 0, (A : Matrix (Fin 2) (Fin 2) K) 0 1;
      0, 1, 0; (A : Matrix (Fin 2) (Fin 2) K) 1 0, 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    simp [Matrix.det_fin_three]
    linear_combination h⟩

theorem coe_outerElt (A : SL(2, K)) :
    ((outerElt A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      !![(A : Matrix (Fin 2) (Fin 2) K) 0 0, 0, (A : Matrix (Fin 2) (Fin 2) K) 0 1;
        0, 1, 0; (A : Matrix (Fin 2) (Fin 2) K) 1 0, 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1] :=
  rfl

theorem outerElt_one : outerElt (1 : SL(2, K)) = 1 := by
  apply Subtype.ext
  rw [coe_outerElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem outerElt_mul (A B : SL(2, K)) : outerElt (A * B) = outerElt A * outerElt B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_outerElt, coe_outerElt, coe_outerElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three]

variable (K) in
@[expose] noncomputable def outerBlock : SL(2, K) →* SL(3, K) where
  toFun := outerElt
  map_one' := outerElt_one
  map_mul' := outerElt_mul

theorem coe_outerBlock (A : SL(2, K)) :
    ((outerBlock K A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      !![(A : Matrix (Fin 2) (Fin 2) K) 0 0, 0, (A : Matrix (Fin 2) (Fin 2) K) 0 1;
        0, 1, 0; (A : Matrix (Fin 2) (Fin 2) K) 1 0, 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1] :=
  rfl

theorem Tmap_outerBlock (A : SL(2, K)) (z : (Fin 3 → K) × (Fin 3 → K)) :
    Tmap K (outerBlock K A) z =
      (![(A : Matrix (Fin 2) (Fin 2) K) 0 0 * z.1 0 + (A : Matrix (Fin 2) (Fin 2) K) 0 1 * z.1 2,
        z.1 1,
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 * z.1 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1 * z.1 2],
       ![(A : Matrix (Fin 2) (Fin 2) K) 1 1 * z.2 0 - (A : Matrix (Fin 2) (Fin 2) K) 1 0 * z.2 2,
        z.2 1,
        -(A : Matrix (Fin 2) (Fin 2) K) 0 1 * z.2 0 +
          (A : Matrix (Fin 2) (Fin 2) K) 0 0 * z.2 2]) := by
  have hinv : ((outerBlock K A)⁻¹ : SL(3, K)) = outerBlock K A⁻¹ := (map_inv _ A).symm
  have h1 : Tmap K (outerBlock K A) z =
      (Matrix.mulVec ((outerBlock K A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) z.1,
        Matrix.mulVec (((outerBlock K A⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K))ᵀ z.2) := by
    simp only [Tmap, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.prodMap_apply,
      Matrix.mulVecLin_apply]
    rw [hinv]
  rw [h1, coe_outerBlock, coe_outerBlock]
  ext i <;> fin_cases i
  all_goals simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

theorem theta_outerBlock (A : SL(2, K)) :
    T.theta (outerBlock K A) = T.frame02.swap.La A := by
  refine LinearEquiv.ext fun x => ?_
  rw [theta_apply, Tmap_outerBlock, Frame.La_apply]
  congr 1
  simp [incl, coords, Frame.incl_apply, Frame.coords_apply, Frame.swap, frame02, e, f,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]
  module

theorem coe_neg_one_sl2 : (((-1 : SL(2, K)) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
  simp [Matrix.SpecialLinearGroup.coe_neg]

theorem blockSL_neg_one_mul :
    blockSL K 3 2 0 (by omega) (-1) * blockSL K 3 2 1 (by omega) (-1) = outerBlock K (-1) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_blockSL, coe_outerBlock,
    blockMat_three_zero, blockMat_three_one, coe_neg_one_sl2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def swapPair (P : HypPair Q) : HypPair Q := ⟨P.f, P.e, P.Q_f, P.Q_e, HypPair.polar_fe P⟩

theorem orth_swapPair_left {P P' : HypPair Q} (h : P.Orth P') : (swapPair P).Orth P' :=
  ⟨h.fe, h.ff, h.ee, h.ef⟩

theorem orth_swapPair_right {P P' : HypPair Q} (h : P.Orth P') : P.Orth (swapPair P') :=
  ⟨h.ef, h.ee, h.ff, h.fe⟩

@[expose] def flipA : Triple Q :=
  ⟨swapPair T.a, T.b, T.c, orth_swapPair_left T.ab, orth_swapPair_left T.ac, T.bc⟩

@[expose] def flipB : Triple Q :=
  ⟨T.a, swapPair T.b, T.c, orth_swapPair_right T.ab, T.ac, orth_swapPair_left T.bc⟩

@[expose] def flipC : Triple Q :=
  ⟨T.a, T.b, swapPair T.c, T.ab, orth_swapPair_right T.ac, orth_swapPair_right T.bc⟩

theorem flipA_frame01_swap : T.flipA.frame01.swap = T.frame01.flip := rfl

theorem flipA_frame12 : T.flipA.frame12 = T.frame12 := rfl

theorem flipB_frame01_swap : T.flipB.frame01.swap = T.frame01 := rfl

theorem flipB_frame12_swap : T.flipB.frame12.swap = T.frame12.flip := rfl

theorem flipC_frame01_swap : T.flipC.frame01.swap = T.frame01.swap := rfl

theorem flipC_frame12_swap : T.flipC.frame12.swap = T.frame12 := rfl

theorem exists_triple_theta {L₁ L₂ : Subgroup (V ≃ₗ[K] V)}
    (h₁ : L₁ = T.frame01.La.range ∨ L₁ = T.frame01.swap.La.range)
    (h₂ : L₂ = T.frame12.La.range ∨ L₂ = T.frame12.swap.La.range) :
    ∃ T' : Triple Q, (B12 K).map T'.theta = L₁ ∧ (B23 K).map T'.theta = L₂ := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact ⟨T.flipB, T.flipB.map_B12, by
      rw [T.flipB.map_B23, flipB_frame12_swap, Frame.La_range_flip]⟩
  · exact ⟨T.flipA, by rw [T.flipA.map_B12, flipA_frame01_swap, Frame.La_range_flip],
      T.flipA.map_B23⟩
  · exact ⟨T.flipC, T.flipC.map_B12, T.flipC.map_B23⟩
  · exact ⟨T, T.map_B12, T.map_B23⟩

theorem exists_theta {L₁ L₂ : Subgroup (V ≃ₗ[K] V)}
    (h₁ : L₁ = T.frame01.La.range ∨ L₁ = T.frame01.swap.La.range)
    (h₂ : L₂ = T.frame12.La.range ∨ L₂ = T.frame12.swap.La.range) :
    ∃ θ : SL(3, K) →* (V ≃ₗ[K] V), Function.Injective θ ∧ θ.range = L₁ ⊔ L₂ ∧
      (B12 K).map θ = L₁ ∧ (B23 K).map θ = L₂ := by
  obtain ⟨T', e1, e2⟩ := T.exists_triple_theta h₁ h₂
  refine ⟨T'.theta, T'.theta_injective, ?_, e1, e2⟩
  rw [← e1, ← e2, ← Subgroup.map_sup, MonoidHom.range_eq_map, ← B12_sup_B23 (K := K)]

theorem La_neg_one_mul_eq :
    T.frame01.swap.La (-1) * T.frame12.swap.La (-1) = T.frame02.swap.La (-1) := by
  rw [← T.theta_blockSL_zero, ← T.theta_blockSL_one, ← map_mul, blockSL_neg_one_mul,
    theta_outerBlock]

theorem La_range_le_range_theta : T.frame02.swap.La.range ≤ T.theta.range := by
  rintro _ ⟨A, rfl⟩
  exact ⟨outerBlock K A, T.theta_outerBlock A⟩

end Triple

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
