module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverShape
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelTransport

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal OrthogonalTail OrthogonalSplit
open CFSG.LieType.Universal.Spin
open scoped commutatorElement

section Tail

variable {K : Type*} [Field K] [CharP K 2]

@[expose] def binEquiv [Finite K] (hK : Nat.card K = 2) : ZMod 2 ≃+* K :=
  RingEquiv.ofBijective (castTwo K) (castTwo_bijective hK)

theorem binEquiv_apply [Finite K] (hK : Nat.card K = 2) (a : ZMod 2) :
    binEquiv hK a = castTwo K a :=
  rfl

theorem castTwo_binEquiv_symm [Finite K] (hK : Nat.card K = 2) (x : K) :
    castTwo K ((binEquiv hK).symm x) = x :=
  (binEquiv hK).apply_symm_apply x

theorem binEquiv_symm_castTwo [Finite K] (hK : Nat.card K = 2) (a : ZMod 2) :
    (binEquiv hK).symm (castTwo K a) = a :=
  (binEquiv hK).symm_apply_apply a

theorem eq_zero_or_eq_one [Finite K] (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  obtain ⟨a, rfl⟩ := (binEquiv hK).surjective x
  fin_cases a
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

variable (K) in
theorem polar_binTail (a b : Fin 2 → K) :
    polar (minusTailForm K 1 1) a b = a 0 * b 1 + a 1 * b 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [polar, minusTailForm_apply, minusTailForm_apply, minusTailForm_apply]
  simp only [Pi.add_apply]
  linear_combination (a 0 * b 0 + a 1 * b 1) * h2

theorem binTail_irreducible [Finite K] (hK : Nat.card K = 2) (s : K) : s ^ 2 + 1 * s + 1 ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rcases eq_zero_or_eq_one hK s with rfl | rfl
  · simp
  · intro h
    have h3 : (1 : K) = 0 := by linear_combination h - h2
    exact one_ne_zero h3

theorem binTail_anisotropic [Finite K] (hK : Nat.card K = 2) :
    (minusTailForm K 1 1).Anisotropic :=
  anisotropic_minusTailForm (binTail_irreducible hK)

theorem binTail_nondegenerate [Finite K] (hK : Nat.card K = 2) :
    (polarBilin (minusTailForm K 1 1)).Nondegenerate :=
  nondegenerate_minusTailForm (binTail_irreducible hK)

omit [CharP K 2] in
theorem binTail_one : minusTailForm K 1 1 ![1, 0] = 1 := by
  rw [minusTailForm_apply]
  simp

omit [CharP K 2] in
theorem binTail_omega : minusTailForm K 1 1 ![0, 1] = 1 := by
  rw [minusTailForm_apply]
  simp

variable (K) in
@[expose] def tailRot : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun a := ![a 1, a 0 + a 1]
  invFun a := ![a 0 + a 1, a 0]
  map_add' a b := by
    ext i
    fin_cases i
    · rfl
    · simp only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply]
      ring
  map_smul' t a := by
    ext i
    fin_cases i
    · rfl
    · simp only [Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      ring
  left_inv a := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    ext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination a 1 * h2
  right_inv a := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    ext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination a 0 * h2

theorem tailRot_apply_zero (a : Fin 2 → K) : tailRot K a 0 = a 1 :=
  rfl

theorem tailRot_apply_one (a : Fin 2 → K) : tailRot K a 1 = a 0 + a 1 :=
  rfl

theorem tailRot_mem_orthogonalGroup :
    tailRot K ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K 1 1) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun a => ?_
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [minusTailForm_apply, minusTailForm_apply, tailRot_apply_zero, tailRot_apply_one]
  linear_combination (a 0 * a 1 + a 1 ^ 2) * h2

end Tail

section Weyl

variable {K : Type*} [Field K] [CharP K 2] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

theorem shortWeyl_hypPairT_apply (i : Fin r) {a₀ : A} (ha₀ : qA a₀ = 1)
    (v : (Fin r ⊕ Fin r → K) × A) :
    shortWeyl (hypPairT r qA i) ((0 : Fin r ⊕ Fin r → K), a₀) v =
      (fun c => v.1 (Equiv.swap (Sum.inl i) (Sum.inr i) c), v.2 + polar qA v.2 a₀ • a₀) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hneg : ∀ x : K, -x = x := fun x => by linear_combination -x * h2
  set P := hypPairT r qA i with hP
  have ha : ((0 : Fin r ⊕ Fin r → K), a₀) ∈ P.perp := tail_mem_perp_hypPairT i a₀
  have hd : quadTail r qA ((0 : Fin r ⊕ Fin r → K), a₀) = 1 := by rw [quadTail_tail, ha₀]
  have hd0 : quadTail r qA ((0 : Fin r ⊕ Fin r → K), a₀) ≠ 0 := by rw [hd]; exact one_ne_zero
  have hpf : polar (quadTail r qA) v P.f = v.1 (Sum.inl i) := by
    rw [hypPairT_f, polar_hypVec, Sum.swap_inr]
  have hpe : polar (quadTail r qA) v P.e = v.1 (Sum.inr i) := by
    rw [hypPairT_e, polar_hypVec, Sum.swap_inl]
  have hpa : polar (quadTail r qA) (P.proj v) ((0 : Fin r ⊕ Fin r → K), a₀) =
      polar qA v.2 a₀ := by
    rw [HypPair.proj, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left,
      (HypPair.mem_perp.1 ha).1, (HypPair.mem_perp.1 ha).2, polar_quadTail, polar_zero_right]
    simp
  conv_lhs => rw [P.eq_add_proj v]
  rw [map_add, map_add, map_smul, map_smul, shortWeyl_e P ha hd0, shortWeyl_f P ha hd0,
    shortWeyl_perp P ha hd0 (P.proj_mem_perp v), hd, hpf, hpe, hpa, inv_one, mul_one]
  simp only [hneg, one_smul, HypPair.proj, hpf, hpe]
  refine Prod.ext (funext fun c => ?_) ?_
  · simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, sub_zero, hP,
      hypPairT_e, hypPairT_f, hypVec]
    rcases c with k | k
    · by_cases hk : k = i
      · subst hk
        simp [Equiv.swap_apply_left]
      · have h1 : Equiv.swap (Sum.inl i) (Sum.inr i) (Sum.inl k : Fin r ⊕ Fin r) = Sum.inl k :=
          Equiv.swap_apply_of_ne_of_ne (by simpa using hk) (by simp)
        simp [h1, hk]
    · by_cases hk : k = i
      · subst hk
        simp [Equiv.swap_apply_right]
      · have h1 : Equiv.swap (Sum.inl i) (Sum.inr i) (Sum.inr k : Fin r ⊕ Fin r) = Sum.inr k :=
          Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hk)
        simp [h1, hk]
  · simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, hP, hypPairT_e, hypPairT_f, hypVec,
      smul_zero, add_zero, zero_add, sub_zero]
    rw [sub_eq_add_neg, ← neg_smul, hneg]

theorem shortWeyl_hypVec (i : Fin r) {a₀ : A} (ha₀ : qA a₀ = 1) (c : Fin r ⊕ Fin r) :
    shortWeyl (hypPairT r qA i) ((0 : Fin r ⊕ Fin r → K), a₀) (hypVec K A c) =
      hypVec K A (Equiv.swap (Sum.inl i) (Sum.inr i) c) := by
  rw [shortWeyl_hypPairT_apply i ha₀]
  refine Prod.ext (funext fun d => ?_) ?_
  · simp only [hypVec, Pi.single_apply, Equiv.swap_apply_eq_iff]
  · simp [hypVec]

end Weyl

section Levi

variable {K : Type*} [Field K] [CharP K 2] {r : ℕ}

theorem shortWeyl_mul_shortWeyl_eq_dMap (i : Fin r) :
    shortWeyl (hypPairT r (minusTailForm K 1 1) i) ((0 : Fin r ⊕ Fin r → K), ![1, 0]) *
        shortWeyl (hypPairT r (minusTailForm K 1 1) i) ((0 : Fin r ⊕ Fin r → K), ![0, 1]) =
      dMap 1 (tailRot K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, shortWeyl_hypPairT_apply i binTail_one,
    shortWeyl_hypPairT_apply i binTail_omega, dMap_apply]
  refine Prod.ext ?_ ?_
  · funext c
    simp only [Equiv.swap_apply_self]
    rcases c with k | k <;> simp
  · ext j
    fin_cases j
    · simp only [Fin.zero_eta, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        polar_binTail, Matrix.cons_val_zero, Matrix.cons_val_one, tailRot_apply_zero]
      linear_combination v.2 0 * h2
    · simp only [Fin.mk_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        polar_binTail, Matrix.cons_val_zero, Matrix.cons_val_one, tailRot_apply_one]
      ring

variable {A : Type*} [AddCommGroup A] [Module K A] {qA : QuadraticForm K A}

omit [CharP K 2] in
theorem dBlock_eq_levi (D : GL (Fin r) K) : dBlock D = levi r K D := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  rw [toMatrix'_dBlock, toMatrix'_levi_eq]

omit [CharP K 2] in
theorem dMap_one_eq_prodHom (D : GL (Fin r) K) :
    dMap D (1 : A ≃ₗ[K] A) = prodHom A (levi r K D) := by
  rw [dMap, prodHom_apply, dBlock_eq_levi]
  rfl

theorem dMap_one_mem_orthElementaryGroup (hr : 3 ≤ r) {D : GL (Fin r) K}
    (hD : (D : Matrix (Fin r) (Fin r) K).det = 1) :
    dMap D (1 : A ≃ₗ[K] A) ∈ orthElementaryGroup (quadTail r qA) := by
  rw [dMap_one_eq_prodHom]
  have h1 : levi r K D ∈ rootSupr r K := by
    rw [← (orthogonal_geometry_split_root_generation (K := K) hr).1]
    have h := levi_toGL_mem_orthElementaryGroup hr ⟨(D : Matrix (Fin r) (Fin r) K), hD⟩
    have hD' : SpecialLinearGroup.toGL ⟨(D : Matrix (Fin r) (Fin r) K), hD⟩ = D := Units.ext rfl
    rwa [hD'] at h
  exact tailRootSupr_le (map_rootSupr_le ⟨_, h1, rfl⟩)

omit [CharP K 2] in
theorem uMap_mem_orthElementaryGroup (L : Fin r → A) {C : Matrix (Fin r) (Fin r) K}
    (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0) :
    uMap qA L C ∈ orthElementaryGroup (quadTail r qA) := by
  have h := dMap_mul_uMap_mem_tailUnipotent (qA := qA) (D := 1)
    (fun i j h => by rw [Units.val_one]; exact Matrix.one_apply_ne (ne_of_gt h))
    (fun i => by simp) L hC hd
  rw [dMap_one_one, one_mul] at h
  exact tailUnipotent_le h

omit [CharP K 2] in
theorem uMap_hypVec_inr_snd (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K) (j : Fin r) :
    (uMap qA L C (hypVec K A (.inr j))).2 = L j := by
  rw [uMap_apply, uLin_apply_snd]
  simp [hypVec, Pi.single_apply]

omit [CharP K 2] in
theorem uMap_injective {L L' : Fin r → A} {C C' : Matrix (Fin r) (Fin r) K}
    (h : uMap qA L C = uMap qA L' C') : L = L' ∧ C = C' := by
  have h' : dMap 1 1 * uMap qA L C = dMap 1 1 * uMap qA L' C' := by rw [h]
  obtain ⟨-, -, hL, hC⟩ := dMap_uMap_injective h'
  exact ⟨hL, hC⟩

omit [CharP K 2] in
theorem dMap_eq_uMap {D : GL (Fin r) K} {L : Fin r → A} {C : Matrix (Fin r) (Fin r) K}
    (h : dMap D (1 : A ≃ₗ[K] A) = uMap qA L C) : D = 1 := by
  have h' : dMap D 1 * uMap qA 0 0 = dMap 1 1 * uMap qA L C := by
    rw [uMap_zero_zero, mul_one, dMap_one_one, one_mul, h]
  exact (dMap_uMap_injective h').1

omit [CharP K 2] in
theorem commutatorElement_uMap (L L' : Fin r → A) (C C' : Matrix (Fin r) (Fin r) K) :
    ⁅uMap qA L C, uMap qA L' C'⁆ = uMap qA 0 (crossMat qA L' L - crossMat qA L L') := by
  have key : uMap qA 0 (crossMat qA L' L - crossMat qA L L') * (uMap qA L' C' * uMap qA L C) =
      uMap qA L C * uMap qA L' C' := by
    rw [uMap_mul_uMap, uMap_mul_uMap, uMap_mul_uMap, zero_add, add_comm L' L]
    congr 1
    have h0 : crossMat qA (0 : Fin r → A) (L + L') = 0 := by
      ext i j
      simp [crossMat]
    simp only [mulParam, sMat_zero, add_comm L' L, h0, zero_add, sub_zero]
    abel
  rw [commutatorElement_def, show uMap qA L C * uMap qA L' C' * (uMap qA L C)⁻¹ *
      (uMap qA L' C')⁻¹ = uMap qA L C * uMap qA L' C' * (uMap qA L' C' * uMap qA L C)⁻¹ by group,
    ← key, mul_inv_cancel_right]

omit [CharP K 2] in
theorem uMap_zero_mul_uMap_zero (C C' : Matrix (Fin r) (Fin r) K) :
    uMap qA (0 : Fin r → A) C * uMap qA 0 C' = uMap qA 0 (C + C') := by
  rw [uMap_mul_uMap, add_zero]
  congr 1
  have h0 : crossMat qA (0 : Fin r → A) 0 = 0 := by
    ext i j
    simp [crossMat]
  simp only [mulParam, sMat_zero, h0, add_zero, sub_zero, zero_add]

end Levi

section Coords

variable {K : Type*} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 2) {r : ℕ}

@[expose] def binCoords (L : Fin r → Fin 2 → K) : (Fin r → ZMod 2) × (Fin r → ZMod 2) :=
  (fun j => (binEquiv hK).symm (L j 0), fun j => (binEquiv hK).symm (L j 1))

@[expose] def ofBinCoords (w : (Fin r → ZMod 2) × (Fin r → ZMod 2)) : Fin r → Fin 2 → K :=
  fun j => ![castTwo K (w.1 j), castTwo K (w.2 j)]

theorem binCoords_ofBinCoords (w : (Fin r → ZMod 2) × (Fin r → ZMod 2)) :
    binCoords hK (ofBinCoords w : Fin r → Fin 2 → K) = w := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · exact binEquiv_symm_castTwo hK _
  · exact binEquiv_symm_castTwo hK _

theorem binCoords_add (L L' : Fin r → Fin 2 → K) :
    binCoords hK (L + L') = binCoords hK L + binCoords hK L' := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    simp only [binCoords, Pi.add_apply, map_add, Prod.fst_add, Prod.snd_add]

theorem binCoords_injective : Function.Injective (binCoords hK (r := r)) := by
  intro L L' h
  funext j i
  fin_cases i
  · exact (binEquiv hK).symm.injective (congrFun (congrArg Prod.fst h) j)
  · exact (binEquiv hK).symm.injective (congrFun (congrArg Prod.snd h) j)

theorem binCoords_eq_zero_iff (L : Fin r → Fin 2 → K) : binCoords hK L = 0 ↔ L = 0 := by
  have h0 : binCoords hK (0 : Fin r → Fin 2 → K) = 0 := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> simp [binCoords]
  exact ⟨fun h => binCoords_injective hK (h.trans h0.symm), fun h => h ▸ h0⟩

theorem crossMat_sub_eq (L L' : Fin r → Fin 2 → K) :
    crossMat (minusTailForm K 1 1) L' L - crossMat (minusTailForm K 1 1) L L' =
      (polarMat (binCoords hK L) (binCoords hK L')).map (castTwo K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  simp only [Matrix.sub_apply, crossMat, of_apply, polar_binTail, Matrix.map_apply, polarMat,
    Matrix.add_apply, vecMulVec_apply, binCoords, map_add, map_mul, castTwo_binEquiv_symm]
  linear_combination -(L i 0 * L' j 1 + L i 1 * L' j 0) * h2

theorem binCoords_conjL (g : GL (Fin r) (ZMod 2)) (L : Fin r → Fin 2 → K) :
    binCoords hK (conjL (Matrix.GeneralLinearGroup.map (castTwo K) g) 1 L) =
      ((g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (binCoords hK L).1,
        (g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (binCoords hK L).2) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
  · simp only [binCoords, conjL, LinearEquiv.coe_one, id_eq, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_sum, map_mul, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.GeneralLinearGroup.map_apply, binEquiv_symm_castTwo]

theorem binCoords_conjL_tailRot (L : Fin r → Fin 2 → K) :
    binCoords hK (conjL 1 (tailRot K) L) = omegaMul (binCoords hK L) := by
  have hL : ∀ j, ∑ i, ((1 : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) j i • L i = L j := by
    intro j
    rw [Units.val_one]
    simp [Matrix.one_apply]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · simp only [binCoords, conjL, hL, omegaMul, tailRot_apply_zero]
  · simp only [binCoords, conjL, hL, omegaMul, tailRot_apply_one, map_add, Pi.add_apply]

end Coords

section Groups

variable {K : Type*} [Field K] [CharP K 2] {r : ℕ}

theorem det_map_castTwo (g : GL (Fin r) (ZMod 2)) :
    ((Matrix.GeneralLinearGroup.map (castTwo K) g : GL (Fin r) K) :
      Matrix (Fin r) (Fin r) K).det = 1 := by
  change ((castTwo K).mapMatrix (g : Matrix (Fin r) (Fin r) (ZMod 2))).det = 1
  rw [← RingHom.map_det, det_eq_one_of_zmod_two, map_one]

variable (K r) in
@[expose] def leviB (hr : 3 ≤ r) :
    GL (Fin r) (ZMod 2) →* orthElementaryGroup (quadTail r (minusTailForm K 1 1)) where
  toFun g := ⟨dMap (Matrix.GeneralLinearGroup.map (castTwo K) g) 1,
    dMap_one_mem_orthElementaryGroup hr (det_map_castTwo g)⟩
  map_one' := Subtype.ext (by
    change dMap (Matrix.GeneralLinearGroup.map (castTwo K) 1) 1 = 1
    rw [map_one, dMap_one_one])
  map_mul' g g' := Subtype.ext (by
    change dMap (Matrix.GeneralLinearGroup.map (castTwo K) (g * g')) 1 =
      dMap (Matrix.GeneralLinearGroup.map (castTwo K) g) 1 *
        dMap (Matrix.GeneralLinearGroup.map (castTwo K) g') 1
    rw [map_mul, dMap_mul_dMap, mul_one])

theorem coe_leviB (hr : 3 ≤ r) (g : GL (Fin r) (ZMod 2)) :
    ((leviB K r hr g : orthElementaryGroup (quadTail r (minusTailForm K 1 1))) :
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) =
      dMap (Matrix.GeneralLinearGroup.map (castTwo K) g) 1 :=
  rfl

theorem leviB_injective (hr : 3 ≤ r) : Function.Injective (leviB K r hr) := by
  intro g g' h
  have h1 := congrArg Subtype.val h
  rw [coe_leviB, coe_leviB] at h1
  have h2 : dMap (Matrix.GeneralLinearGroup.map (castTwo K) g) 1 *
      uMap (minusTailForm K 1 1) 0 0 =
      dMap (Matrix.GeneralLinearGroup.map (castTwo K) g') 1 * uMap (minusTailForm K 1 1) 0 0 := by
    rw [h1]
  have h3 := congrArg (fun D : GL (Fin r) K => (D : Matrix (Fin r) (Fin r) K))
    (dMap_uMap_injective h2).1
  exact Units.ext (Matrix.map_injective castTwo_injective h3)

variable (K r) in
@[expose] def radN : Subgroup (orthElementaryGroup (quadTail r (minusTailForm K 1 1))) where
  carrier := {g | ∃ (L : Fin r → Fin 2 → K) (C : Matrix (Fin r) (Fin r) K), Cᵀ = -C ∧
    (∀ i, C i i = 0) ∧ (g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) =
      uMap (minusTailForm K 1 1) L C}
  mul_mem' := by
    rintro _ _ ⟨L, C, hC, hd, hg⟩ ⟨L', C', hC', hd', hg'⟩
    obtain ⟨hC'', hd''⟩ := mulParam_alternating (qA := minusTailForm K 1 1) L L' hC hd hC' hd'
    exact ⟨L + L', _, hC'', hd'', by rw [Subgroup.coe_mul, hg, hg', uMap_mul_uMap]⟩
  one_mem' := ⟨0, 0, by simp, fun _ => rfl, by rw [OneMemClass.coe_one, uMap_zero_zero]⟩
  inv_mem' := by
    rintro _ ⟨L, C, hC, hd, hg⟩
    obtain ⟨hC0, hd0⟩ := mulParam_alternating (qA := minusTailForm K 1 1) L (-L) hC hd
      (C' := 0) (by simp) (fun _ => rfl)
    refine ⟨-L, -mulParam (minusTailForm K 1 1) L (-L) C 0, by rw [transpose_neg, hC0],
      fun i => by rw [Matrix.neg_apply, hd0, neg_zero], ?_⟩
    rw [Subgroup.coe_inv, hg, inv_eq_iff_mul_eq_one, uMap_mul_uMap, add_neg_cancel]
    have h0 : mulParam (minusTailForm K 1 1) L (-L) C
        (-mulParam (minusTailForm K 1 1) L (-L) C 0) = 0 := by
      simp only [mulParam]
      abel
    rw [h0, uMap_zero_zero]

omit [CharP K 2] in
theorem mem_radN {g : orthElementaryGroup (quadTail r (minusTailForm K 1 1))} :
    g ∈ radN K r ↔ ∃ (L : Fin r → Fin 2 → K) (C : Matrix (Fin r) (Fin r) K), Cᵀ = -C ∧
      (∀ i, C i i = 0) ∧ (g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) =
        uMap (minusTailForm K 1 1) L C :=
  Iff.rfl

variable (K r) in
@[expose] def radTau :
    Multiplicative (binaryAltMatrices r) →* orthElementaryGroup (quadTail r (minusTailForm K 1 1))
    where
  toFun B := ⟨uMap (minusTailForm K 1 1) 0
      ((B.toAdd : Matrix (Fin r) (Fin r) (ZMod 2)).map (castTwo K)),
    uMap_mem_orthElementaryGroup 0 (map_mem_altSubgroup B.toAdd.2).1
      (map_mem_altSubgroup B.toAdd.2).2⟩
  map_one' := Subtype.ext (by
    change uMap (minusTailForm K 1 1) 0 ((0 : Matrix (Fin r) (Fin r) (ZMod 2)).map (castTwo K)) =
      1
    rw [Matrix.map_zero _ (map_zero _), uMap_zero_zero])
  map_mul' B B' := Subtype.ext (by
    change uMap (minusTailForm K 1 1) 0
        ((((B.toAdd + B'.toAdd : binaryAltMatrices r)) : Matrix (Fin r) (Fin r) (ZMod 2)).map
          (castTwo K)) = uMap (minusTailForm K 1 1) 0 _ * uMap (minusTailForm K 1 1) 0 _
    rw [uMap_zero_mul_uMap_zero, AddSubgroup.coe_add, Matrix.map_add _ (map_add _)])

theorem coe_radTau (B : Multiplicative (binaryAltMatrices r)) :
    ((radTau K r B : orthElementaryGroup (quadTail r (minusTailForm K 1 1))) :
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) =
      uMap (minusTailForm K 1 1) 0 ((B.toAdd : Matrix (Fin r) (Fin r) (ZMod 2)).map (castTwo K)) :=
  rfl

theorem radTau_injective : Function.Injective (radTau K r) := by
  intro B B' h
  have h1 := (uMap_injective (congrArg Subtype.val h)).2
  exact Multiplicative.toAdd.injective (Subtype.ext (Matrix.map_injective castTwo_injective h1))

theorem radTau_mem (B : Multiplicative (binaryAltMatrices r)) : radTau K r B ∈ radN K r :=
  ⟨0, _, (map_mem_altSubgroup B.toAdd.2).1, (map_mem_altSubgroup B.toAdd.2).2, rfl⟩

variable (K r) in
@[expose] def rotB (hr : 3 ≤ r) : orthElementaryGroup (quadTail r (minusTailForm K 1 1)) :=
  ⟨dMap 1 (tailRot K), by
    rw [← shortWeyl_mul_shortWeyl_eq_dMap (⟨0, by omega⟩ : Fin r)]
    exact mul_mem (shortWeyl_mem _ _) (shortWeyl_mem _ _)⟩

theorem coe_rotB (hr : 3 ≤ r) :
    ((rotB K r hr : orthElementaryGroup (quadTail r (minusTailForm K 1 1))) :
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) = dMap 1 (tailRot K) :=
  rfl

end Groups

section Shape

variable {K : Type*} [Field K] [CharP K 2] [Finite K] {r : ℕ} (hK : Nat.card K = 2)

variable (K r) in
@[expose] def radCoord (g : orthElementaryGroup (quadTail r (minusTailForm K 1 1))) :
    (Fin r → ZMod 2) × (Fin r → ZMod 2) :=
  binCoords hK fun j =>
    ((g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))
      (hypVec K (Fin 2 → K) (.inr j))).2

theorem radCoord_eq {g : orthElementaryGroup (quadTail r (minusTailForm K 1 1))}
    {L : Fin r → Fin 2 → K} {C : Matrix (Fin r) (Fin r) K}
    (hg : (g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) = uMap (minusTailForm K 1 1) L C) :
    radCoord K r hK g = binCoords hK L := by
  rw [radCoord, hg]
  congr 1
  funext j
  exact uMap_hypVec_inr_snd L C j

theorem radCoord_mul {m n : orthElementaryGroup (quadTail r (minusTailForm K 1 1))}
    (hm : m ∈ radN K r) (hn : n ∈ radN K r) :
    radCoord K r hK (m * n) = radCoord K r hK m + radCoord K r hK n := by
  obtain ⟨L, C, -, -, hmL⟩ := hm
  obtain ⟨L', C', -, -, hnL⟩ := hn
  rw [radCoord_eq hK hmL, radCoord_eq hK hnL,
    radCoord_eq hK (by rw [Subgroup.coe_mul, hmL, hnL, uMap_mul_uMap]), binCoords_add]

theorem exists_radCoord (w : (Fin r → ZMod 2) × (Fin r → ZMod 2)) :
    ∃ n ∈ radN K r, radCoord K r hK n = w :=
  ⟨⟨uMap (minusTailForm K 1 1) (ofBinCoords w) 0,
    uMap_mem_orthElementaryGroup _ (by simp) fun _ => rfl⟩,
    ⟨_, 0, by simp, fun _ => rfl, rfl⟩, by rw [radCoord_eq hK rfl, binCoords_ofBinCoords]⟩

theorem radCoord_eq_zero_iff {n : orthElementaryGroup (quadTail r (minusTailForm K 1 1))}
    (hn : n ∈ radN K r) : radCoord K r hK n = 0 ↔ n ∈ (radTau K r).range := by
  obtain ⟨L, C, hC, hd, hnL⟩ := hn
  rw [radCoord_eq hK hnL, binCoords_eq_zero_iff]
  constructor
  · rintro rfl
    have hsymm : ∀ i j, C j i = C i j := fun i j => by
      have h := congrFun (congrFun hC i) j
      simp only [transpose_apply, Matrix.neg_apply] at h
      rw [h]
      exact CharTwo.neg_eq _
    set B : Matrix (Fin r) (Fin r) (ZMod 2) := C.map (binEquiv hK).symm with hBdef
    have hB : B ∈ binaryAltMatrices r := by
      refine ⟨Matrix.ext fun i j => ?_, fun i => ?_⟩
      · simp only [hBdef, transpose_apply, Matrix.map_apply, hsymm]
      · simp only [hBdef, Matrix.map_apply, hd, map_zero]
    refine ⟨Multiplicative.ofAdd ⟨B, hB⟩, Subtype.ext ?_⟩
    rw [coe_radTau, hnL, toAdd_ofAdd]
    congr 1
    ext i j
    exact castTwo_binEquiv_symm hK _
  · rintro ⟨B, hB⟩
    rw [← hB, coe_radTau] at hnL
    exact (uMap_injective hnL).1.symm

theorem commutatorElement_radN {m n : orthElementaryGroup (quadTail r (minusTailForm K 1 1))}
    (hm : m ∈ radN K r) (hn : n ∈ radN K r) :
    ⁅m, n⁆ = radTau K r (Multiplicative.ofAdd (polarAlt (radCoord K r hK m)
      (radCoord K r hK n))) := by
  obtain ⟨L, C, -, -, hmL⟩ := hm
  obtain ⟨L', C', -, -, hnL⟩ := hn
  apply Subtype.ext
  rw [coe_radTau, toAdd_ofAdd, coe_polarAlt, radCoord_eq hK hmL, radCoord_eq hK hnL,
    ← crossMat_sub_eq hK, ← commutatorElement_uMap, ← hmL, ← hnL]
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]

theorem leviB_conj_mem (hr : 3 ≤ r) (g : GL (Fin r) (ZMod 2))
    {n : orthElementaryGroup (quadTail r (minusTailForm K 1 1))} (hn : n ∈ radN K r) :
    leviB K r hr g * n * (leviB K r hr g)⁻¹ ∈ radN K r ∧
      radCoord K r hK (leviB K r hr g * n * (leviB K r hr g)⁻¹) =
        ((g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (radCoord K r hK n).1,
          (g : Matrix (Fin r) (Fin r) (ZMod 2)) *ᵥ (radCoord K r hK n).2) := by
  obtain ⟨L, C, hC, hd, hnL⟩ := hn
  have hcoe : ((leviB K r hr g * n * (leviB K r hr g)⁻¹ :
      orthElementaryGroup (quadTail r (minusTailForm K 1 1))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) =
      uMap (minusTailForm K 1 1) (conjL (Matrix.GeneralLinearGroup.map (castTwo K) g) 1 L)
        (conjC (minusTailForm K 1 1) (Matrix.GeneralLinearGroup.map (castTwo K) g) 1 L C) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_leviB, hnL]
    exact dMap_conj_uMap (one_mem _) _ _ _
  obtain ⟨hC', hd'⟩ := conjC_alternating (one_mem _)
    (Matrix.GeneralLinearGroup.map (castTwo K) g) L hC hd
  exact ⟨⟨_, _, hC', hd', hcoe⟩, by rw [radCoord_eq hK hcoe, binCoords_conjL, radCoord_eq hK hnL]⟩

theorem rotB_conj_mem (hr : 3 ≤ r) {n : orthElementaryGroup (quadTail r (minusTailForm K 1 1))}
    (hn : n ∈ radN K r) :
    rotB K r hr * n * (rotB K r hr)⁻¹ ∈ radN K r ∧
      radCoord K r hK (rotB K r hr * n * (rotB K r hr)⁻¹) = omegaMul (radCoord K r hK n) := by
  obtain ⟨L, C, hC, hd, hnL⟩ := hn
  have hcoe : ((rotB K r hr * n * (rotB K r hr)⁻¹ :
      orthElementaryGroup (quadTail r (minusTailForm K 1 1))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) =
      uMap (minusTailForm K 1 1) (conjL 1 (tailRot K) L)
        (conjC (minusTailForm K 1 1) 1 (tailRot K) L C) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_rotB, hnL]
    exact dMap_conj_uMap tailRot_mem_orthogonalGroup _ _ _
  obtain ⟨hC', hd'⟩ := conjC_alternating tailRot_mem_orthogonalGroup (1 : GL (Fin r) K) L hC hd
  exact ⟨⟨_, _, hC', hd', hcoe⟩, by
    rw [radCoord_eq hK hcoe, binCoords_conjL_tailRot, radCoord_eq hK hnL]⟩

omit [Finite K] in
theorem rotB_mul_radTau (hr : 3 ≤ r) (B : Multiplicative (binaryAltMatrices r)) :
    rotB K r hr * radTau K r B = radTau K r B * rotB K r hr := by
  rw [← mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_rotB, coe_radTau,
    dMap_conj_uMap tailRot_mem_orthogonalGroup]
  have hL : conjL 1 (tailRot K) (0 : Fin r → Fin 2 → K) = 0 := funext fun j => by
    simp [conjL]
  rw [conjC, hL, Units.val_one, Matrix.one_mul, transpose_one, Matrix.mul_one, sMat_zero,
    zero_add, sub_zero]

omit [Finite K] in
theorem rotB_mul_leviB (hr : 3 ≤ r) (g : GL (Fin r) (ZMod 2)) :
    rotB K r hr * leviB K r hr g = leviB K r hr g * rotB K r hr := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_rotB, coe_leviB, dMap_mul_dMap, dMap_mul_dMap,
    one_mul, mul_one, one_mul, mul_one]

include hK in
theorem exists_sylow_binShape (hr : 3 ≤ r) :
    ∃ S : Sylow 2 (orthElementaryGroup (quadTail r (minusTailForm K 1 1))),
      ∀ s ∈ (S : Subgroup (orthElementaryGroup (quadTail r (minusTailForm K 1 1)))),
        ∃ a ∈ (LinearFlag.unitriangular r (ZMod 2)).map
          ((leviB K r hr).comp SpecialLinearGroup.toGL), ∃ b ∈ radN K r, s = a * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨S, hS⟩, -⟩ := orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hr
    (binTail_anisotropic hK) (binTail_nondegenerate hK) (Or.inr finrank_fin_two_fun)
  refine ⟨S, fun s hs => ?_⟩
  rw [hS, Subgroup.mem_subgroupOf] at hs
  obtain ⟨D, L, C, hD, h1, hC, hd, hsD⟩ := (mem_tailUnipotent_iff (binTail_anisotropic hK)).1 hs
  set A₀ : Matrix (Fin r) (Fin r) (ZMod 2) := (D : Matrix (Fin r) (Fin r) K).map
    (binEquiv hK).symm with hA₀def
  have hA₀ : A₀.map (castTwo K) = D := Matrix.ext fun i j => castTwo_binEquiv_symm hK _
  have hdet : A₀.det = 1 := by
    apply castTwo_injective (K := K)
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA₀, map_one,
      Matrix.det_of_isUpperTriangular hD]
    exact Finset.prod_eq_one fun i _ => h1 i
  set A₁ : SpecialLinearGroup (Fin r) (ZMod 2) := ⟨A₀, hdet⟩ with hA₁def
  have hA₁ : A₁ ∈ LinearFlag.unitriangular r (ZMod 2) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · change (binEquiv hK).symm ((D : Matrix (Fin r) (Fin r) K) i j) = 0
      rw [hD hij, map_zero]
    · change (binEquiv hK).symm ((D : Matrix (Fin r) (Fin r) K) i i) = 1
      rw [h1 i, map_one]
  refine ⟨leviB K r hr (SpecialLinearGroup.toGL A₁), ⟨A₁, hA₁, rfl⟩,
    ⟨uMap _ L C, uMap_mem_orthElementaryGroup L hC hd⟩, ⟨L, C, hC, hd, rfl⟩, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, coe_leviB, hsD]
  congr 2
  exact Units.ext hA₀.symm

omit [Finite K] in
theorem inf_radN_eq_bot (hr : 3 ≤ r) :
    (LinearFlag.unitriangular r (ZMod 2)).map ((leviB K r hr).comp SpecialLinearGroup.toGL) ⊓
      radN K r = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨A, -, rfl⟩, ⟨L, C, -, -, hx⟩⟩
  rw [Subgroup.mem_bot, MonoidHom.comp_apply]
  rw [MonoidHom.comp_apply, coe_leviB] at hx
  have hD := congrArg (fun D : GL (Fin r) K => (D : Matrix (Fin r) (Fin r) K)) (dMap_eq_uMap hx)
  have hD' : ((SpecialLinearGroup.toGL A : GL (Fin r) (ZMod 2)) :
      Matrix (Fin r) (Fin r) (ZMod 2)).map (castTwo K) =
      (1 : Matrix (Fin r) (Fin r) (ZMod 2)).map (castTwo K) := by
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact hD
  have hA : SpecialLinearGroup.toGL A = 1 := Units.ext (Matrix.map_injective castTwo_injective hD')
  rw [hA, map_one]

variable (K r) in
@[expose] def binShape (hr : 3 ≤ r) :
    Shape (orthElementaryGroup (quadTail r (minusTailForm K 1 1))) r where
  ρ := leviB K r hr
  ρ_injective := leviB_injective hr
  N := radN K r
  π := radCoord K r hK
  π_mul _ hm _ hn := radCoord_mul hK hm hn
  exists_π := exists_radCoord hK
  τ := radTau K r
  τ_injective := radTau_injective
  τ_mem := radTau_mem
  π_eq_zero_iff _ hn := radCoord_eq_zero_iff hK hn
  commutator_eq _ hm _ hn := commutatorElement_radN hK hm hn
  ρ_conj_mem g _ hn := (leviB_conj_mem hK hr g hn).1
  π_ρ_conj g _ hn := (leviB_conj_mem hK hr g hn).2
  h := rotB K r hr
  h_conj_mem _ hn := (rotB_conj_mem hK hr hn).1
  π_h_conj _ hn := (rotB_conj_mem hK hr hn).2
  h_τ := rotB_mul_radTau hr
  h_ρ := rotB_mul_leviB hr
  sylow := exists_sylow_binShape hK hr
  inf_eq_bot := inf_radN_eq_bot hr

end Shape

section ModelIso

variable {K : Type*} [Field K] [CharP K 2] {r : ℕ}

theorem elemScalars_quadTail_eq_bot {A : Type*} [AddCommGroup A] [Module K A]
    {qA : QuadraticForm K A} (hr : 1 ≤ r) : elemScalars (quadTail r qA) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨c, hc⟩
  rw [Subgroup.mem_bot]
  set i : Fin r := ⟨0, by omega⟩
  set v : (Fin r ⊕ Fin r → K) × A := hypVec K A (.inl i) + hypVec K A (.inr i) with hv
  have hQv : quadTail r qA v = 1 := by
    rw [hv, QuadraticMap.map_add (quadTail r qA), quadTail_hypVec, quadTail_hypVec,
      polar_hypVec_hypVec,
      Sum.swap_inl, ite_eq_left rfl, zero_add, zero_add]
  have h := map_of_mem (orthElementaryGroup_le _ g.2) v
  rw [hc, map_smul_eq_sq, hQv, mul_one] at h
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc1 : c = 1 := by
    have h3 : (c - 1) ^ 2 = 0 := by linear_combination h + (1 - c) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h3)
  exact Subtype.ext (LinearEquiv.ext fun x => by rw [hc, hc1, one_smul]; rfl)

theorem exists_mulEquiv_of_lieModel {J : Type} [Group J] {n : ℕ}
    (hJ : CFSG.Blueprint.LieModel J .POmegaMinus n 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ∧ 4 ≤ n ∧
      Nonempty (J ≃* orthElementaryGroup (quadTail (n - 1) (minusTailForm K 1 1))) := by
  rcases hJ with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, -, hn⟩, K, hK, hfin, hcard, b, c, hirr, ⟨e⟩⟩ := hc
    have hn' : 4 ≤ n := hn
    have hK2 : Nat.card K = 2 := by rw [hcard, pow_one]
    have hchar : CharP K 2 :=
      finite_field_prime_power_characteristic (K := K) Nat.prime_two le_rfl hcard
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hc1 : c = 1 := by
      rcases eq_zero_or_eq_one hK2 c with h | h
      · exact absurd (by rw [h]; ring) (hirr 0)
      · exact h
    subst hc1
    have hb1 : b = 1 := by
      rcases eq_zero_or_eq_one hK2 b with h | h
      · exact absurd (by rw [h]; linear_combination h2) (hirr 1)
      · exact h
    subst hb1
    have hE := commutator_orthogonalGroup_quadMinus hn' hirr
    exact ⟨K, hK, hfin, hchar, hK2, hn', ⟨e.trans ((tailProjEquiv (minusTailIsometry n K 1 1)
      (coe_quadMinus n K 1 1) hE).trans ((QuotientGroup.quotientMulEquivOfEq
        (elemScalars_quadTail_eq_bot (by omega))).trans QuotientGroup.quotientBot))⟩⟩
  all_goals exact absurd ht (by decide)

end ModelIso

end CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover
