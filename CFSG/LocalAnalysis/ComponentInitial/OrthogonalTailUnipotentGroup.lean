module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWeylLift

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Matrix
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

section Formulas

@[expose] noncomputable def uBlock (C : Matrix (Fin r) (Fin r) K) :
    (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (fromBlocks 1 C 0 1))
    (Matrix.toLin' (fromBlocks 1 (-C) 0 1))
    (by rw [← Matrix.toLin'_mul, fromBlocks_multiply]; simp [Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, fromBlocks_multiply]; simp [Matrix.toLin'_one])

theorem uBlock_apply (C : Matrix (Fin r) (Fin r) K) (w : Fin r ⊕ Fin r → K) :
    uBlock C w = Sum.elim (w ∘ Sum.inl + C *ᵥ (w ∘ Sum.inr)) (w ∘ Sum.inr) := by
  change Matrix.toLin' _ w = _
  rw [Matrix.toLin'_apply, fromBlocks_mulVec_apply]
  simp

theorem uMap_zero_eq (C : Matrix (Fin r) (Fin r) K) :
    uMap qA 0 C = (uBlock C).prodCongr (LinearEquiv.refl K A) := by
  refine LinearEquiv.ext fun v => Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i
    · rw [uMap_apply, uLin_apply_inl, sMat_zero, zero_add, LinearEquiv.prodCongr_apply,
        uBlock_apply]
      simp
    · rw [LinearEquiv.prodCongr_apply, uBlock_apply]
      rfl
  · rw [uMap_apply, uLin_apply_snd, LinearEquiv.prodCongr_apply]
    simp

theorem toMatrix'_dBlock_mul_uBlock (D : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K) :
    LinearMap.toMatrix' (((dBlock D * uBlock C : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) :
      (Fin r ⊕ Fin r → K) →ₗ[K] _)) =
      fromBlocks (D : Matrix (Fin r) (Fin r) K) ((D : Matrix (Fin r) (Fin r) K) * C) 0
        ((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := by
  rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix'_mul, toMatrix'_dBlock]
  change _ * LinearMap.toMatrix' (Matrix.toLin' _) = _
  rw [LinearMap.toMatrix'_toLin', fromBlocks_multiply]
  simp

theorem dMap_mul_uMap_zero (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (C : Matrix (Fin r) (Fin r) K) :
    dMap D h * uMap qA 0 C = (dBlock D * uBlock C).prodCongr h := by
  rw [uMap_zero_eq, dMap]
  exact LinearEquiv.ext fun _ => rfl

theorem dMap_mul_dMap (D D' : GL (Fin r) K) (h h' : A ≃ₗ[K] A) :
    dMap D h * dMap D' h' = dMap (D * D') (h * h') := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, dMap_apply, dMap_apply, dMap_apply]
  refine Prod.ext ?_ rfl
  change Sum.elim _ _ = Sum.elim _ _
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_mulVec, _root_.mul_inv_rev,
    Units.val_mul, transpose_mul]

variable (qA) in
@[expose] def crossMat (L L' : Fin r → A) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => polar qA (L i) (L' j)

variable (qA) in
@[expose] def mulParam (L L' : Fin r → A) (C C' : Matrix (Fin r) (Fin r) K) :
    Matrix (Fin r) (Fin r) K :=
  sMat qA L + sMat qA L' - crossMat qA L L' + C + C' - sMat qA (L + L')

theorem crossMat_mulVec (L L' : Fin r → A) (y : Fin r → K) (i : Fin r) :
    (crossMat qA L L' *ᵥ y) i = polar qA (L i) (∑ j, y j • L' j) := by
  simp only [mulVec, dotProduct, crossMat, of_apply]
  rw [polar_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [polar_smul_right_eq, mul_comm]

theorem uMap_mul_uMap (L L' : Fin r → A) (C C' : Matrix (Fin r) (Fin r) K) :
    uMap qA L C * uMap qA L' C' = uMap qA (L + L') (mulParam qA L L' C C') := by
  refine LinearEquiv.ext fun v => Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i
    · rw [LinearEquiv.mul_apply, uMap_apply, uMap_apply, uMap_apply, uLin_apply_inl,
        uLin_apply_inl, uLin_apply_inl]
      have hy : (uLin qA L' C' v).1 ∘ Sum.inr = v.1 ∘ Sum.inr := rfl
      rw [hy, uLin_apply_snd, mulParam]
      simp only [add_mulVec, sub_mulVec, Pi.add_apply, Pi.sub_apply, add_sub_cancel,
        crossMat_mulVec, polar_add_right, Pi.add_apply, polar_add_left, Function.comp_apply]
      ring
    · rfl
  · rw [LinearEquiv.mul_apply, uMap_apply, uMap_apply, uMap_apply, uLin_apply_snd, uLin_apply_snd,
      uLin_apply_snd]
    simp only [uLin_apply_inr, Pi.add_apply, smul_add, Finset.sum_add_distrib]
    abel

theorem mulParam_alternating (L L' : Fin r → A) {C C' : Matrix (Fin r) (Fin r) K}
    (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0) (hC' : C'ᵀ = -C') (hd' : ∀ i, C' i i = 0) :
    (mulParam qA L L' C C')ᵀ = -mulParam qA L L' C C' ∧ ∀ i, mulParam qA L L' C C' i i = 0 := by
  have hCij : ∀ i j, C j i = -C i j := fun i j => by
    have := congrFun (congrFun hC i) j
    simpa using this
  have hCij' : ∀ i j, C' j i = -C' i j := fun i j => by
    have := congrFun (congrFun hC' i) j
    simpa using this
  have hent : ∀ i j, mulParam qA L L' C C' i j =
      (if i = j then 0 else if i < j then polar qA (L' i) (L j) else -polar qA (L i) (L' j)) +
        C i j + C' i j := by
    intro i j
    simp only [mulParam, Matrix.sub_apply, Matrix.add_apply, sMat, crossMat, of_apply,
      Pi.add_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      rw [QuadraticMap.map_add qA]
      ring
    · by_cases hlt : i < j
      · simp only [hij, hlt, ↓reduceIte]
        rw [polar_add_left, polar_add_right, polar_add_right]
        ring
      · simp only [hij, hlt, ↓reduceIte]
        ring
  refine ⟨?_, fun i => by rw [hent, ite_eq_left rfl, hd, hd']; ring⟩
  ext i j
  rw [transpose_apply, neg_apply, hent, hent, hCij i j, hCij' i j]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    rw [hd, hd']
    ring
  · have hji : j ≠ i := Ne.symm hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · simp only [hji, hij, hlt, not_lt.2 hlt.le, ite_true, ite_false]
      rw [polar_comm]
      ring
    · simp only [hji, hij, hlt, not_lt.2 hlt.le, ite_true, ite_false]
      rw [polar_comm]
      ring

theorem eichler_inl_tail_eq_uMap (i : Fin r) (b : A) :
    eichler (quadTail r qA) (hypVec K A (.inl i)) ((0 : Fin r ⊕ Fin r → K), b) =
      uMap qA (Pi.single i b) 0 := by
  refine LinearEquiv.ext fun v => ?_
  rw [eichler_apply (quadTail_hypVec _) (polar_hypVec_tail _ _), polar_hypVec, Sum.swap_inl,
    polar_quadTail, polar_zero_right, zero_add, quadTail_tail]
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with k | k
    · rw [uMap_apply, uLin_apply_inl, add_zero]
      simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply,
        smul_zero, add_zero, hypVec, smul_eq_mul]
      by_cases hki : k = i
      · subst hki
        have hS : (sMat qA (Pi.single k b) *ᵥ (v.1 ∘ Sum.inr)) k = -qA b * v.1 (Sum.inr k) := by
          simp only [mulVec, dotProduct, sMat, of_apply]
          rw [Finset.sum_eq_single k]
          · simp
          · intro j _ hj
            simp [Ne.symm hj, hj]
          · simp
        rw [hS]
        simp [polar_comm]
        ring
      · have hS : (sMat qA (Pi.single i b) *ᵥ (v.1 ∘ Sum.inr)) k = 0 := by
          simp only [mulVec, dotProduct, sMat, of_apply]
          refine Finset.sum_eq_zero fun j _ => ?_
          simp [hki]
        rw [hS]
        simp [hki]
    · simp [uMap_apply, uLin_apply_inr, hypVec]
  · rw [uMap_apply, uLin_apply_snd]
    simp [hypVec, Pi.single_apply]

theorem dMap_one_one : dMap (1 : GL (Fin r) K) (1 : A ≃ₗ[K] A) = 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [dMap_apply]
  refine Prod.ext ?_ rfl
  change Sum.elim _ _ = v.1
  simp

theorem dMap_inv (D : GL (Fin r) K) (h : A ≃ₗ[K] A) : (dMap D h)⁻¹ = dMap D⁻¹ h⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, dMap_mul_dMap, mul_inv_cancel, mul_inv_cancel, dMap_one_one]

@[expose] def conjL (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (L : Fin r → A) : Fin r → A :=
  fun j => h (∑ i, (D : Matrix (Fin r) (Fin r) K) j i • L i)

variable (qA) in
@[expose] def conjC (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (L : Fin r → A)
    (C : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  (D : Matrix (Fin r) (Fin r) K) * (sMat qA L + C) * (D : Matrix (Fin r) (Fin r) K)ᵀ -
    sMat qA (conjL D h L)

theorem sum_conjL (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (L : Fin r → A) (y : Fin r → K) :
    ∑ j, y j • conjL D h L j =
      h (∑ j, ((D : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ y) j • L j) := by
  simp only [conjL, map_sum, map_smul, Finset.smul_sum, smul_smul, mulVec, dotProduct,
    transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

variable {h : A ≃ₗ[K] A} (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup qA)
include hh

theorem dMap_conj_uMap (D : GL (Fin r) K) (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K) :
    dMap D h * uMap qA L C * (dMap D h)⁻¹ = uMap qA (conjL D h L) (conjC qA D h L C) := by
  have hpol : ∀ x a, polar qA (h x) a = polar qA x (h.symm a) := fun x a => by
    rw [← polar_map_of_mem hh x (h.symm a), LinearEquiv.apply_symm_apply]
  rw [dMap_inv]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, dMap_apply, dMap_apply, uMap_apply,
    uMap_apply]
  set w := ((Sum.elim (((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ (v.1 ∘ Sum.inl))
    ((((D⁻¹)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ (v.1 ∘ Sum.inr)),
      (h⁻¹ : A ≃ₗ[K] A) v.2) : (Fin r ⊕ Fin r → K) × A) with hw
  have hwx : w.1 ∘ Sum.inl = ((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ
      (v.1 ∘ Sum.inl) := rfl
  have hwy : w.1 ∘ Sum.inr = (D : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ (v.1 ∘ Sum.inr) := by
    change ((((D⁻¹)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ (v.1 ∘ Sum.inr)) = _
    rw [inv_inv]
  have hwa : w.2 = h.symm v.2 := by
    rw [hw, LinearEquiv.coe_inv]
  have hux : (uLin qA L C w).1 ∘ Sum.inl = w.1 ∘ Sum.inl - (fun k => polar qA (L k) w.2) +
      (sMat qA L + C) *ᵥ (w.1 ∘ Sum.inr) := rfl
  have huy : (uLin qA L C w).1 ∘ Sum.inr = w.1 ∘ Sum.inr := rfl
  refine Prod.ext ?_ ?_
  · change Sum.elim ((D : Matrix (Fin r) (Fin r) K) *ᵥ ((uLin qA L C w).1 ∘ Sum.inl))
      (((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ ((uLin qA L C w).1 ∘ Sum.inr)) = _
    funext c
    rcases c with i | i
    · have hS : sMat qA (conjL D h L) + conjC qA D h L C =
          (D : Matrix (Fin r) (Fin r) K) * (sMat qA L + C) * (D : Matrix (Fin r) (Fin r) K)ᵀ := by
        rw [conjC, add_sub_cancel]
      have hp : (fun k => polar qA (conjL D h L k) v.2) =
          (D : Matrix (Fin r) (Fin r) K) *ᵥ fun k => polar qA (L k) (h.symm v.2) := by
        funext k
        simp only [conjL, hpol, polar_finset_sum_left, polar_smul_left_eq, mulVec, dotProduct]
      have hp' := congrFun hp i
      rw [Sum.elim_inl, hux, hwx, hwy, hwa, mulVec_add, mulVec_sub, mulVec_mulVec,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, mulVec_mulVec, mulVec_mulVec,
        ← hS, uLin_apply_inl]
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [← hp']
      rfl
    · rw [Sum.elim_inr, huy, hwy, mulVec_mulVec, ← transpose_mul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, transpose_one, one_mulVec]
      rfl
  · change h (uLin qA L C w).2 = (uLin qA (conjL D h L) (conjC qA D h L C) v).2
    rw [uLin_apply_snd, uLin_apply_snd, map_add, hwa, LinearEquiv.apply_symm_apply]
    congr 1
    rw [sum_conjL]
    congr 1

theorem conjC_alternating (D : GL (Fin r) K) (L : Fin r → A) {C : Matrix (Fin r) (Fin r) K}
    (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0) :
    (conjC qA D h L C)ᵀ = -conjC qA D h L C ∧ ∀ i, conjC qA D h L C i i = 0 := by
  refine alternating_of_mulVec_dotProduct_self fun y => ?_
  set z := (D : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ y with hz
  have h1 : (((D : Matrix (Fin r) (Fin r) K) * (sMat qA L + C) *
      (D : Matrix (Fin r) (Fin r) K)ᵀ) *ᵥ y) ⬝ᵥ y = ((sMat qA L + C) *ᵥ z) ⬝ᵥ z := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec,
      ← mulVec_transpose, dotProduct_comm]
  rw [conjC, sub_mulVec, sub_dotProduct, h1, add_mulVec, add_dotProduct,
    mulVec_dotProduct_self_eq_zero hC hd, add_zero, dotProduct_comm, dotProduct_sMat_mulVec,
    dotProduct_comm, dotProduct_sMat_mulVec, sum_conjL, map_of_mem hh, ← hz]
  ring

end Formulas

section InUnip

theorem prodHom_mem_tailUnipotent {b : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hb : b ∈ posUnip r K) : prodHom A b ∈ tailUnipotent r qA := by
  rw [← unipotent_eq_posUnip] at hb
  have hle : (unipotent r K).map (prodHom A) ≤ tailUnipotent r qA := by
    rw [unipotent, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun α hα => ?_
    rw [← Subgroup.map_le_iff_le_comap, ← tailLongGroup_eq_map,
      ← tailRootGroup_of_mem_roots (posRoots_subset_roots hα)]
    exact tailRootGroup_le_tailUnipotent (Or.inr hα)
  exact hle ⟨b, hb, rfl⟩

theorem dBlock_mul_uBlock_mem_posUnip {D : GL (Fin r) K}
    (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ i, (D : Matrix (Fin r) (Fin r) K) i i = 1) {C : Matrix (Fin r) (Fin r) K}
    (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0) : dBlock D * uBlock C ∈ posUnip r K :=
  mem_posUnip_iff.2 ⟨D, C, hD, h1, hC, hd, toMatrix'_dBlock_mul_uBlock D C⟩

theorem prodHom_dBlock_mul_uBlock (D : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K) :
    prodHom A (dBlock D * uBlock C) = dMap D 1 * uMap qA 0 C := by
  rw [dMap_mul_uMap_zero, prodHom_apply]
  rfl

theorem uMap_zero_zero : uMap qA (0 : Fin r → A) 0 = 1 := by
  rw [uMap_zero_eq]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.prodCongr_apply, uBlock_apply]
  refine Prod.ext ?_ rfl
  change Sum.elim _ _ = v.1
  simp

theorem uMap_zero_mem_tailUnipotent (L : Fin r → A) : uMap qA L 0 ∈ tailUnipotent r qA := by
  have key : ∀ s : Finset (Fin r), ∃ C : Matrix (Fin r) (Fin r) K, Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
      uMap qA (fun j => if j ∈ s then L j else 0) C ∈ tailUnipotent r qA := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨0, by simp, fun _ => rfl, ?_⟩
      have h0 : (fun j => if j ∈ (∅ : Finset (Fin r)) then L j else 0) = 0 := funext fun j => by
        simp
      rw [h0, uMap_zero_zero]
      exact one_mem _
    | insert a s ha ih =>
      obtain ⟨C, hC, hd, hmem⟩ := ih
      have hshort : uMap qA (Pi.single a (L a)) 0 ∈ tailUnipotent r qA := by
        rw [← eichler_inl_tail_eq_uMap]
        exact tailRootGroup_le_tailUnipotent (Or.inl ⟨a, rfl⟩)
          (mem_tailRootGroup_eps.2 ⟨L a, rfl⟩)
      have hsum : Pi.single a (L a) + (fun j => if j ∈ s then L j else 0) =
          fun j => if j ∈ insert a s then L j else 0 := by
        funext j
        by_cases hja : j = a
        · subst hja
          simp [ha]
        · by_cases hjs : j ∈ s
          · simp [hja, hjs]
          · simp [hja, hjs]
      obtain ⟨hC'', hd''⟩ := mulParam_alternating (qA := qA) (Pi.single a (L a))
        (fun j => if j ∈ s then L j else 0) (C := 0) (C' := C) (by simp) (fun _ => rfl) hC hd
      refine ⟨_, hC'', hd'', ?_⟩
      rw [← hsum, ← uMap_mul_uMap]
      exact mul_mem hshort hmem
  obtain ⟨C, hC, hd, hmem⟩ := key Finset.univ
  have hL : (fun j => if j ∈ (Finset.univ : Finset (Fin r)) then L j else 0) = L := funext fun j =>
    by simp
  rw [hL] at hmem
  have h0 : uMap qA (0 : Fin r → A) C ∈ tailUnipotent r qA := by
    have := prodHom_mem_tailUnipotent (A := A) (qA := qA)
      (dBlock_mul_uBlock_mem_posUnip (D := 1)
        (fun i j h => by rw [Units.val_one]; exact Matrix.one_apply_ne (ne_of_gt h))
        (fun i => by simp) hC hd)
    rwa [prodHom_dBlock_mul_uBlock, show dMap (1 : GL (Fin r) K) (1 : A ≃ₗ[K] A) = 1 from
      dMap_one_one, one_mul] at this
  have heq : uMap qA L 0 = (uMap qA 0 C)⁻¹ * uMap qA L C := by
    rw [← uMap_zero_mul_uMap L C, inv_mul_cancel_left]
  rw [heq]
  exact mul_mem (inv_mem h0) hmem

theorem dMap_mul_uMap_mem_tailUnipotent {D : GL (Fin r) K}
    (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ i, (D : Matrix (Fin r) (Fin r) K) i i = 1) (L : Fin r → A)
    {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0) :
    dMap D 1 * uMap qA L C ∈ tailUnipotent r qA := by
  rw [← uMap_zero_mul_uMap, ← mul_assoc, ← prodHom_dBlock_mul_uBlock]
  exact mul_mem (prodHom_mem_tailUnipotent (dBlock_mul_uBlock_mem_posUnip hD h1 hC hd))
    (uMap_zero_mem_tailUnipotent L)

end InUnip

section Delta

theorem dMap_mul_uMap_mem_tailFlagStab {D : GL (Fin r) K}
    (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular) {h : A ≃ₗ[K] A}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup qA) (L : Fin r → A)
    {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0) :
    dMap D h * uMap qA L C ∈ tailFlagStab r qA := by
  refine mem_tailFlagStab.2 ⟨mul_mem (dMap_mem_orthogonalGroup D hh)
    (uMap_mem_orthogonalGroup L hC hd), fun i _ _ => ?_⟩
  rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp,
    map_tailFlag_uMap, map_tailFlag_dMap hD]

@[expose] def stabDiag (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
    (Fin r → K) × Module.End K A :=
  (fun i => (g (hypVec K A (.inl i))).1 (.inl i),
    (LinearMap.snd K (Fin r ⊕ Fin r → K) A).comp
      ((g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _).comp (LinearMap.inr K (Fin r ⊕ Fin r → K) A)))

theorem stabDiag_dMap_uMap (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (L : Fin r → A)
    (C : Matrix (Fin r) (Fin r) K) :
    stabDiag (dMap D h * uMap qA L C) =
      (fun i => (D : Matrix (Fin r) (Fin r) K) i i, (h : Module.End K A)) := by
  refine Prod.ext (funext fun i => ?_) (LinearMap.ext fun a => ?_)
  · change (dMap D h (uMap qA L C (hypVec K A (.inl i)))).1 (.inl i) = _
    rw [uMap_apply_of_fst_inr L C (fun k => by simp [hypVec]) rfl, dMap_apply]
    have hx : (hypVec K A (.inl i) : (Fin r ⊕ Fin r → K) × A).1 ∘ Sum.inl = Pi.single i 1 := by
      funext k
      simp [hypVec, Pi.single_apply]
    change ((D : Matrix (Fin r) (Fin r) K) *ᵥ _) i = _
    rw [hx, mulVec_single_one, col_apply]
  · change (dMap D h (uMap qA L C ((0 : Fin r ⊕ Fin r → K), a))).2 = h a
    rw [dMap_apply, uMap_apply, uLin_apply_snd]
    simp

theorem mul_apply_self_of_upperTriangular {D D' : Matrix (Fin r) (Fin r) K}
    (hD : D.IsUpperTriangular) (hD' : D'.IsUpperTriangular) (i : Fin r) :
    (D * D') i i = D i i * D' i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hD h, zero_mul]
    · rw [hD' h, mul_zero]
  · simp

theorem dMap_uMap_mul_dMap_uMap (D₁ D₂ : GL (Fin r) K) (h₁ : A ≃ₗ[K] A) {h₂ : A ≃ₗ[K] A}
    (hh₂ : h₂ ∈ TauCeti.QuadraticMap.orthogonalGroup qA) (L₁ L₂ : Fin r → A)
    (C₁ C₂ : Matrix (Fin r) (Fin r) K) :
    dMap D₁ h₁ * uMap qA L₁ C₁ * (dMap D₂ h₂ * uMap qA L₂ C₂) =
      dMap (D₁ * D₂) (h₁ * h₂) * uMap qA (conjL D₂⁻¹ h₂⁻¹ L₁ + L₂)
        (mulParam qA (conjL D₂⁻¹ h₂⁻¹ L₁) L₂ (conjC qA D₂⁻¹ h₂⁻¹ L₁ C₁) C₂) := by
  have hconj := dMap_conj_uMap (inv_mem hh₂) D₂⁻¹ L₁ C₁ (qA := qA)
  rw [dMap_inv, inv_inv, inv_inv] at hconj
  rw [← uMap_mul_uMap, ← hconj, ← dMap_mul_dMap]
  have hinv : dMap D₂⁻¹ h₂⁻¹ = (dMap D₂ h₂)⁻¹ := (dMap_inv D₂ h₂).symm
  rw [hinv]
  group

theorem eq_dBlock_mul_uBlock {b : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    {D : GL (Fin r) K} {C : Matrix (Fin r) (Fin r) K}
    (hM : LinearMap.toMatrix' (b : (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      fromBlocks (D : Matrix (Fin r) (Fin r) K) ((D : Matrix (Fin r) (Fin r) K) * C) 0
        ((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) :
    b = dBlock D * uBlock C :=
  LinearEquiv.toLinearMap_injective
    (LinearMap.toMatrix'.injective (hM.trans (toMatrix'_dBlock_mul_uBlock D C).symm))

end Delta

section Levi

variable [FiniteDimensional K A]

variable (r qA) in
@[expose] noncomputable def stabDiagHom (hani : qA.Anisotropic) :
    tailFlagStab r qA →* (Fin r → K) × Module.End K A where
  toFun g := stabDiag g.1
  map_one' := by
    have h1 : ((1 : tailFlagStab r qA) : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) =
        dMap 1 1 * uMap qA 0 0 := by
      rw [dMap_one_one, uMap_zero_zero, one_mul]
      rfl
    rw [h1, stabDiag_dMap_uMap]
    refine Prod.ext (funext fun i => ?_) rfl
    simp
  map_mul' g₁ g₂ := by
    obtain ⟨D₁, h₁, L₁, C₁, hD₁, -, -, -, he₁⟩ := exists_dMap_uMap_eq hani g₁.2
    obtain ⟨D₂, h₂, L₂, C₂, hD₂, hh₂, -, -, he₂⟩ := exists_dMap_uMap_eq hani g₂.2
    change stabDiag (g₁.1 * g₂.1) = stabDiag g₁.1 * stabDiag g₂.1
    rw [he₁, he₂, dMap_uMap_mul_dMap_uMap D₁ D₂ h₁ hh₂, stabDiag_dMap_uMap, stabDiag_dMap_uMap,
      stabDiag_dMap_uMap]
    refine Prod.ext (funext fun i => ?_) rfl
    change ((D₁ * D₂ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i i =
      (D₁ : Matrix (Fin r) (Fin r) K) i i * (D₂ : Matrix (Fin r) (Fin r) K) i i
    rw [Units.val_mul, mul_apply_self_of_upperTriangular hD₁ hD₂]

variable (hani : qA.Anisotropic)

theorem stabDiagHom_apply (g : tailFlagStab r qA) : stabDiagHom r qA hani g = stabDiag g.1 :=
  rfl

include hani

theorem mem_ker_of_eq {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    {D : GL (Fin r) K} (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ i, (D : Matrix (Fin r) (Fin r) K) i i = 1) {L : Fin r → A}
    {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0)
    (hg : g = dMap D 1 * uMap qA L C) :
    g ∈ (stabDiagHom r qA hani).ker.map (tailFlagStab r qA).subtype := by
  have hmem : g ∈ tailFlagStab r qA := by
    rw [hg]
    exact dMap_mul_uMap_mem_tailFlagStab hD (one_mem _) L hC hd
  refine ⟨⟨g, hmem⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
  rw [stabDiagHom_apply]
  change stabDiag g = 1
  rw [hg, stabDiag_dMap_uMap]
  refine Prod.ext (funext fun i => h1 i) rfl

theorem tailUnipotent_le_ker :
    tailUnipotent r qA ≤ (stabDiagHom r qA hani).ker.map (tailFlagStab r qA).subtype := by
  refine iSup₂_le fun α hα => ?_
  rcases hα with ⟨i, rfl⟩ | hlong
  · rintro g hg
    obtain ⟨b, rfl⟩ := mem_tailRootGroup_eps.1 hg
    rw [eichler_inl_tail_eq_uMap]
    exact mem_ker_of_eq hani (D := 1) (L := Pi.single i b) (C := 0)
      (fun i j h => by rw [Units.val_one]; exact Matrix.one_apply_ne (ne_of_gt h))
      (fun i => by rw [Units.val_one, Matrix.one_apply_eq]) (by simp) (fun _ => rfl)
      (by rw [dMap_one_one, one_mul])
  · rw [tailRootGroup_of_mem_roots (posRoots_subset_roots hlong), tailLongGroup_eq_map]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b ∈ posUnip r K := by
      rw [← unipotent_eq_posUnip]
      exact rootSubgroup_le_unipotent hlong hb
    obtain ⟨D, C, hD, h1, hC, hd, hM⟩ := mem_posUnip_iff.1 hb'
    refine mem_ker_of_eq hani hD h1 hC hd (L := 0) ?_
    change prodHom A b = _
    rw [eq_dBlock_mul_uBlock hM, prodHom_dBlock_mul_uBlock]

theorem mem_tailUnipotent_iff {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} :
    g ∈ tailUnipotent r qA ↔ ∃ (D : GL (Fin r) K) (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K),
      (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧
      (∀ i, (D : Matrix (Fin r) (Fin r) K) i i = 1) ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
      g = dMap D 1 * uMap qA L C := by
  constructor
  · intro hg
    obtain ⟨⟨g', hg'⟩, hker, rfl⟩ := tailUnipotent_le_ker hani hg
    obtain ⟨D, h, L, C, hD, -, hC, hd, he⟩ := exists_dMap_uMap_eq hani hg'
    have h1 := MonoidHom.mem_ker.1 hker
    rw [stabDiagHom_apply] at h1
    change stabDiag g' = 1 at h1
    rw [he, stabDiag_dMap_uMap] at h1
    have hh : h = 1 := LinearEquiv.ext fun a => LinearMap.congr_fun (congrArg Prod.snd h1) a
    refine ⟨D, L, C, hD, fun i => congrFun (congrArg Prod.fst h1) i, hC, hd, ?_⟩
    show g' = _
    rw [he, hh]
  · rintro ⟨D, L, C, hD, h1, hC, hd, rfl⟩
    exact dMap_mul_uMap_mem_tailUnipotent hD h1 L hC hd

theorem tailUnipotent_le_tailFlagStab : tailUnipotent r qA ≤ tailFlagStab r qA := fun g hg => by
  obtain ⟨⟨g', hg'⟩, -, rfl⟩ := tailUnipotent_le_ker hani hg
  exact hg'

theorem mem_tailUnipotent_iff_ker {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _} :
    g ∈ tailUnipotent r qA ↔ ∃ hg : g ∈ tailFlagStab r qA, stabDiagHom r qA hani ⟨g, hg⟩ = 1 := by
  constructor
  · intro hg
    obtain ⟨⟨g', hg'⟩, hker, rfl⟩ := tailUnipotent_le_ker hani hg
    exact ⟨hg', hker⟩
  · rintro ⟨hg, h1⟩
    obtain ⟨D, h, L, C, hD, -, hC, hd, he⟩ := exists_dMap_uMap_eq hani hg
    rw [stabDiagHom_apply] at h1
    change stabDiag g = 1 at h1
    rw [he, stabDiag_dMap_uMap] at h1
    have hh : h = 1 := LinearEquiv.ext fun a => LinearMap.congr_fun (congrArg Prod.snd h1) a
    rw [he, hh]
    exact dMap_mul_uMap_mem_tailUnipotent hD (fun i => congrFun (congrArg Prod.fst h1) i) L hC hd

omit hani [FiniteDimensional K A] in
theorem tailBorel_le_tailFlagStab : tailBorel r qA ≤ tailFlagStab r qA := fun g hg => by
  obtain ⟨hE, hF⟩ := mem_tailBorel.1 hg
  exact mem_tailFlagStab.2 ⟨orthElementaryGroup_le _ hE, hF⟩

theorem tailUnipotent_le_tailBorel : tailUnipotent r qA ≤ tailBorel r qA := fun _ hg =>
  mem_tailBorel.2 ⟨tailUnipotent_le hg,
    (mem_tailFlagStab.1 (tailUnipotent_le_tailFlagStab hani hg)).2⟩

omit hani [FiniteDimensional K A] in
theorem dBlock_diagGL (t : Fin r → Kˣ) : dBlock (diagGL t) = torusElt r K t := by
  refine LinearEquiv.ext fun w => funext fun c => ?_
  rw [dBlock_apply, torusElt_apply]
  rcases c with i | i
  · simp [diagGL, mulVec_diagonal]
  · have hinv : (((diagGL t)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
        diagonal fun i => (((t i)⁻¹ : Kˣ) : K) := rfl
    simp [hinv, mulVec_diagonal]

omit hani [FiniteDimensional K A] in
theorem tailDiag_eq_dMap (t : Fin r → Kˣ) (h : A ≃ₗ[K] A) : tailDiag r t h = dMap (diagGL t) h := by
  rw [tailDiag, dMap, dBlock_diagGL]

omit hani [FiniteDimensional K A] in
theorem diagGL_isUpperTriangular (t : Fin r → Kˣ) :
    ((diagGL t : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).IsUpperTriangular :=
  fun _ _ h => diagonal_apply_ne _ (ne_of_gt h)

omit hani [FiniteDimensional K A] in
theorem tailTorus_le_tailBorel : tailTorus r qA ≤ tailBorel r qA := by
  rintro _ ⟨hE, t, h, -, rfl⟩
  refine mem_tailBorel.2 ⟨hE, fun i _ _ => ?_⟩
  rw [tailDiag_eq_dMap]
  exact map_tailFlag_dMap (diagGL_isUpperTriangular t) h i

theorem tailUnipotent_normal : ((tailUnipotent r qA).subgroupOf (tailBorel r qA)).Normal := by
  refine ⟨fun u hu b => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hu ⊢
  obtain ⟨hus, hu1⟩ := (mem_tailUnipotent_iff_ker hani).1 hu
  have hbs := tailBorel_le_tailFlagStab b.2
  refine (mem_tailUnipotent_iff_ker hani).2 ⟨mul_mem (mul_mem hbs hus) (inv_mem hbs), ?_⟩
  have : (⟨(b * u * b⁻¹ : tailBorel r qA), mul_mem (mul_mem hbs hus) (inv_mem hbs)⟩ :
      tailFlagStab r qA) = ⟨b, hbs⟩ * ⟨u, hus⟩ * (⟨b, hbs⟩)⁻¹ := rfl
  rw [this, map_mul, map_mul, hu1, mul_one, ← map_mul, mul_inv_cancel, map_one]

omit [AddCommGroup A] [Module K A] [FiniteDimensional K A] hani in
theorem diag_ne_zero_of_upperTriangular {D : GL (Fin r) K}
    (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular) (i : Fin r) :
    (D : Matrix (Fin r) (Fin r) K) i i ≠ 0 := by
  have hdet : (D : Matrix (Fin r) (Fin r) K).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1
    D.isUnit |>.ne_zero
  rw [det_of_isUpperTriangular hD] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)

theorem exists_tailTorus_mul_tailUnipotent {b} (hb : b ∈ tailBorel r qA) :
    ∃ τ ∈ tailTorus r qA, ∃ υ ∈ tailUnipotent r qA, b = τ * υ := by
  obtain ⟨D, h, L, C, hD, hh, hC, hd, he⟩ := exists_dMap_uMap_eq hani
    (tailBorel_le_tailFlagStab hb)
  set t : Fin r → Kˣ := fun i => Units.mk0 ((D : Matrix (Fin r) (Fin r) K) i i)
    (diag_ne_zero_of_upperTriangular hD i) with ht
  set D₁ := (diagGL t)⁻¹ * D with hD₁
  have hD₁m : (D₁ : Matrix (Fin r) (Fin r) K) =
      diagonal (fun i => (((t i)⁻¹ : Kˣ) : K)) * (D : Matrix (Fin r) (Fin r) K) := rfl
  have hD₁u : (D₁ : Matrix (Fin r) (Fin r) K).IsUpperTriangular := fun i j hij => by
    rw [hD₁m, diagonal_mul, hD hij, mul_zero]
  have hD₁1 : ∀ i, (D₁ : Matrix (Fin r) (Fin r) K) i i = 1 := fun i => by
    rw [hD₁m, diagonal_mul]
    simp only [ht, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact inv_mul_cancel₀ (diag_ne_zero_of_upperTriangular hD i)
  have hυ : dMap D₁ 1 * uMap qA L C ∈ tailUnipotent r qA :=
    dMap_mul_uMap_mem_tailUnipotent hD₁u hD₁1 L hC hd
  have hb' : b = tailDiag r t h * (dMap D₁ 1 * uMap qA L C) := by
    rw [he, tailDiag_eq_dMap, ← mul_assoc, dMap_mul_dMap, hD₁, mul_inv_cancel_left, mul_one]
  refine ⟨tailDiag r t h, Subgroup.mem_inf.2 ⟨?_, t, h, hh, rfl⟩, _, hυ, hb'⟩
  have : tailDiag r t h = b * (dMap D₁ 1 * uMap qA L C)⁻¹ := by
    rw [hb', mul_inv_cancel_right]
  rw [this]
  exact mul_mem (mem_tailBorel.1 hb).1
    (inv_mem (show _ ∈ orthElementaryGroup (quadTail r qA) from tailUnipotent_le hυ))

theorem tailTorus_inf_tailUnipotent : tailTorus r qA ⊓ tailUnipotent r qA = ⊥ := by
  refine eq_bot_iff.2 fun τ ⟨hτT, hτU⟩ => ?_
  obtain ⟨-, t, h, hh, rfl⟩ := hτT
  obtain ⟨hs, h1⟩ := (mem_tailUnipotent_iff_ker hani).1 hτU
  rw [stabDiagHom_apply] at h1
  change stabDiag (tailDiag r t h) = 1 at h1
  rw [tailDiag_eq_dMap, ← mul_one (dMap (diagGL t) h), ← uMap_zero_zero (qA := qA),
    stabDiag_dMap_uMap] at h1
  have ht : t = 1 := funext fun i => Units.ext (by
    have := congrFun (congrArg Prod.fst h1) i
    simpa [diagGL] using this)
  have hh1 : h = 1 := LinearEquiv.ext fun a => LinearMap.congr_fun (congrArg Prod.snd h1) a
  rw [Subgroup.mem_bot, ht, hh1, tailDiag_eq_dMap]
  have : diagGL (1 : Fin r → Kˣ) = 1 := Units.ext (by simp [diagGL])
  rw [this, dMap_one_one]

theorem tailBorel_eq_mul :
    (tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) =
        (tailTorus r qA : Set _) * (tailUnipotent r qA : Set _) ∧
      (tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) =
        (tailUnipotent r qA : Set _) * (tailTorus r qA : Set _) := by
  have hTB := tailTorus_le_tailBorel (r := r) (qA := qA)
  have hUB := tailUnipotent_le_tailBorel hani (r := r)
  refine ⟨Set.Subset.antisymm (fun b hb => ?_) ?_, Set.Subset.antisymm (fun b hb => ?_) ?_⟩
  · obtain ⟨τ, hτ, υ, hυ, rfl⟩ := exists_tailTorus_mul_tailUnipotent hani hb
    exact ⟨τ, hτ, υ, hυ, rfl⟩
  · rintro _ ⟨τ, hτ, υ, hυ, rfl⟩
    exact mul_mem (hTB hτ) (hUB hυ)
  · obtain ⟨τ, hτ, υ, hυ, rfl⟩ := exists_tailTorus_mul_tailUnipotent hani hb
    refine ⟨τ * υ * τ⁻¹, ?_, τ, hτ, by group⟩
    have hN := (tailUnipotent_normal hani (r := r) (qA := qA)).conj_mem ⟨υ, hUB hυ⟩
      (Subgroup.mem_subgroupOf.2 hυ) ⟨τ, hTB hτ⟩
    exact Subgroup.mem_subgroupOf.1 hN
  · rintro _ ⟨υ, hυ, τ, hτ, rfl⟩
    exact mul_mem (hUB hυ) (hTB hτ)

theorem nonempty_quotient_mulEquiv_tailTorus :
    haveI := tailUnipotent_normal hani (r := r) (qA := qA)
    Nonempty (tailBorel r qA ⧸ (tailUnipotent r qA).subgroupOf (tailBorel r qA) ≃*
      tailTorus r qA) := by
  have : ((tailUnipotent r qA).subgroupOf (tailBorel r qA)).Normal := tailUnipotent_normal hani
  set ψ : tailTorus r qA →* tailBorel r qA ⧸ (tailUnipotent r qA).subgroupOf (tailBorel r qA) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion tailTorus_le_tailBorel) with hψ
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).2 fun τ hτ => ?_
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hτ
    have h1 : (τ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) ∈ tailTorus r qA ⊓ tailUnipotent r qA :=
      Subgroup.mem_inf.2 ⟨τ.2, hτ⟩
    rw [tailTorus_inf_tailUnipotent hani, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨τ, hτ, υ, hυ, hb⟩ := exists_tailTorus_mul_tailUnipotent hani b.2
    refine ⟨⟨τ, hτ⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    change (τ⁻¹ * (b : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)) ∈ tailUnipotent r qA
    rw [hb, inv_mul_cancel_left]
    exact hυ
  exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm⟩

theorem card_tailUnipotent [Finite K] :
    Nat.card (tailUnipotent r qA) = Nat.card K ^ (r * (r - 1) + r * Module.finrank K A) := by
  set f : posUnip r K × (Fin r → A) → tailUnipotent r qA := fun p =>
    ⟨prodHom A p.1.1 * uMap qA p.2 0,
      mul_mem (prodHom_mem_tailUnipotent p.1.2) (uMap_zero_mem_tailUnipotent p.2)⟩ with hf
  have hform : ∀ p : posUnip r K × (Fin r → A), ∃ (D : GL (Fin r) K) (C : Matrix (Fin r) (Fin r) K),
      (p.1 : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) = dBlock D * uBlock C ∧
      prodHom A p.1.1 * uMap qA p.2 0 = dMap D 1 * uMap qA p.2 C := by
    intro p
    obtain ⟨D, C, -, -, -, -, hM⟩ := mem_posUnip_iff.1 p.1.2
    refine ⟨D, C, eq_dBlock_mul_uBlock hM, ?_⟩
    rw [eq_dBlock_mul_uBlock hM, prodHom_dBlock_mul_uBlock, mul_assoc, uMap_zero_mul_uMap]
  have hinj : Function.Injective f := by
    intro p p' hpp'
    obtain ⟨D, C, hb, he⟩ := hform p
    obtain ⟨D', C', hb', he'⟩ := hform p'
    have h := congrArg Subtype.val hpp'
    change prodHom A p.1.1 * uMap qA p.2 0 = prodHom A p'.1.1 * uMap qA p'.2 0 at h
    rw [he, he'] at h
    obtain ⟨rfl, -, hL, rfl⟩ := dMap_uMap_injective h
    exact Prod.ext (Subtype.ext (hb.trans hb'.symm)) hL
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨D, L, C, hD, h1, hC, hd, rfl⟩ := (mem_tailUnipotent_iff hani).1 hg
    refine ⟨(⟨dBlock D * uBlock C, dBlock_mul_uBlock_mem_posUnip hD h1 hC hd⟩, L), ?_⟩
    apply Subtype.ext
    change prodHom A (dBlock D * uBlock C) * uMap qA L 0 = _
    rw [prodHom_dBlock_mul_uBlock, mul_assoc, uMap_zero_mul_uMap]
  have hA : Nat.card A = Nat.card K ^ Module.finrank K A := Module.natCard_eq_pow_finrank
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, card_posUnip,
    Nat.card_fun, Nat.card_fin, hA, ← pow_mul, ← pow_add, mul_comm (Module.finrank K A) r]

end Levi

theorem orthogonal_geometry_tail_upper_unipotent_matrices {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) :
    (∀ g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A),
      (g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) ∧ ∀ i, 1 ≤ i → i ≤ r →
          (tailFlag K A r i).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = tailFlag K A r i) ↔
        ∃ (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K),
          (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧
          h ∈ TauCeti.QuadraticMap.orthogonalGroup qA ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
          g = dMap D h * uMap qA L C) ∧
    (∀ (D D' : GL (Fin r) K) (h h' : A ≃ₗ[K] A) (L L' : Fin r → A)
        (C C' : Matrix (Fin r) (Fin r) K), dMap D h * uMap qA L C = dMap D' h' * uMap qA L' C' →
      D = D' ∧ h = h' ∧ L = L' ∧ C = C') ∧
    (∀ g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A),
      g ∈ tailUnipotent r qA ↔
        ∃ (D : GL (Fin r) K) (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K),
          (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧
          (∀ i, (D : Matrix (Fin r) (Fin r) K) i i = 1) ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
          g = dMap D 1 * uMap qA L C) ∧
    tailUnipotent r qA ≤ tailBorel r qA ∧
    ((tailUnipotent r qA).subgroupOf (tailBorel r qA)).Normal ∧
    ((tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) =
        (tailTorus r qA : Set _) * (tailUnipotent r qA : Set _) ∧
      (tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) =
        (tailUnipotent r qA : Set _) * (tailTorus r qA : Set _)) ∧
    tailTorus r qA ⊓ tailUnipotent r qA = ⊥ ∧
    (haveI := tailUnipotent_normal hani (r := r) (qA := qA);
      Nonempty (tailBorel r qA ⧸ (tailUnipotent r qA).subgroupOf (tailBorel r qA) ≃*
        tailTorus r qA)) ∧
    (Finite K →
      Nat.card (tailUnipotent r qA) = Nat.card K ^ (r * (r - 1) + r * Module.finrank K A)) := by
  refine ⟨fun g => ?_, fun D D' h h' L L' C C' heq => dMap_uMap_injective heq,
    fun g => mem_tailUnipotent_iff hani, tailUnipotent_le_tailBorel hani,
    tailUnipotent_normal hani, tailBorel_eq_mul hani, tailTorus_inf_tailUnipotent hani,
    nonempty_quotient_mulEquiv_tailTorus hani, fun _ => card_tailUnipotent hani⟩
  rw [← mem_tailFlagStab]
  refine ⟨fun hg => exists_dMap_uMap_eq hani hg, ?_⟩
  rintro ⟨D, h, L, C, hD, hh, hC, hd, rfl⟩
  exact dMap_mul_uMap_mem_tailFlagStab hD hh L hC hd

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
