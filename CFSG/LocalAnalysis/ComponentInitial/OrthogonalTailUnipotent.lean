module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPositive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Matrix
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

section QuadSum

theorem polar_finset_sum_left {ι : Type*} (s : Finset ι) (w : ι → A) (v : A) :
    polar qA (∑ i ∈ s, w i) v = ∑ i ∈ s, polar qA (w i) v := by
  have := map_sum ((polarBilin qA).flip v) w s
  simpa only [LinearMap.flip_apply, polarBilin_apply_apply] using this

theorem quad_sum_eq (w : Fin r → A) (s : Finset (Fin r)) :
    qA (∑ i ∈ s, w i) =
      ∑ i ∈ s, qA (w i) + ∑ i ∈ s, ∑ j ∈ s, if i < j then polar qA (w i) (w j) else 0 := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h1 : ∑ j ∈ s, (if a < j then polar qA (w a) (w j) else 0) = 0 :=
      Finset.sum_eq_zero fun j hj => ite_eq_right (not_lt.2 (ha j hj).le)
    have h2 : ∑ i ∈ s, (if i < a then polar qA (w i) (w a) else 0) =
        polar qA (w a) (∑ i ∈ s, w i) := by
      rw [polar_comm, polar_finset_sum_left]
      exact Finset.sum_congr rfl fun i hi => ite_eq_left (ha i hi)
    have hL : qA (∑ i ∈ insert a s, w i) =
        qA (w a) + qA (∑ i ∈ s, w i) + polar qA (w a) (∑ i ∈ s, w i) := by
      rw [Finset.sum_insert has, QuadraticMap.map_add qA]
    have hR : ∑ i ∈ insert a s, ∑ j ∈ insert a s,
        (if i < j then polar qA (w i) (w j) else 0) =
        ((if a < a then polar qA (w a) (w a) else 0) +
          ∑ j ∈ s, if a < j then polar qA (w a) (w j) else 0) +
        ∑ i ∈ s, ((if i < a then polar qA (w i) (w a) else 0) +
          ∑ j ∈ s, if i < j then polar qA (w i) (w j) else 0) := by
      rw [Finset.sum_insert has, Finset.sum_insert has]
      exact congrArg _ (Finset.sum_congr rfl fun i _ => Finset.sum_insert has)
    rw [hL, ih, Finset.sum_insert has, hR, ite_eq_right (lt_irrefl a), h1,
      Finset.sum_add_distrib, h2]
    ring

end QuadSum

section UMap

variable (qA) in
@[expose] def sMat (L : Fin r → A) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => if i = j then -qA (L i) else if i < j then -polar qA (L i) (L j) else 0

variable (qA) in
@[expose] def gramMat (L : Fin r → A) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j => polar qA (L i) (L j)

theorem sum_smul_add (L : Fin r → A) (y y' : Fin r → K) :
    ∑ j, (y j + y' j) • L j = ∑ j, y j • L j + ∑ j, y' j • L j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => add_smul _ _ _

theorem dotProduct_sMat_mulVec (L : Fin r → A) (y : Fin r → K) :
    y ⬝ᵥ (sMat qA L *ᵥ y) = -qA (∑ j, y j • L j) := by
  have hrow : ∀ i, y i * ∑ j, sMat qA L i j * y j = ∑ j, -((if i = j then y i ^ 2 * qA (L i)
      else 0) + if i < j then y i * y j * polar qA (L i) (L j) else 0) := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [sMat, of_apply]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, lt_irrefl, ite_false]
      ring
    · by_cases hlt : i < j
      · simp only [hij, hlt, ite_true, ite_false]
        ring
      · simp only [hij, hlt, ite_false]
        ring
  rw [quad_sum_eq]
  simp only [dotProduct, mulVec]
  rw [Finset.sum_congr rfl fun i _ => hrow i]
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, neg_add, map_smul_eq_sq, polar_smul_left_eq, polar_smul_right_eq]
  congr 2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem comp_inr_add (w w' : Fin r ⊕ Fin r → K) :
    (w + w') ∘ Sum.inr = w ∘ Sum.inr + w' ∘ Sum.inr :=
  rfl

theorem comp_inr_smul (t : K) (w : Fin r ⊕ Fin r → K) : (t • w) ∘ Sum.inr = t • (w ∘ Sum.inr) :=
  rfl

variable (qA) in
@[expose] def uLin (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K) :
    ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A) where
  toFun v := (Sum.elim (fun i => v.1 (.inl i) - polar qA (L i) v.2 +
      ((sMat qA L + C) *ᵥ (v.1 ∘ Sum.inr)) i) (v.1 ∘ Sum.inr), v.2 + ∑ j, v.1 (.inr j) • L j)
  map_add' v w := by
    refine Prod.ext (funext fun c => ?_) ?_
    · rcases c with i | i
      · simp only [Sum.elim_inl, Prod.fst_add, Prod.snd_add, Pi.add_apply]
        rw [comp_inr_add, mulVec_add, polar_add_right, Pi.add_apply]
        ring
      · rfl
    · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      abel
  map_smul' t v := by
    refine Prod.ext (funext fun c => ?_) ?_
    · rcases c with i | i
      · simp only [Sum.elim_inl, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        rw [comp_inr_smul, mulVec_smul, polar_smul_right_eq, Pi.smul_apply, smul_eq_mul]
        ring
      · rfl
    · simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        smul_add, Finset.smul_sum, mul_smul]

variable (qA) in
@[expose] def uInvLin (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K) :
    ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A) where
  toFun v := (Sum.elim (fun i => v.1 (.inl i) + polar qA (L i) v.2 -
      ((gramMat qA L + sMat qA L + C) *ᵥ (v.1 ∘ Sum.inr)) i) (v.1 ∘ Sum.inr),
    v.2 - ∑ j, v.1 (.inr j) • L j)
  map_add' v w := by
    refine Prod.ext (funext fun c => ?_) ?_
    · rcases c with i | i
      · simp only [Sum.elim_inl, Prod.fst_add, Prod.snd_add, Pi.add_apply]
        rw [comp_inr_add, mulVec_add, polar_add_right, Pi.add_apply]
        ring
      · rfl
    · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      abel
  map_smul' t v := by
    refine Prod.ext (funext fun c => ?_) ?_
    · rcases c with i | i
      · simp only [Sum.elim_inl, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        rw [comp_inr_smul, mulVec_smul, polar_smul_right_eq, Pi.smul_apply, smul_eq_mul]
        ring
      · rfl
    · simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        smul_sub, Finset.smul_sum, mul_smul]

theorem uLin_apply_inl (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K)
    (v : (Fin r ⊕ Fin r → K) × A) (i : Fin r) :
    (uLin qA L C v).1 (.inl i) = v.1 (.inl i) - polar qA (L i) v.2 +
      ((sMat qA L + C) *ᵥ (v.1 ∘ Sum.inr)) i :=
  rfl

theorem uLin_apply_inr (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K)
    (v : (Fin r ⊕ Fin r → K) × A) (i : Fin r) : (uLin qA L C v).1 (.inr i) = v.1 (.inr i) :=
  rfl

theorem uLin_apply_snd (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K)
    (v : (Fin r ⊕ Fin r → K) × A) : (uLin qA L C v).2 = v.2 + ∑ j, v.1 (.inr j) • L j :=
  rfl

theorem gramMat_mulVec (L : Fin r → A) (y : Fin r → K) (i : Fin r) :
    (gramMat qA L *ᵥ y) i = polar qA (L i) (∑ j, y j • L j) := by
  simp only [mulVec, dotProduct, gramMat, of_apply]
  rw [polar_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [polar_smul_right_eq, mul_comm]

theorem uInvLin_uLin (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K)
    (v : (Fin r ⊕ Fin r → K) × A) : uInvLin qA L C (uLin qA L C v) = v := by
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i
    · change (uLin qA L C v).1 (.inl i) + polar qA (L i) (uLin qA L C v).2 -
        ((gramMat qA L + sMat qA L + C) *ᵥ ((uLin qA L C v).1 ∘ Sum.inr)) i = v.1 (.inl i)
      have hy : (uLin qA L C v).1 ∘ Sum.inr = v.1 ∘ Sum.inr := rfl
      rw [hy, uLin_apply_inl, uLin_apply_snd, polar_add_right]
      simp only [add_mulVec, Pi.add_apply]
      rw [gramMat_mulVec]
      simp only [Function.comp_apply]
      ring
    · rfl
  · change (uLin qA L C v).2 - ∑ j, (uLin qA L C v).1 (.inr j) • L j = v.2
    rw [uLin_apply_snd]
    simp only [uLin_apply_inr, add_sub_cancel_right]

theorem uLin_uInvLin (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K)
    (v : (Fin r ⊕ Fin r → K) × A) : uLin qA L C (uInvLin qA L C v) = v := by
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i
    · rw [uLin_apply_inl]
      have hy : (uInvLin qA L C v).1 ∘ Sum.inr = v.1 ∘ Sum.inr := rfl
      change (v.1 (.inl i) + polar qA (L i) v.2 -
        ((gramMat qA L + sMat qA L + C) *ᵥ (v.1 ∘ Sum.inr)) i) -
          polar qA (L i) (v.2 - ∑ j, v.1 (.inr j) • L j) +
          ((sMat qA L + C) *ᵥ ((uInvLin qA L C v).1 ∘ Sum.inr)) i = v.1 (.inl i)
      rw [hy, polar_sub_right]
      simp only [add_mulVec, Pi.add_apply]
      rw [gramMat_mulVec]
      simp only [Function.comp_apply]
      ring
    · rfl
  · change (v.2 - ∑ j, v.1 (.inr j) • L j) + ∑ j, (uInvLin qA L C v).1 (.inr j) • L j = v.2
    exact sub_add_cancel _ _

variable (qA) in
@[expose] def uMap (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K) :
    ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  LinearEquiv.ofLinearMap (uLin qA L C) (uInvLin qA L C) (LinearMap.ext fun v => uLin_uInvLin L C v)
    (LinearMap.ext fun v => uInvLin_uLin L C v)

theorem uMap_apply (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K)
    (v : (Fin r ⊕ Fin r → K) × A) : uMap qA L C v = uLin qA L C v :=
  rfl

theorem uMap_mem_orthogonalGroup (L : Fin r → A) {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) : uMap qA L C ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
  rw [uMap_apply, quadTail_apply, quadTail_apply, quadPlus_eq_dotProduct, quadPlus_eq_dotProduct]
  have hx : (uLin qA L C v).1 ∘ Sum.inl = v.1 ∘ Sum.inl - (fun i => polar qA (L i) v.2) +
      (sMat qA L + C) *ᵥ (v.1 ∘ Sum.inr) := rfl
  have hy : (uLin qA L C v).1 ∘ Sum.inr = v.1 ∘ Sum.inr := rfl
  rw [hx, hy, uLin_apply_snd, QuadraticMap.map_add qA, add_dotProduct, sub_dotProduct,
    add_mulVec, add_dotProduct, dotProduct_comm (sMat qA L *ᵥ _), dotProduct_sMat_mulVec,
    mulVec_dotProduct_self_eq_zero hC hd]
  have hpol : (fun i => polar qA (L i) v.2) ⬝ᵥ (v.1 ∘ Sum.inr) =
      polar qA v.2 (∑ j, v.1 (.inr j) • L j) := by
    rw [polar_sum_right]
    simp only [dotProduct, polar_smul_right_eq, Function.comp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [polar_comm, mul_comm]
  rw [hpol]
  simp only [Function.comp_apply]
  ring

theorem sMat_zero : sMat qA (0 : Fin r → A) = 0 := by
  ext i j
  simp only [sMat, of_apply, Pi.zero_apply, QuadraticMap.map_zero, polar_zero_left, neg_zero,
    Matrix.zero_apply]
  split_ifs <;> rfl

theorem uMap_zero_mul_uMap (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K) :
    uMap qA 0 C * uMap qA L 0 = uMap qA L C := by
  refine LinearEquiv.ext fun v => Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i
    · rw [LinearEquiv.mul_apply, uMap_apply, uMap_apply, uMap_apply, uLin_apply_inl,
        uLin_apply_inl, uLin_apply_inl, sMat_zero]
      have hy : (uLin qA L 0 v).1 ∘ Sum.inr = v.1 ∘ Sum.inr := rfl
      rw [hy, uLin_apply_snd]
      simp only [Pi.zero_apply, polar_zero_left, sub_zero, zero_add, add_zero, add_mulVec,
        Pi.add_apply]
      ring
    · rfl
  · rw [LinearEquiv.mul_apply, uMap_apply, uMap_apply, uMap_apply, uLin_apply_snd, uLin_apply_snd,
      uLin_apply_snd]
    simp only [Pi.zero_apply, smul_zero, Finset.sum_const_zero, add_zero]

theorem uMap_apply_of_fst_inr (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K)
    {v : (Fin r ⊕ Fin r → K) × A} (hy : ∀ i, v.1 (.inr i) = 0) (ha : v.2 = 0) :
    uMap qA L C v = v := by
  have hy' : v.1 ∘ Sum.inr = 0 := funext hy
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i
    · rw [uMap_apply, uLin_apply_inl, hy', mulVec_zero, Pi.zero_apply, ha, polar_zero_right]
      ring
    · rfl
  · rw [uMap_apply, uLin_apply_snd, ha, zero_add]
    simp [hy]

theorem mem_tailFlag_top_iff {v : (Fin r ⊕ Fin r → K) × A} :
    v ∈ tailFlag K A r r ↔ (∀ i, v.1 (.inr i) = 0) ∧ v.2 = 0 := by
  rw [tailFlag_eq_map, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨mem_flag_top.1 hw, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨v.1, mem_flag_top.2 h1, Prod.ext rfl h2.symm⟩

theorem tailFlag_le_top (k : ℕ) : tailFlag K A r k ≤ tailFlag K A r r := by
  rw [tailFlag_eq_map, tailFlag_eq_map]
  rcases le_total k r with hk | hk
  · exact Submodule.map_mono (Submodule.span_mono (Set.image_mono fun j (hj : (j : ℕ) < k) =>
      show (j : ℕ) < r by omega))
  · rw [flag_eq_top_of_le hk]

theorem map_tailFlag_uMap (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K) (k : ℕ) :
    (tailFlag K A r k).map (uMap qA L C : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) =
      tailFlag K A r k := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨h1, h2⟩ := mem_tailFlag_top_iff.1 (tailFlag_le_top k hw)
    rw [LinearEquiv.coe_coe, uMap_apply_of_fst_inr L C h1 h2]
    exact hw
  · intro hv
    obtain ⟨h1, h2⟩ := mem_tailFlag_top_iff.1 (tailFlag_le_top k hv)
    exact ⟨v, hv, uMap_apply_of_fst_inr L C h1 h2⟩

end UMap

section DMap

@[expose] noncomputable def dBlock (D : GL (Fin r) K) :
    (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  LinearEquiv.ofLinearMap
    (Matrix.toLin' (fromBlocks (D : Matrix (Fin r) (Fin r) K) 0 0
      ((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ))
    (Matrix.toLin' (fromBlocks ((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) 0 0
      (D : Matrix (Fin r) (Fin r) K)ᵀ))
    (by
      rw [← Matrix.toLin'_mul, fromBlocks_multiply]
      simp [← Matrix.transpose_mul, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, fromBlocks_multiply]
      simp [← Matrix.transpose_mul, Matrix.toLin'_one])

theorem toMatrix'_dBlock (D : GL (Fin r) K) :
    LinearMap.toMatrix' ((dBlock D : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) : (Fin r ⊕ Fin r → K) →ₗ[K] _) =
      fromBlocks (D : Matrix (Fin r) (Fin r) K) ((D : Matrix (Fin r) (Fin r) K) * 0) 0
        ((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ := by
  rw [mul_zero]
  exact LinearMap.toMatrix'_toLin' _

theorem dBlock_apply (D : GL (Fin r) K) (w : Fin r ⊕ Fin r → K) :
    dBlock D w = Sum.elim ((D : Matrix (Fin r) (Fin r) K) *ᵥ (w ∘ Sum.inl))
      (((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ (w ∘ Sum.inr)) := by
  change Matrix.toLin' _ w = _
  rw [Matrix.toLin'_apply, fromBlocks_mulVec_apply]
  simp

@[expose] noncomputable def dMap (D : GL (Fin r) K) (h : A ≃ₗ[K] A) :
    ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  (dBlock D).prodCongr h

theorem dMap_apply (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (v : (Fin r ⊕ Fin r → K) × A) :
    dMap D h v = (Sum.elim ((D : Matrix (Fin r) (Fin r) K) *ᵥ (v.1 ∘ Sum.inl))
      (((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ (v.1 ∘ Sum.inr)), h v.2) := by
  rw [dMap, LinearEquiv.prodCongr_apply, dBlock_apply]

theorem dBlock_mem_posBorel {D : GL (Fin r) K}
    (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular) :
    dBlock D ∈ posBorel r K :=
  mem_posBorel_iff.2 ⟨D, 0, hD, by simp, fun i => rfl, toMatrix'_dBlock D⟩

theorem map_tailFlag_prodCongr (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
    (h : A ≃ₗ[K] A) (k : ℕ) :
    (tailFlag K A r k).map ((g.prodCongr h : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
      ((flag r K k).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))).map
        (LinearMap.inl K (Fin r ⊕ Fin r → K) A) := by
  rw [tailFlag_eq_map, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply, map_zero]

theorem map_tailFlag_prodCongr_eq_iff (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
    (h : A ≃ₗ[K] A) (k : ℕ) :
    (tailFlag K A r k).map ((g.prodCongr h : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = tailFlag K A r k ↔
      (flag r K k).map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) = flag r K k := by
  rw [map_tailFlag_prodCongr, tailFlag_eq_map]
  exact (Submodule.map_injective_of_injective LinearMap.inl_injective).eq_iff

theorem dMap_mem_orthogonalGroup (D : GL (Fin r) K) {h : A ≃ₗ[K] A}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup qA) :
    dMap D h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
  rw [dMap_apply, quadTail_apply, quadTail_apply, map_of_mem hh, quadPlus_eq_dotProduct,
    quadPlus_eq_dotProduct]
  congr 1
  change ((D : Matrix (Fin r) (Fin r) K) *ᵥ (v.1 ∘ Sum.inl)) ⬝ᵥ
    ((((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) *ᵥ (v.1 ∘ Sum.inr)) = _
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, dotProduct_comm]

theorem map_tailFlag_dMap {D : GL (Fin r) K} (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h : A ≃ₗ[K] A) (k : ℕ) :
    (tailFlag K A r k).map (dMap D h : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = tailFlag K A r k :=
  (map_tailFlag_prodCongr_eq_iff (dBlock D) h k).2 ((mem_posBorel.1 (dBlock_mem_posBorel hD)).2 k)

end DMap

section Stab

variable (r qA) in
@[expose] noncomputable def tailFlagStab :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) ⊓
    ⨅ i ∈ Set.Icc 1 r, MulAction.stabilizer (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) (tailFlag K A r i)

theorem mem_tailFlagStab {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} :
    g ∈ tailFlagStab r qA ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) ∧
      ∀ i, 1 ≤ i → i ≤ r →
        (tailFlag K A r i).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = tailFlag K A r i := by
  simp only [tailFlagStab, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_Icc, and_imp,
    Submodule.mem_stabilizer_submodule_iff_map_eq]
  rfl

theorem tailFlag_zero : tailFlag K A r 0 = ⊥ := by
  rw [tailFlag_eq_map, flag_zero, Submodule.map_bot]

theorem tailFlag_eq_top_of_le {i : ℕ} (hi : r ≤ i) : tailFlag K A r i = tailFlag K A r r := by
  rw [tailFlag_eq_map, tailFlag_eq_map, flag_eq_top_of_le hi]

theorem map_tailFlag_of_mem_tailFlagStab
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} (hg : g ∈ tailFlagStab r qA)
    (k : ℕ) :
    (tailFlag K A r k).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = tailFlag K A r k := by
  obtain ⟨-, hF⟩ := mem_tailFlagStab.1 hg
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [tailFlag_zero, Submodule.map_bot]
  · by_cases hkr : k ≤ r
    · exact hF k hk hkr
    · rw [tailFlag_eq_top_of_le (by omega)]
      rcases Nat.eq_zero_or_pos r with hr | hr
      · have h0 : tailFlag K A r r = ⊥ := by
          rw [tailFlag, Submodule.span_eq_bot]
          rintro _ ⟨j, -, rfl⟩
          exact absurd j.isLt (by omega)
        rw [h0, Submodule.map_bot]
      · exact hF r hr le_rfl

theorem fst_inr_apply_eq_zero {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : g ∈ tailFlagStab r qA) {v : (Fin r ⊕ Fin r → K) × A} (hv : ∀ i, v.1 (.inr i) = 0)
    (i : Fin r) : (g v).1 (.inr i) = 0 := by
  have hgO := (mem_tailFlagStab.1 hg).1
  have hX := map_tailFlag_of_mem_tailFlagStab hg r
  have hmem : hypVec K A (.inl i) ∈ tailFlag K A r r :=
    Submodule.subset_span ⟨i, i.isLt, rfl⟩
  rw [← hX] at hmem
  obtain ⟨z, hz, hzi⟩ := hmem
  obtain ⟨hz1, hz2⟩ := mem_tailFlag_top_iff.1 hz
  have h := polar_hypVec (qA := qA) (g v) (.inl i)
  rw [Sum.swap_inl] at h
  rw [← h, ← hzi, LinearEquiv.coe_coe, polar_map_of_mem hgO, polar_quadTail, hz2,
    polar_zero_right, add_zero, polar_quadPlus]
  exact Finset.sum_eq_zero fun k _ => by simp [hv k, hz1 k]

theorem uMap_symm_tail (L : Fin r → A) (a : A) :
    (uMap qA L 0).symm ((0 : Fin r ⊕ Fin r → K), a) =
      (Sum.elim (fun i => polar qA (L i) a) 0, 0) + ((0 : Fin r ⊕ Fin r → K), a) := by
  change uInvLin qA L 0 (0, a) = _
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i
    · change (0 : Fin r ⊕ Fin r → K) (.inl i) + polar qA (L i) a -
        ((gramMat qA L + sMat qA L + 0) *ᵥ ((0 : Fin r ⊕ Fin r → K) ∘ Sum.inr)) i = _
      have h0 : ((0 : Fin r ⊕ Fin r → K) ∘ Sum.inr) = 0 := rfl
      simp [h0]
    · change (0 : Fin r ⊕ Fin r → K) (Sum.inr i) = _
      simp
  · change a - ∑ j, (0 : Fin r ⊕ Fin r → K) (.inr j) • L j = _
    simp

theorem uMap_symm_hypVec_inr (L : Fin r → A) (j : Fin r) :
    (uMap qA L 0).symm (hypVec K A (.inr j)) =
      (Sum.elim (fun i => -((gramMat qA L + sMat qA L) *ᵥ Pi.single j 1) i) 0, 0) +
        hypVec K A (.inr j) + ((0 : Fin r ⊕ Fin r → K), -L j) := by
  change uInvLin qA L 0 (hypVec K A (.inr j)) = _
  have hy : (hypVec K A (.inr j) : (Fin r ⊕ Fin r → K) × A).1 ∘ Sum.inr = Pi.single j 1 := by
    funext k
    simp [hypVec, Pi.single_apply]
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i
    · change (hypVec K A (.inr j) : (Fin r ⊕ Fin r → K) × A).1 (.inl i) +
        polar qA (L i) (hypVec K A (.inr j) : (Fin r ⊕ Fin r → K) × A).2 -
        ((gramMat qA L + sMat qA L + 0) *ᵥ
          ((hypVec K A (.inr j) : (Fin r ⊕ Fin r → K) × A).1 ∘ Sum.inr)) i = _
      rw [hy, add_zero]
      simp [hypVec]
    · change (Pi.single (Sum.inr j) 1 : Fin r ⊕ Fin r → K) (Sum.inr i) = _
      simp [hypVec]
  · change (hypVec K A (.inr j) : (Fin r ⊕ Fin r → K) × A).2 -
      ∑ k, (hypVec K A (.inr j) : (Fin r ⊕ Fin r → K) × A).1 (.inr k) • L k = _
    simp [hypVec, Pi.single_apply]

end Stab

section Decomp

variable [FiniteDimensional K A] (hani : qA.Anisotropic)
  {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} (hg : g ∈ tailFlagStab r qA)
include hani hg

theorem exists_tail_block :
    ∃ h : A ≃ₗ[K] A, h ∈ TauCeti.QuadraticMap.orthogonalGroup qA ∧
      ∀ a, (g ((0 : Fin r ⊕ Fin r → K), a)).2 = h a := by
  have hgO := (mem_tailFlagStab.1 hg).1
  set hL : A →ₗ[K] A := (LinearMap.snd K (Fin r ⊕ Fin r → K) A).comp
    ((g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _).comp (LinearMap.inr K (Fin r ⊕ Fin r → K) A))
    with hhL
  have happ : ∀ a, hL a = (g ((0 : Fin r ⊕ Fin r → K), a)).2 := fun a => rfl
  have hq : ∀ a, qA (hL a) = qA a := by
    intro a
    have h1 := map_of_mem hgO ((0 : Fin r ⊕ Fin r → K), a)
    have hX : ∀ i, (g ((0 : Fin r ⊕ Fin r → K), a)).1 (.inr i) = 0 :=
      fst_inr_apply_eq_zero hg (fun i => rfl)
    rw [quadTail_apply, quadTail_apply, quadPlus_apply, QuadraticMap.map_zero, zero_add,
      Finset.sum_eq_zero fun i _ => by rw [hX i, mul_zero], zero_add] at h1
    rw [happ, h1]
  have hinj : Function.Injective hL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hani a (by rw [← hq, ha, QuadraticMap.map_zero])
  have hbij : Function.Bijective hL := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  refine ⟨LinearEquiv.ofBijective hL hbij,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun a => hq a, fun a => rfl⟩

theorem exists_dMap_uMap_eq :
    ∃ (D : GL (Fin r) K) (h : A ≃ₗ[K] A) (L : Fin r → A) (C : Matrix (Fin r) (Fin r) K),
      (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular ∧
      h ∈ TauCeti.QuadraticMap.orthogonalGroup qA ∧ Cᵀ = -C ∧ (∀ i, C i i = 0) ∧
      g = dMap D h * uMap qA L C := by
  have hgO := (mem_tailFlagStab.1 hg).1
  obtain ⟨h, hh, hgh⟩ := exists_tail_block hani hg
  set L : Fin r → A := fun j => h.symm ((g (hypVec K A (.inr j))).2) with hLdef
  set u := uMap qA L 0 with hu
  have huO : u ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) :=
    uMap_mem_orthogonalGroup L (by simp) fun i => rfl
  set g' := g * u⁻¹ with hg'
  have hg'O : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) :=
    mul_mem hgO (inv_mem huO)
  have hg'apply : ∀ v, g' v = g (u.symm v) := fun v => by
    rw [hg', LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  have hgX : ∀ v : (Fin r ⊕ Fin r → K) × A, (∀ i, v.1 (.inr i) = 0) → v.2 = 0 →
      (g v).2 = 0 := by
    intro v h1 h2
    have hv : v ∈ tailFlag K A r r := mem_tailFlag_top_iff.2 ⟨h1, h2⟩
    have hmem : g v ∈ (tailFlag K A r r).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) :=
      Submodule.mem_map_of_mem hv
    rw [map_tailFlag_of_mem_tailFlagStab hg r] at hmem
    exact (mem_tailFlag_top_iff.1 hmem).2
  have hA : ∀ w : Fin r ⊕ Fin r → K, (g' (w, 0)).2 = 0 := by
    have hzero : (LinearMap.snd K (Fin r ⊕ Fin r → K) A).comp
        ((g' : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _).comp
          (LinearMap.inl K (Fin r ⊕ Fin r → K) A)) = 0 := by
      refine LinearMap.pi_ext fun c x => ?_
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.zero_apply,
        LinearEquiv.coe_coe, LinearMap.snd_apply]
      have hsx : ((Pi.single c x, 0) : (Fin r ⊕ Fin r → K) × A) = x • hypVec K A c := by
        rw [hypVec_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
      rw [hsx, map_smul, Prod.smul_snd, hg'apply]
      rcases c with i | j
      · have hfix : u.symm (hypVec K A (.inl i)) = hypVec K A (.inl i) := by
          rw [LinearEquiv.symm_apply_eq, hu]
          exact (uMap_apply_of_fst_inr L 0 (fun k => by simp [hypVec]) rfl).symm
        rw [hfix, hgX _ (fun k => by simp [hypVec]) rfl, smul_zero]
      · rw [hu, uMap_symm_hypVec_inr, map_add, map_add, Prod.snd_add, Prod.snd_add,
          hgX _ (fun k => rfl) rfl, hgh, map_neg, hLdef, LinearEquiv.apply_symm_apply,
          zero_add, add_neg_cancel, smul_zero]
    intro w
    exact LinearMap.congr_fun hzero w
  set φ : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) :=
    (LinearMap.fst K (Fin r ⊕ Fin r → K) A).comp ((g' : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _).comp
      (LinearMap.inl K (Fin r ⊕ Fin r → K) A)) with hφ
  have hφapply : ∀ w, g' (w, 0) = (φ w, 0) := fun w => Prod.ext rfl (hA w)
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : g' (w, 0) = 0 := by rw [hφapply, hw]; rfl
    have := g'.injective (h0.trans (map_zero g').symm)
    exact congrArg Prod.fst this
  have hφbij : Function.Bijective φ := ⟨hφinj, LinearMap.injective_iff_surjective.1 hφinj⟩
  have hT : ∀ a : A, g' ((0 : Fin r ⊕ Fin r → K), a) = (0, h a) := by
    intro a
    have h2 : (g' ((0 : Fin r ⊕ Fin r → K), a)).2 = h a := by
      rw [hg'apply, hu, uMap_symm_tail, map_add, Prod.snd_add, hgX _ (fun k => rfl) rfl, hgh,
        zero_add]
    refine Prod.ext ?_ h2
    refine eq_zero_of_polar_eq_zero (nondegenerate_polarBilin_quadPlus r K) fun w => ?_
    obtain ⟨z, hz⟩ := hφbij.2 w
    have h3 := polar_map_of_mem hg'O ((0 : Fin r ⊕ Fin r → K), a) (z, 0)
    rw [hφapply, hz, polar_quadTail, polar_quadTail, polar_zero_right, add_zero,
      polar_zero_left, polar_zero_right, add_zero] at h3
    exact h3
  set gH := LinearEquiv.ofBijective φ hφbij with hgH
  have hg'eq : g' = gH.prodCongr h := by
    refine LinearEquiv.ext fun v => ?_
    have hv : v = (v.1, 0) + ((0 : Fin r ⊕ Fin r → K), v.2) := by simp
    rw [hv, map_add, hφapply, hT, LinearEquiv.prodCongr_apply]
    simp [hgH]
  have hgHmem : gH ∈ posBorel r K := by
    have hflag : ∀ k, (flag r K k).map (gH : (Fin r ⊕ Fin r → K) →ₗ[K] _) = flag r K k := by
      intro k
      have hus : (tailFlag K A r k).map (u.symm : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) =
          tailFlag K A r k := by
        have h1 := map_tailFlag_uMap (qA := qA) L 0 k
        rw [← hu] at h1
        ext x
        rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
        constructor
        · intro hx
          rw [← h1] at hx
          obtain ⟨y, hy, hyx⟩ := hx
          rwa [u.injective hyx] at hy
        · intro hx
          rw [← h1]
          exact Submodule.mem_map_of_mem hx
      have hcomp : ((g' : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _) :
          ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
          (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _).comp
            (u.symm : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) :=
        LinearMap.ext fun v => hg'apply v
      rw [← map_tailFlag_prodCongr_eq_iff gH h k, ← hg'eq, hcomp, Submodule.map_comp, hus,
        map_tailFlag_of_mem_tailFlagStab hg k]
    refine mem_posBorel.2 ⟨⟨?_, hflag r⟩, hflag⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun w => ?_
    have h4 := map_of_mem hg'O (w, 0)
    rw [hφapply, quadTail_apply, quadTail_apply, QuadraticMap.map_zero, add_zero, add_zero] at h4
    exact h4
  obtain ⟨D, C, hD, hC, hd, hM⟩ := mem_posBorel_iff.1 hgHmem
  refine ⟨D, h, L, C, hD, hh, hC, hd, ?_⟩
  have hgg : g = g' * u := by rw [hg', inv_mul_cancel_right]
  rw [hgg, hg'eq, ← uMap_zero_mul_uMap, ← mul_assoc, hu]
  congr 1
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.prodCongr_apply, LinearEquiv.mul_apply, dMap_apply, apply_eq_of_toMatrix' hM]
  refine Prod.ext ?_ ?_
  · change Sum.elim _ _ = Sum.elim _ _
    have hx : (uMap qA (0 : Fin r → A) C v).1 ∘ Sum.inl = v.1 ∘ Sum.inl + C *ᵥ (v.1 ∘ Sum.inr) := by
      funext i
      rw [Function.comp_apply, uMap_apply, uLin_apply_inl, sMat_zero, zero_add]
      simp
    have hy : (uMap qA (0 : Fin r → A) C v).1 ∘ Sum.inr = v.1 ∘ Sum.inr := rfl
    rw [hx, hy]
  · change h v.2 = h (uMap qA (0 : Fin r → A) C v).2
    rw [uMap_apply, uLin_apply_snd]
    simp

end Decomp

theorem dMap_uMap_injective {D D' : GL (Fin r) K} {h h' : A ≃ₗ[K] A} {L L' : Fin r → A}
    {C C' : Matrix (Fin r) (Fin r) K} (heq : dMap D h * uMap qA L C = dMap D' h' * uMap qA L' C') :
    D = D' ∧ h = h' ∧ L = L' ∧ C = C' := by
  have happ := fun v => LinearEquiv.congr_fun heq v
  have hD : D = D' := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h1 := congrArg (fun v => v.1 (Sum.inl i)) (happ (hypVec K A (.inl j)))
    simp only [LinearEquiv.mul_apply] at h1
    rw [uMap_apply_of_fst_inr L C (fun k => by simp [hypVec]) rfl,
      uMap_apply_of_fst_inr L' C' (fun k => by simp [hypVec]) rfl, dMap_apply, dMap_apply] at h1
    have hx : (hypVec K A (.inl j) : (Fin r ⊕ Fin r → K) × A).1 ∘ Sum.inl = Pi.single j 1 := by
      funext k
      simp [hypVec, Pi.single_apply]
    simp only [Sum.elim_inl, hx, mulVec_single_one, col_apply] at h1
    exact h1
  subst hD
  have hh : h = h' := LinearEquiv.ext fun a => by
    have h1 := congrArg Prod.snd (happ ((0 : Fin r ⊕ Fin r → K), a))
    simpa [LinearEquiv.mul_apply, dMap_apply, uMap_apply, uLin_apply_snd] using h1
  subst hh
  have hf : ∀ j, L j = L' j ∧ (sMat qA L + C) *ᵥ Pi.single j 1 =
      (sMat qA L' + C') *ᵥ Pi.single j 1 := by
    intro j
    have h1 := happ (hypVec K A (.inr j))
    simp only [LinearEquiv.mul_apply, dMap_apply] at h1
    have hy : ∀ (M : Fin r → A) (N : Matrix (Fin r) (Fin r) K),
        (uMap qA M N (hypVec K A (.inr j))).1 ∘ Sum.inr = Pi.single j 1 := fun M N => by
      funext k
      change (Pi.single (Sum.inr j) 1 : Fin r ⊕ Fin r → K) (Sum.inr k) = _
      simp [Pi.single_apply]
    have hsnd : ∀ (M : Fin r → A) (N : Matrix (Fin r) (Fin r) K),
        (uMap qA M N (hypVec K A (.inr j))).2 = M j := fun M N => by
      rw [uMap_apply, uLin_apply_snd]
      simp [hypVec, Pi.single_apply]
    have hfst : ∀ (M : Fin r → A) (N : Matrix (Fin r) (Fin r) K),
        (uMap qA M N (hypVec K A (.inr j))).1 ∘ Sum.inl = (sMat qA M + N) *ᵥ Pi.single j 1 :=
      fun M N => by
        funext k
        rw [Function.comp_apply, uMap_apply, uLin_apply_inl]
        have hy' : (hypVec K A (.inr j) : (Fin r ⊕ Fin r → K) × A).1 ∘ Sum.inr =
            Pi.single j 1 := by
          funext k
          simp [hypVec, Pi.single_apply]
        rw [hy']
        simp [hypVec]
    refine ⟨h.injective ?_, ?_⟩
    · have := congrArg Prod.snd h1
      simp only at this
      rwa [hsnd, hsnd] at this
    · have := congrArg (fun v => v.1 ∘ Sum.inl) h1
      simp only [Sum.elim_comp_inl, hfst] at this
      have h2 := congrArg (fun z => ((D⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ z) this
      simp only [mulVec_mulVec] at h2
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul, Matrix.one_mul] at h2
  have hL : L = L' := funext fun j => (hf j).1
  subst hL
  refine ⟨rfl, rfl, rfl, ?_⟩
  ext i j
  have := congrFun (hf j).2 i
  simp only [mulVec_single_one, col_apply] at this
  exact add_left_cancel this

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
