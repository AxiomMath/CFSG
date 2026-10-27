module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4FrobTensor
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Eta

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.Open
  CFSG.StandardType.TriBridge CFSG.StandardType.Triality CFSG.StandardType.AutOm
  QuadraticMap CFSG.LieType.D4Small
open scoped Matrix

section Model


variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] def natMat : adjointGroup .D4 K →* Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K where
  toFun g := LinearMap.toMatrix'
    ((eta K g : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).toLinearMap
  map_one' := by
    rw [map_one]
    exact LinearMap.toMatrix'_id
  map_mul' g h := by
    rw [map_mul, ← LinearMap.toMatrix'_mul]
    rfl

variable (k : Type) [Field k] [Algebra K k] [CharP k 2]

@[expose] def tensorD4 (S : Finset ℕ) :
    Representation k (adjointGroup .D4 K) ((S → Fin 4 ⊕ Fin 4) → k) :=
  frobTensorRep k (natMat K) S

@[expose] def hwVec (S : Finset ℕ) : (S → Fin 4 ⊕ Fin 4) → k :=
  Pi.single (fun _ => Sum.inl 1) 1

@[expose] def chiT (S : Finset ℕ) : adjointGroup .D4 K → k :=
  fun h => tensorD4 (K := K) k S h (hwVec k S) (fun _ => Sum.inl 1)

@[expose] def frobNatRep (b : ℕ) : Representation k (adjointGroup .D4 K) (Fin 4 ⊕ Fin 4 → k) where
  toFun g := Matrix.toLin' ((frobHom (K := K) k b).mapMatrix (natMat K g))
  map_one' := by rw [map_one, map_one]; exact Matrix.toLin'_one
  map_mul' g h := by rw [map_mul, map_mul, Matrix.toLin'_mul]; rfl

private def eI (i : Fin 4) : Fin 4 ⊕ Fin 4 := Sum.inl i

private def fI (i : Fin 4) : Fin 4 ⊕ Fin 4 := Sum.inr i

private theorem eta_val_eq (x : adjointGroup .D4 K) :
    eta K x = plusDerivedEquiv 4 K (by norm_num)
      ((statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm
        ((CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose x)) := rfl

private theorem eta_apply (x : adjointGroup .D4 K) (v : Fin 4 ⊕ Fin 4 → K) :
    ((eta K x : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v =
      (reindexVectorEquiv (plusIndexEquiv 4)).symm
        (((((CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose x :
              Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          reindexVectorEquiv (plusIndexEquiv 4) v) := by
  rw [eta_val_eq, plusDerivedEquiv_val]
  conv_lhs => rw [← LinearEquiv.symm_apply_apply (reindexVectorEquiv (plusIndexEquiv 4)) v]
  exact statedDerivedReindexEquiv_symm_vector (plusIndexEquiv 4) (quadPlus 4 K)
    (coe_quadPlus 4 K)
    ((CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose x)
    (reindexVectorEquiv (plusIndexEquiv 4) v)

private theorem eta_pinnedX_apply {β : Fin Tag.D4.rank → ℤ} (hβ : β ∈ rootFinset .D4)
    {i j : Fin 4} (hij : i ≠ j) {s t : Bool} (h : toStdD 4 (bLinv β) = lv i j s t)
    (c : K) (v : Fin 4 ⊕ Fin 4 → K) :
    ((eta K ⟨pinnedX .D4 K β c, pinnedX_mem_adjointGroup β c⟩ :
        orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v =
      v + (c * polar (quadPlus 4 K) v (plusVec 4 K j t)) • plusVec 4 K i s +
        (c * polar (quadPlus 4 K) v (plusVec 4 K i s)) • plusVec 4 K j t := by
  rw [eta_apply]
  simp only [CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8.choose_spec β hβ c]
  rw [CFSG.LieType.SpinGeom.X8_mulVec_eich hij h c, map_add, map_add, map_smul, map_smul,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    CFSG.StandardType.AutOm.polar_reindex_plus, CFSG.StandardType.AutOm.polar_reindex_plus]

private theorem bLinv_single_zero :
    toStdD 4 (bLinv (Pi.single (0 : Fin 4) 1)) = lv 1 2 true false := by
  decide +kernel

private theorem bLinv_single_one :
    toStdD 4 (bLinv (Pi.single (1 : Fin 4) 1)) = lv 0 3 false true := by
  decide +kernel

private theorem bLinv_single_two :
    toStdD 4 (bLinv (Pi.single (2 : Fin 4) 1)) = lv 2 3 true false := by
  decide +kernel

private theorem bLinv_single_three :
    toStdD 4 (bLinv (Pi.single (3 : Fin 4) 1)) = lv 0 3 true true := by
  decide +kernel

private theorem bLinv_neg_single_zero :
    toStdD 4 (bLinv (-Pi.single (0 : Fin 4) 1)) = lv 2 1 true false := by
  decide +kernel

private theorem bLinv_single_neg_zero :
    toStdD 4 (bLinv (Pi.single (0 : Fin 4) (-1))) = lv 2 1 true false := by
  decide +kernel

private theorem bLinv_neg_single_one :
    toStdD 4 (bLinv (-Pi.single (1 : Fin 4) 1)) = lv 0 3 true false := by
  decide +kernel

private theorem bLinv_neg_single_two :
    toStdD 4 (bLinv (-Pi.single (2 : Fin 4) 1)) = lv 3 2 true false := by
  decide +kernel

private theorem bLinv_neg_single_three :
    toStdD 4 (bLinv (-Pi.single (3 : Fin 4) 1)) = lv 0 3 false false := by
  decide +kernel

private theorem xC_eq_pinned (i : Fin 4) (c : K) :
    xC .D4 K i c = ⟨pinnedX .D4 K (Pi.single i 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  refine Subtype.ext ?_
  exact (pinnedX_single .D4 K i c).symm

private theorem yC_eq_pinned (i : Fin 4) (c : K) :
    yC .D4 K i c = ⟨pinnedX .D4 K (-Pi.single i 1) c, pinnedX_mem_adjointGroup _ c⟩ := by
  refine Subtype.ext ?_
  exact (pinnedX_neg_single .D4 K i c).symm

private theorem eta_xC_zero (c : K) (a : Fin 4) (r : Bool) :
    ((eta K (xC .D4 K (0 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K a r) =
      plusVec 4 K a r +
        (if a = 2 ∧ r = true then c else 0) • plusVec 4 K (1 : Fin 4) true +
        (if a = 1 ∧ r = false then c else 0) • plusVec 4 K (2 : Fin 4) false := by
  rw [xC_eq_pinned]
  rw [eta_pinnedX_apply (β := Pi.single (0 : Fin 4) 1) (mem_rootFinset.mpr (isRoot_single _ _))
    (by decide) bLinv_single_zero c (plusVec 4 K a r)]
  rw [polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 2) (s := r) (t := false),
    polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 1) (s := r) (t := true)]
  split_ifs <;> simp_all

private theorem eta_xC_one (c : K) (a : Fin 4) (r : Bool) :
    ((eta K (xC .D4 K (1 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K a r) =
      plusVec 4 K a r +
        (if a = 3 ∧ r = false then c else 0) • plusVec 4 K (0 : Fin 4) false +
        (if a = 0 ∧ r = true then c else 0) • plusVec 4 K (3 : Fin 4) true := by
  rw [xC_eq_pinned]
  rw [eta_pinnedX_apply (β := Pi.single (1 : Fin 4) 1) (mem_rootFinset.mpr (isRoot_single _ _))
    (by decide) bLinv_single_one c (plusVec 4 K a r)]
  rw [polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 3) (s := r) (t := true),
    polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 0) (s := r) (t := false)]
  split_ifs <;> simp_all

private theorem eta_xC_two (c : K) (a : Fin 4) (r : Bool) :
    ((eta K (xC .D4 K (2 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K a r) =
      plusVec 4 K a r +
        (if a = 3 ∧ r = true then c else 0) • plusVec 4 K (2 : Fin 4) true +
        (if a = 2 ∧ r = false then c else 0) • plusVec 4 K (3 : Fin 4) false := by
  rw [xC_eq_pinned]
  rw [eta_pinnedX_apply (β := Pi.single (2 : Fin 4) 1) (mem_rootFinset.mpr (isRoot_single _ _))
    (by decide) bLinv_single_two c (plusVec 4 K a r)]
  rw [polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 3) (s := r) (t := false),
    polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 2) (s := r) (t := true)]
  split_ifs <;> simp_all

private theorem eta_xC_three (c : K) (a : Fin 4) (r : Bool) :
    ((eta K (xC .D4 K (3 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K a r) =
      plusVec 4 K a r +
        (if a = 3 ∧ r = false then c else 0) • plusVec 4 K (0 : Fin 4) true +
        (if a = 0 ∧ r = false then c else 0) • plusVec 4 K (3 : Fin 4) true := by
  rw [xC_eq_pinned]
  rw [eta_pinnedX_apply (β := Pi.single (3 : Fin 4) 1) (mem_rootFinset.mpr (isRoot_single _ _))
    (by decide) bLinv_single_three c (plusVec 4 K a r)]
  rw [polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 3) (s := r) (t := true),
    polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 0) (s := r) (t := true)]
  split_ifs <;> simp_all

private theorem eta_yC_zero (c : K) (a : Fin 4) (r : Bool) :
    ((eta K (yC .D4 K (0 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K a r) =
      plusVec 4 K a r +
        (if a = 1 ∧ r = true then c else 0) • plusVec 4 K (2 : Fin 4) true +
        (if a = 2 ∧ r = false then c else 0) • plusVec 4 K (1 : Fin 4) false := by
  rw [yC_eq_pinned]
  have h := eta_pinnedX_apply (β := -Pi.single (0 : Fin 4) 1)
    (mem_rootFinset.mpr (isRoot_neg_single _ _)) (by decide) bLinv_neg_single_zero c
    (plusVec 4 K a r)
  refine h.trans ?_
  rw [polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 1) (s := r) (t := false),
    polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 2) (s := r) (t := true)]
  split_ifs <;> simp_all

private theorem eta_yC_one (c : K) (a : Fin 4) (r : Bool) :
    ((eta K (yC .D4 K (1 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K a r) =
      plusVec 4 K a r +
        (if a = 3 ∧ r = true then c else 0) • plusVec 4 K (0 : Fin 4) true +
        (if a = 0 ∧ r = false then c else 0) • plusVec 4 K (3 : Fin 4) false := by
  rw [yC_eq_pinned]
  have h := eta_pinnedX_apply (β := -Pi.single (1 : Fin 4) 1)
    (mem_rootFinset.mpr (isRoot_neg_single _ _)) (by decide) bLinv_neg_single_one c
    (plusVec 4 K a r)
  refine h.trans ?_
  rw [polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 3) (s := r) (t := false),
    polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 0) (s := r) (t := true)]
  split_ifs <;> simp_all

private theorem eta_yC_two (c : K) (a : Fin 4) (r : Bool) :
    ((eta K (yC .D4 K (2 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K a r) =
      plusVec 4 K a r +
        (if a = 2 ∧ r = true then c else 0) • plusVec 4 K (3 : Fin 4) true +
        (if a = 3 ∧ r = false then c else 0) • plusVec 4 K (2 : Fin 4) false := by
  rw [yC_eq_pinned]
  have h := eta_pinnedX_apply (β := -Pi.single (2 : Fin 4) 1)
    (mem_rootFinset.mpr (isRoot_neg_single _ _)) (by decide) bLinv_neg_single_two c
    (plusVec 4 K a r)
  refine h.trans ?_
  rw [polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 2) (s := r) (t := false),
    polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 3) (s := r) (t := true)]
  split_ifs <;> simp_all

private theorem eta_yC_three (c : K) (a : Fin 4) (r : Bool) :
    ((eta K (yC .D4 K (3 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K a r) =
      plusVec 4 K a r +
        (if a = 3 ∧ r = true then c else 0) • plusVec 4 K (0 : Fin 4) false +
        (if a = 0 ∧ r = true then c else 0) • plusVec 4 K (3 : Fin 4) false := by
  rw [yC_eq_pinned]
  have h := eta_pinnedX_apply (β := -Pi.single (3 : Fin 4) 1)
    (mem_rootFinset.mpr (isRoot_neg_single _ _)) (by decide) bLinv_neg_single_three c
    (plusVec 4 K a r)
  refine h.trans ?_
  rw [polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 3) (s := r) (t := false),
    polar_quadPlus_plusVec (n := 4) (K := K) (i := a) (j := 0) (s := r) (t := false)]
  split_ifs <;> simp_all


private def frameElt (x x' : Fin 4 ⊕ Fin 4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  fun a b => if b = x then (if a = x' then 1 else 0) else 0

private def E0 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  frameElt (eI 2) (eI 1) + frameElt (fI 1) (fI 2)

private def E1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  frameElt (fI 3) (fI 0) + frameElt (eI 0) (eI 3)

private def E2 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  frameElt (eI 3) (eI 2) + frameElt (fI 2) (fI 3)

private def E3 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  frameElt (fI 3) (eI 0) + frameElt (fI 0) (eI 3)

private def F0 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  frameElt (eI 1) (eI 2) + frameElt (fI 2) (fI 1)

private def F1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  frameElt (eI 3) (eI 0) + frameElt (fI 0) (fI 3)

private def F2 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  frameElt (fI 3) (fI 2) + frameElt (eI 2) (eI 3)

private def F3 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  frameElt (eI 3) (fI 0) + frameElt (eI 0) (fI 3)

private theorem natMat_xC_zero (c : K) : natMat K (xC .D4 K (0 : Fin 4) c) = 1 + c • E0 := by
  ext a b
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  change (((eta K (xC .D4 K (0 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single b 1)) a = _
  rcases a with l | l <;> rcases b with k | k
  all_goals
    first
      | rw [show (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k true from rfl]
      | rw [show (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k false from rfl]
    rw [eta_xC_zero]
    simp only [frameElt, E0, Matrix.add_apply, Pi.add_apply, Pi.smul_apply, plusVec_true,
      Pi.single_apply, eI, fI, Sum.inl.injEq, Sum.inr.injEq]
    split_ifs <;> simp_all

private theorem natMat_xC_one (c : K) : natMat K (xC .D4 K (1 : Fin 4) c) = 1 + c • E1 := by
  ext a b
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  change (((eta K (xC .D4 K (1 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single b 1)) a = _
  rcases a with l | l <;> rcases b with k | k
  all_goals
    first
      | rw [show (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k true from rfl]
      | rw [show (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k false from rfl]
    rw [eta_xC_one]
    simp only [frameElt, E1, Matrix.add_apply, Pi.add_apply, Pi.smul_apply, plusVec_true,
      Pi.single_apply, eI, fI, Sum.inl.injEq, Sum.inr.injEq]
    split_ifs <;> simp_all

private theorem natMat_xC_two (c : K) : natMat K (xC .D4 K (2 : Fin 4) c) = 1 + c • E2 := by
  ext a b
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  change (((eta K (xC .D4 K (2 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single b 1)) a = _
  rcases a with l | l <;> rcases b with k | k
  all_goals
    first
      | rw [show (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k true from rfl]
      | rw [show (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k false from rfl]
    rw [eta_xC_two]
    simp only [frameElt, E2, Matrix.add_apply, Pi.add_apply, Pi.smul_apply, plusVec_true,
      Pi.single_apply, eI, fI, Sum.inl.injEq, Sum.inr.injEq]
    split_ifs <;> simp_all

private theorem natMat_xC_three (c : K) : natMat K (xC .D4 K (3 : Fin 4) c) = 1 + c • E3 := by
  ext a b
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  change (((eta K (xC .D4 K (3 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single b 1)) a = _
  rcases a with l | l <;> rcases b with k | k
  all_goals
    first
      | rw [show (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k true from rfl]
      | rw [show (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k false from rfl]
    rw [eta_xC_three]
    simp only [frameElt, E3, Matrix.add_apply, Pi.add_apply, Pi.smul_apply, plusVec_true,
      Pi.single_apply, eI, fI, Sum.inl.injEq, Sum.inr.injEq]
    split_ifs <;> simp_all

private theorem natMat_yC_zero (c : K) : natMat K (yC .D4 K (0 : Fin 4) c) = 1 + c • F0 := by
  ext a b
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  change (((eta K (yC .D4 K (0 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single b 1)) a = _
  rcases a with l | l <;> rcases b with k | k
  all_goals
    first
      | rw [show (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k true from rfl]
      | rw [show (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k false from rfl]
    rw [eta_yC_zero]
    simp only [frameElt, F0, Matrix.add_apply, Pi.add_apply, Pi.smul_apply, plusVec_true,
      Pi.single_apply, eI, fI, Sum.inl.injEq, Sum.inr.injEq]
    split_ifs <;> simp_all

private theorem natMat_yC_one (c : K) : natMat K (yC .D4 K (1 : Fin 4) c) = 1 + c • F1 := by
  ext a b
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  change (((eta K (yC .D4 K (1 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single b 1)) a = _
  rcases a with l | l <;> rcases b with k | k
  all_goals
    first
      | rw [show (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k true from rfl]
      | rw [show (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k false from rfl]
    rw [eta_yC_one]
    simp only [frameElt, F1, Matrix.add_apply, Pi.add_apply, Pi.smul_apply, plusVec_true,
      Pi.single_apply, eI, fI, Sum.inl.injEq, Sum.inr.injEq]
    split_ifs <;> simp_all

private theorem natMat_yC_two (c : K) : natMat K (yC .D4 K (2 : Fin 4) c) = 1 + c • F2 := by
  ext a b
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  change (((eta K (yC .D4 K (2 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single b 1)) a = _
  rcases a with l | l <;> rcases b with k | k
  all_goals
    first
      | rw [show (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k true from rfl]
      | rw [show (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k false from rfl]
    rw [eta_yC_two]
    simp only [frameElt, F2, Matrix.add_apply, Pi.add_apply, Pi.smul_apply, plusVec_true,
      Pi.single_apply, eI, fI, Sum.inl.injEq, Sum.inr.injEq]
    split_ifs <;> simp_all

private theorem natMat_yC_three (c : K) : natMat K (yC .D4 K (3 : Fin 4) c) = 1 + c • F3 := by
  ext a b
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  change (((eta K (yC .D4 K (3 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single b 1)) a = _
  rcases a with l | l <;> rcases b with k | k
  all_goals
    first
      | rw [show (Pi.single (Sum.inl k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k true from rfl]
      | rw [show (Pi.single (Sum.inr k) 1 : Fin 4 ⊕ Fin 4 → K) = plusVec 4 K k false from rfl]
    rw [eta_yC_three]
    simp only [frameElt, F3, Matrix.add_apply, Pi.add_apply, Pi.smul_apply, plusVec_true,
      Pi.single_apply, eI, fI, Sum.inl.injEq, Sum.inr.injEq]
    split_ifs <;> simp_all


private lemma frameElt_mulVec_apply (x x' : Fin 4 ⊕ Fin 4) (w : Fin 4 ⊕ Fin 4 → k)
    (a : Fin 4 ⊕ Fin 4) :
    ((frameElt x x').map (algebraMap K k) *ᵥ w) a =
      if a = x' then w x else 0 := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single x]
  · simp [frameElt, Matrix.map_apply]
  · intro b _ hb
    simp [frameElt, Matrix.map_apply, hb]
  · intro hx; simp at hx

private lemma frameElt_mulVec_single (x x' : Fin 4 ⊕ Fin 4) :
    (frameElt x x').map (algebraMap K k) *ᵥ (Pi.single x 1) =
      Pi.single x' 1 := by
  funext a
  rw [frameElt_mulVec_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : a = x'
  · subst h; simp
  · rw [if_neg h, if_neg h]

private lemma frameElt_add_mulVec_single (x1 x2 x1' x2' : Fin 4 ⊕ Fin 4) (h : x1 ≠ x2) :
    (((frameElt (K := K) x1 x1' + frameElt (K := K) x2 x2') :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).map (algebraMap K k)) *ᵥ (Pi.single x1 1) =
      Pi.single x1' 1 := by
  rw [Matrix.map_add (algebraMap K k) (map_add _), Matrix.add_mulVec, frameElt_mulVec_single]
  have h0 : ((frameElt (K := K) x2 x2').map (algebraMap K k)) *ᵥ (Pi.single x1 1) = 0 := by
    funext a
    rw [frameElt_mulVec_apply, Pi.single_eq_of_ne h.symm]
    simp
  rw [h0, add_zero]

private lemma frameElt_add_mulVec_apply (x1 x2 x1' x2' : Fin 4 ⊕ Fin 4)
    (w : Fin 4 ⊕ Fin 4 → k) (a : Fin 4 ⊕ Fin 4) :
    ((((frameElt (K := K) x1 x1' + frameElt (K := K) x2 x2') :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).map (algebraMap K k)) *ᵥ w) a =
      (if a = x1' then w x1 else 0) +
        (if a = x2' then w x2 else 0) := by
  rw [Matrix.map_add (algebraMap K k) (map_add _), Matrix.add_mulVec, Pi.add_apply,
    frameElt_mulVec_apply, frameElt_mulVec_apply]


private def Es : Fin 4 → Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K := ![E0, E1, E2, E3]

private def Fs : Fin 4 → Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K := ![F0, F1, F2, F3]

private theorem ker_two (Emat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)
    (x1 x2 x1' x2' : Fin 4 ⊕ Fin 4)
    (hE : Emat = frameElt x1 x1' + frameElt x2 x2') (hx' : x1' ≠ x2')
    (w : Fin 4 ⊕ Fin 4 → k) (h : Emat.map (algebraMap K k) *ᵥ w = 0) :
    w x1 = 0 ∧ w x2 = 0 := by
  constructor
  · have h1 := congrFun h x1'
    rw [hE, frameElt_add_mulVec_apply] at h1
    have hne : x1' ≠ x2' := hx'
    simp [hne] at h1
    exact h1
  · have h1 := congrFun h x2'
    rw [hE, frameElt_add_mulVec_apply] at h1
    have hne : x2' ≠ x1' := hx'.symm
    simp [hne] at h1
    exact h1

private theorem ker_Es (w : Fin 4 ⊕ Fin 4 → k)
    (h : ∀ i, (Es i).map (algebraMap K k) *ᵥ w = 0) : ∀ j, j ≠ eI 1 → w j = 0 := by
  have h0 := ker_two k E0 (eI 2) (fI 1) (eI 1) (fI 2) rfl (by decide) w (by simpa [Es] using h 0)
  have h1 := ker_two k E1 (fI 3) (eI 0) (fI 0) (eI 3) rfl (by decide) w (by simpa [Es] using h 1)
  have h2 := ker_two k E2 (eI 3) (fI 2) (eI 2) (fI 3) rfl (by decide) w (by simpa [Es] using h 2)
  have h3 := ker_two k E3 (fI 3) (fI 0) (eI 0) (eI 3) rfl (by decide) w (by simpa [Es] using h 3)
  rintro j hj
  rcases j with a | a <;> fin_cases a <;> simp_all [eI, fI]

private lemma frameElt_add_mulVec_single_right (x1 x2 x1' x2' : Fin 4 ⊕ Fin 4) (h : x1 ≠ x2) :
    (((frameElt (K := K) x1 x1' + frameElt (K := K) x2 x2') :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).map (algebraMap K k)) *ᵥ (Pi.single x2 1) =
      Pi.single x2' 1 := by
  rw [Matrix.map_add (algebraMap K k) (map_add _), Matrix.add_mulVec]
  have h0 : ((frameElt (K := K) x1 x1').map (algebraMap K k)) *ᵥ (Pi.single x2 1) = 0 := by
    funext a
    rw [frameElt_mulVec_apply, Pi.single_eq_of_ne h]
    simp
  rw [h0, zero_add, frameElt_mulVec_single]

private theorem F_step' (Emat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)
    (x1 x2 x1' x2' : Fin 4 ⊕ Fin 4)
    (hE : Emat = frameElt x1 x1' + frameElt x2 x2') (hx : x1 ≠ x2)
    (W : Submodule k (Fin 4 ⊕ Fin 4 → k)) (hW : Emat.map (algebraMap K k) *ᵥ (Pi.single x2 1) ∈ W) :
    Pi.single x2' 1 ∈ W := by
  rwa [hE, frameElt_add_mulVec_single_right k x1 x2 x1' x2' hx] at hW

private theorem F_step (Emat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)
    (x1 x2 x1' x2' : Fin 4 ⊕ Fin 4)
    (hE : Emat = frameElt x1 x1' + frameElt x2 x2') (hx : x1 ≠ x2)
    (W : Submodule k (Fin 4 ⊕ Fin 4 → k)) (hW : Emat.map (algebraMap K k) *ᵥ (Pi.single x1 1) ∈ W) :
    Pi.single x1' 1 ∈ W := by
  rwa [hE, frameElt_add_mulVec_single k x1 x2 x1' x2' hx] at hW

private theorem gen_Fs (W : Submodule k (Fin 4 ⊕ Fin 4 → k))
    (h0 : Pi.single (eI 1) 1 ∈ W)
    (hW : ∀ i, ∀ w ∈ W, (Fs i).map (algebraMap K k) *ᵥ w ∈ W) : W = ⊤ := by
  have he2 : Pi.single (eI 2) 1 ∈ W :=
    F_step k F0 (eI 1) (fI 2) (eI 2) (fI 1) rfl (by decide) W (by simpa [Fs] using hW 0 _ h0)
  have he3 : Pi.single (eI 3) 1 ∈ W :=
    F_step' k F2 (fI 3) (eI 2) (fI 2) (eI 3) rfl (by decide) W (by simpa [Fs] using hW 2 _ he2)
  have he0 : Pi.single (eI 0) 1 ∈ W :=
    F_step k F1 (eI 3) (fI 0) (eI 0) (fI 3) rfl (by decide) W (by simpa [Fs] using hW 1 _ he3)
  have hf3 : Pi.single (fI 3) 1 ∈ W :=
    F_step' k F3 (eI 3) (eI 0) (fI 0) (fI 3) rfl (by decide) W (by simpa [Fs] using hW 3 _ he0)
  have hf2 : Pi.single (fI 2) 1 ∈ W :=
    F_step k F2 (fI 3) (eI 2) (fI 2) (eI 3) rfl (by decide) W (by simpa [Fs] using hW 2 _ hf3)
  have hf1 : Pi.single (fI 1) 1 ∈ W :=
    F_step' k F0 (eI 1) (fI 2) (eI 2) (fI 1) rfl (by decide) W (by simpa [Fs] using hW 0 _ hf2)
  have hf0 : Pi.single (fI 0) 1 ∈ W :=
    F_step k F3 (eI 3) (eI 0) (fI 0) (fI 3) rfl (by decide) W (by simpa [Fs] using hW 3 _ he3)
  have hmem : ∀ a : Fin 4 ⊕ Fin 4, Pi.single a 1 ∈ W := by
    intro a
    rcases a with i | i <;> fin_cases i
    · simpa [eI] using he0
    · simpa [eI] using h0
    · simpa [eI] using he2
    · simpa [eI] using he3
    · simpa [fI] using hf0
    · simpa [fI] using hf1
    · simpa [fI] using hf2
    · simpa [fI] using hf3
  refine eq_top_iff.mpr fun w _ => ?_
  rw [← Finset.univ_sum_single w]
  refine W.sum_mem fun a _ => ?_
  have hsm : (w a • Pi.single a 1 : Fin 4 ⊕ Fin 4 → k) = Pi.single a (w a) := by
    funext b
    by_cases h : b = a
    · subst h; simp
    · simp [h]
  rw [← hsm]
  exact W.smul_mem (w a) (hmem a)


private theorem pos_root_bLinv_coord :
    ∀ α ∈ rootFinset .D4, 0 < height α → toStdD 4 (bLinv α) 1 ≠ -1 := by
  decide +kernel

private theorem eta_pinnedX_fix {α : Fin Tag.D4.rank → ℤ} (hα : α ∈ rootFinset .D4)
    (hpos : 0 < height α) (c : K) :
    ((eta K ⟨pinnedX .D4 K α c, pinnedX_mem_adjointGroup α c⟩ :
        orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  have hroot : IsRoot TwistTag.D4.tag α := mem_rootFinset.mp hα
  obtain ⟨i, j, s, t, hij, hstd, -⟩ := exists_eq_fromStd (bLinv_mem hroot)
  have hne : toStdD 4 (bLinv α) 1 ≠ -1 := pos_root_bLinv_coord α hα hpos
  have hval : (lv i j s t) 1 ≠ -1 := by rwa [hstd] at hne
  have h1 : polar (quadPlus 4 K) (plusVec 4 K (1 : Fin 4) true) (plusVec 4 K j t) = 0 := by
    rw [polar_quadPlus_plusVec]
    by_cases hc : (1 : Fin 4) = j ∧ true = !t
    · exfalso
      have hj : j = 1 := hc.1.symm
      have ht : t = false := by simpa using hc.2
      apply hval
      subst hj
      simp [lv, ht, hij]
    · rw [if_neg hc]
  have h2 : polar (quadPlus 4 K) (plusVec 4 K (1 : Fin 4) true) (plusVec 4 K i s) = 0 := by
    rw [polar_quadPlus_plusVec]
    by_cases hc : (1 : Fin 4) = i ∧ true = !s
    · exfalso
      have hi : i = 1 := hc.1.symm
      have hs : s = false := by simpa using hc.2
      apply hval
      subst hi
      have hj : j ≠ 1 := fun h => hij (by rw [h])
      simp [lv, hs, hj]
    · rw [if_neg hc]
  have h := eta_pinnedX_apply (β := α) hα hij hstd c (plusVec 4 K (1 : Fin 4) true)
  refine h.trans ?_
  rw [h1, h2]
  simp

private theorem natMat_mulVec (g : adjointGroup .D4 K) (v : Fin 4 ⊕ Fin 4 → K) :
    natMat K g *ᵥ v = ((eta K g : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v := by
  change LinearMap.toMatrix' ((eta K g : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)).toLinearMap *ᵥ v = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

private def fixer : Subgroup (ModGL .D4 K) where
  carrier := {g | ∃ hg : g ∈ adjointGroup .D4 K,
    natMat K ⟨g, hg⟩ *ᵥ (Pi.single (Sum.inl (1 : Fin 4)) 1 : Fin 4 ⊕ Fin 4 → K) =
      Pi.single (Sum.inl (1 : Fin 4)) 1}
  one_mem' := ⟨Subgroup.one_mem _, by
    rw [show (⟨1, Subgroup.one_mem _⟩ : adjointGroup .D4 K) = 1 from Subtype.ext rfl, map_one,
      Matrix.one_mulVec]⟩
  mul_mem' := by
    rintro g h ⟨hg, hgfix⟩ ⟨hh, hhfix⟩
    refine ⟨mul_mem hg hh, ?_⟩
    rw [show (⟨g * h, mul_mem hg hh⟩ : adjointGroup .D4 K) = ⟨g, hg⟩ * ⟨h, hh⟩ from
        Subtype.ext rfl, map_mul, ← Matrix.mulVec_mulVec, hhfix, hgfix]
  inv_mem' := by
    rintro g ⟨hg, hgfix⟩
    refine ⟨inv_mem hg, ?_⟩
    have hmul : (⟨g⁻¹, inv_mem hg⟩ : adjointGroup .D4 K) * ⟨g, hg⟩ = 1 :=
      Subtype.ext (inv_mul_cancel g)
    have hmap : natMat K ⟨g⁻¹, inv_mem hg⟩ * natMat K ⟨g, hg⟩ = 1 := by
      rw [← map_mul, hmul, map_one]
    calc natMat K ⟨g⁻¹, inv_mem hg⟩ *ᵥ Pi.single (Sum.inl (1 : Fin 4)) 1
        = natMat K ⟨g⁻¹, inv_mem hg⟩ *ᵥ
            (natMat K ⟨g, hg⟩ *ᵥ Pi.single (Sum.inl (1 : Fin 4)) 1) := by rw [hgfix]
      _ = (natMat K ⟨g⁻¹, inv_mem hg⟩ * natMat K ⟨g, hg⟩) *ᵥ
            Pi.single (Sum.inl (1 : Fin 4)) 1 := by rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ Pi.single (Sum.inl (1 : Fin 4)) 1 := by rw [hmap]
      _ = Pi.single (Sum.inl (1 : Fin 4)) 1 := Matrix.one_mulVec _

private theorem rootSubgroup_le_fixer (α : Fin Tag.D4.rank → ℤ) (hα : IsRoot .D4 α)
    (hpos : 0 < height α) : rootSubgroup .D4 K α ≤ fixer := by
  rw [rootSubgroup, Subgroup.closure_le]
  rintro g ⟨c, rfl⟩
  refine ⟨pinnedX_mem_adjointGroup α c, ?_⟩
  rw [natMat_mulVec]
  exact eta_pinnedX_fix (mem_rootFinset.mpr hα) hpos c

private theorem posUnipotent_le_fixer : posUnipotent .D4 K ≤ fixer := by
  rw [posUnipotent, rootSpan]
  refine iSup_le fun α => iSup_le fun hα => ?_
  exact rootSubgroup_le_fixer α hα.1 hα.2

private theorem mem_fixer {u : adjointGroup .D4 K} (hu : (u : ModGL .D4 K) ∈ posUnipotent .D4 K) :
    natMat K u *ᵥ (Pi.single (Sum.inl (1 : Fin 4)) 1 : Fin 4 ⊕ Fin 4 → K) =
      Pi.single (Sum.inl (1 : Fin 4)) 1 := by
  have h := posUnipotent_le_fixer hu
  obtain ⟨hg, hgfix⟩ := h
  rwa [show (⟨(u : ModGL .D4 K), hg⟩ : adjointGroup .D4 K) = u from Subtype.ext rfl] at hgfix



private theorem natMat_posUnipotent_col {u : adjointGroup .D4 K}
    (hu : (u : ModGL .D4 K) ∈ posUnipotent .D4 K) (j : Fin 4 ⊕ Fin 4) :
    natMat K u j (Sum.inl 1) = if j = Sum.inl 1 then (1 : K) else 0 := by
  by_cases hj : j = Sum.inl 1
  · subst hj
    have h := congrFun (mem_fixer hu) (Sum.inl 1)
    rw [Matrix.mulVec, dotProduct] at h
    rw [Finset.sum_eq_single (Sum.inl (1 : Fin 4))] at h
    · simpa [Pi.single_eq_same] using h
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · rw [if_neg hj]
    have h := congrFun (mem_fixer hu) j
    rw [Matrix.mulVec, dotProduct] at h
    rw [Finset.sum_eq_single (Sum.inl (1 : Fin 4))] at h
    · simpa [Pi.single_eq_same, Pi.single_eq_of_ne hj] using h
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot

private theorem tensorD4_hwVec_fix {S : Finset ℕ} {u : adjointGroup .D4 K}
    (hu : (u : ModGL .D4 K) ∈ posUnipotent .D4 K) :
    tensorD4 (K := K) k S u (hwVec k S) = hwVec k S := by
  classical
  rw [tensorD4, hwVec]
  exact frobTensorRep_single_of_col_single (k := k) (M := natMat K) (S := S) (g := u)
    (v := Sum.inl 1) (v' := Sum.inl 1) (fun j => natMat_posUnipotent_col hu j)

private theorem hwVec_coord (S : Finset ℕ) :
    hwVec k S (fun _ => Sum.inl (1 : Fin 4)) = (1 : k) := by simp [hwVec]

private theorem chiT_one (S : Finset ℕ) :
    chiT (K := K) k S (1 : adjointGroup .D4 K) = (1 : k) := by
  change ((tensorD4 k S 1 (hwVec k S)) (fun _ => Sum.inl (1 : Fin 4))) = 1
  rw [map_one, Module.End.one_apply, hwVec_coord]

private theorem chiT_mul_of_eigen {S : Finset ℕ} {g h : adjointGroup .D4 K}
    (hh : tensorD4 (K := K) k S h (hwVec k S) = chiT (K := K) k S h • hwVec k S) :
    chiT (K := K) k S (g * h) = chiT (K := K) k S h * chiT (K := K) k S g := by
  change ((tensorD4 k S (g * h) (hwVec k S)) (fun _ => Sum.inl (1 : Fin 4))) =
    ((tensorD4 k S h (hwVec k S)) (fun _ => Sum.inl (1 : Fin 4))) *
      ((tensorD4 k S g (hwVec k S)) (fun _ => Sum.inl (1 : Fin 4)))
  rw [map_mul, Module.End.mul_apply, hh, map_smul, Pi.smul_apply, smul_eq_mul,
    Pi.smul_apply, smul_eq_mul, hwVec_coord, mul_one]

private theorem hwVec_ne_zero (S : Finset ℕ) : hwVec k S ≠ 0 := by
  intro h
  have hc := congrFun h (fun _ => Sum.inl (1 : Fin 4))
  simp [hwVec] at hc

private def eigenProp (S : Finset ℕ) (g : adjointGroup .D4 K) : Prop :=
  tensorD4 (K := K) k S g (hwVec k S) = chiT (K := K) k S g • hwVec k S

private def eigenSubgroupMod (S : Finset ℕ) : Subgroup (ModGL .D4 K) where
  carrier := {g | ∃ hg : g ∈ adjointGroup .D4 K, eigenProp k S ⟨g, hg⟩}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    change tensorD4 (K := K) k S (⟨1, Subgroup.one_mem _⟩ : adjointGroup .D4 K) (hwVec k S) =
      chiT (K := K) k S (⟨1, Subgroup.one_mem _⟩ : adjointGroup .D4 K) • hwVec k S
    rw [show (⟨1, Subgroup.one_mem _⟩ : adjointGroup .D4 K) = 1 from Subtype.ext rfl,
      chiT_one, one_smul, map_one, Module.End.one_apply]
  mul_mem' := by
    rintro g h ⟨hg, hgP⟩ ⟨hh, hhP⟩
    refine ⟨mul_mem hg hh, ?_⟩
    change tensorD4 (K := K) k S (⟨g * h, mul_mem hg hh⟩ : adjointGroup .D4 K) (hwVec k S) =
      chiT (K := K) k S (⟨g * h, mul_mem hg hh⟩ : adjointGroup .D4 K) • hwVec k S
    rw [show (⟨g * h, mul_mem hg hh⟩ : adjointGroup .D4 K) =
      (⟨g, hg⟩ : adjointGroup .D4 K) * ⟨h, hh⟩ from Subtype.ext rfl]
    rw [map_mul, Module.End.mul_apply, hhP, map_smul, hgP,
      chiT_mul_of_eigen (k := k) hhP, smul_smul]
  inv_mem' := by
    rintro g ⟨hg, hgP⟩
    set χ : k := chiT (K := K) k S ⟨g, hg⟩ with hχ
    have hgP' : tensorD4 (K := K) k S ⟨g, hg⟩ (hwVec k S) = χ • hwVec k S := hgP
    have hχne : χ ≠ 0 := by
      intro h0
      have hzero : tensorD4 (K := K) k S ⟨g, hg⟩ (hwVec k S) = 0 := by
        rw [hgP', h0, zero_smul]
      have hy0 : hwVec k S = 0 := by
        have h := congrArg (tensorD4 (K := K) k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹) hzero
        change ((tensorD4 k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹ *
          tensorD4 k S (⟨g, hg⟩ : adjointGroup .D4 K)) (hwVec k S)) =
            tensorD4 k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹ 0 at h
        rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at h
        exact h
      exact hwVec_ne_zero k S hy0
    have h := congrArg (tensorD4 (K := K) k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹) hgP'
    change ((tensorD4 k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹ *
      tensorD4 k S (⟨g, hg⟩ : adjointGroup .D4 K)) (hwVec k S)) =
        tensorD4 k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹ (χ • hwVec k S) at h
    rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_smul] at h
    have hinv : tensorD4 (K := K) k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹ (hwVec k S) =
        χ⁻¹ • hwVec k S := by
      have h' : χ⁻¹ • hwVec k S =
          tensorD4 (K := K) k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹ (hwVec k S) := by
        have := congrArg (fun w => χ⁻¹ • w) h
        simpa [smul_smul, hχne] using this
      exact h'.symm
    refine ⟨inv_mem hg, ?_⟩
    change tensorD4 (K := K) k S (⟨g⁻¹, inv_mem hg⟩ : adjointGroup .D4 K) (hwVec k S) =
      chiT (K := K) k S (⟨g⁻¹, inv_mem hg⟩ : adjointGroup .D4 K) • hwVec k S
    rw [show (⟨g⁻¹, inv_mem hg⟩ : adjointGroup .D4 K) = (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹
      from Subtype.ext rfl, hinv]
    have hchi_inv : chiT (K := K) k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹ = χ⁻¹ := by
      change ((tensorD4 k S (⟨g, hg⟩ : adjointGroup .D4 K)⁻¹ (hwVec k S))
        (fun _ => Sum.inl (1 : Fin 4))) = χ⁻¹
      rw [hinv, Pi.smul_apply, smul_eq_mul, hwVec_coord, mul_one]
    rw [hchi_inv]

private theorem frameElt_add_apply_01 (x1 x2 x1' x2' : Fin 4 ⊕ Fin 4) (h : x1 ≠ x2)
    (a b : Fin 4 ⊕ Fin 4) :
    ((frameElt (K := K) x1 x1' + frameElt (K := K) x2 x2' :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)) a b = (0 : K) ∨
      ((frameElt (K := K) x1 x1' + frameElt (K := K) x2 x2' :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)) a b = (1 : K) := by
  rw [Matrix.add_apply]
  by_cases hb1 : b = x1
  · have hb2 : b ≠ x2 := fun h2 => h (hb1.symm.trans h2)
    have h1 : (frameElt (K := K) x1 x1') a b = (if a = x1' then (1 : K) else 0) := by
      simp [frameElt, hb1]
    have h2 : (frameElt (K := K) x2 x2') a b = 0 := by simp [frameElt, hb2]
    rw [h1, h2, add_zero]
    split_ifs <;> simp
  · by_cases hb2 : b = x2
    · have h1 : (frameElt (K := K) x1 x1') a b = 0 := by simp [frameElt, hb1]
      have h2 : (frameElt (K := K) x2 x2') a b = (if a = x2' then (1 : K) else 0) := by
        simp [frameElt, hb2]
      rw [h1, h2, zero_add]
      split_ifs <;> simp
    · have h1 : (frameElt (K := K) x1 x1') a b = 0 := by simp [frameElt, hb1]
      have h2 : (frameElt (K := K) x2 x2') a b = 0 := by simp [frameElt, hb2]
      rw [h1, h2]
      simp

theorem isSimpleRep_tensorD4 {n : ℕ} (hK : Nat.card K = 2 ^ n) (S : Finset ℕ)
    (hS : ∀ b ∈ S, b < n) : IsSimpleRep (tensorD4 (K := K) k S) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α :=
    ⟨_, invWord_four_smul⟩
  have hE01 : ∀ i (a b : Fin 4 ⊕ Fin 4), Es i a b = (0 : K) ∨ Es i a b = (1 : K) := by
    intro i a b
    fin_cases i
    · simpa [Es, E0] using
        frameElt_add_apply_01 (K := K) (eI 2) (fI 1) (eI 1) (fI 2) (by decide) a b
    · simpa [Es, E1] using
        frameElt_add_apply_01 (K := K) (fI 3) (eI 0) (fI 0) (eI 3) (by decide) a b
    · simpa [Es, E2] using
        frameElt_add_apply_01 (K := K) (eI 3) (fI 2) (eI 2) (fI 3) (by decide) a b
    · simpa [Es, E3] using
        frameElt_add_apply_01 (K := K) (fI 3) (fI 0) (eI 0) (eI 3) (by decide) a b
  have hF01 : ∀ i (a b : Fin 4 ⊕ Fin 4), Fs i a b = (0 : K) ∨ Fs i a b = (1 : K) := by
    intro i a b
    fin_cases i
    · simpa [Fs, F0] using
        frameElt_add_apply_01 (K := K) (eI 1) (fI 2) (eI 2) (fI 1) (by decide) a b
    · simpa [Fs, F1] using
        frameElt_add_apply_01 (K := K) (eI 3) (fI 0) (eI 0) (fI 3) (by decide) a b
    · simpa [Fs, F2] using
        frameElt_add_apply_01 (K := K) (fI 3) (eI 2) (fI 2) (eI 3) (by decide) a b
    · simpa [Fs, F3] using
        frameElt_add_apply_01 (K := K) (eI 3) (eI 0) (fI 0) (fI 3) (by decide) a b
  have hu : ∀ (i : Fin 4) (c : K), natMat K (xC .D4 K i c) = 1 + c • Es i := by
    intro i c
    fin_cases i
    · simpa [Es] using natMat_xC_zero (K := K) c
    · simpa [Es] using natMat_xC_one (K := K) c
    · simpa [Es] using natMat_xC_two (K := K) c
    · simpa [Es] using natMat_xC_three (K := K) c
  have hl : ∀ (i : Fin 4) (c : K), natMat K (yC .D4 K i c) = 1 + c • Fs i := by
    intro i c
    fin_cases i
    · simpa [Fs] using natMat_yC_zero (K := K) c
    · simpa [Fs] using natMat_yC_one (K := K) c
    · simpa [Fs] using natMat_yC_two (K := K) c
    · simpa [Fs] using natMat_yC_three (K := K) c
  refine isSimpleRep_frobTensorRep (k := k) (G := adjointGroup .D4 K) hK' (natMat K) S hS
    Es (fun i c => xC .D4 K i c) hu Fs (fun i c => yC .D4 K i c) hl hE01 hF01
    (Sum.inl 1) (ker_Es k) (gen_Fs k) (chevDatum .D4 K 2 hw).U
    (chevDatum .D4 K 2 hw).isPGroup_U (fun i c => xUnit_mem_posUnipotent (τ := Tag.D4) i c)


private theorem weylEltC_eq (i : Fin 4) (t : Kˣ) :
    (⟨weylElt .D4 K i t, weylElt_mem_adjointGroup (τ := Tag.D4) i t⟩ : adjointGroup .D4 K) =
      xC .D4 K i (t : K) * yC .D4 K i (-((t⁻¹ : Kˣ) : K)) * xC .D4 K i (t : K) :=
  Subtype.ext (CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul (τ := Tag.D4) i t)

private theorem dC_eq (i : Fin 4) (t : Kˣ) :
    dC .D4 K i t =
      (⟨weylElt .D4 K i t, weylElt_mem_adjointGroup (τ := Tag.D4) i t⟩ : adjointGroup .D4 K) *
      ⟨weylElt .D4 K i (-1), weylElt_mem_adjointGroup (τ := Tag.D4) i (-1)⟩ := rfl

private theorem eta_mul_apply (g h : adjointGroup .D4 K) (v : Fin 4 ⊕ Fin 4 → K) :
    ((eta K (g * h) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v =
      ((eta K g : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
        (((eta K h : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) v) := by
  rw [map_mul]
  rfl

private theorem eta_xC_zero_e1 (c : K) :
    ((eta K (xC .D4 K (0 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [eta_xC_zero]
  simp []

private theorem eta_xC_zero_e2 (c : K) :
    ((eta K (xC .D4 K (0 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (2 : Fin 4) true) =
      plusVec 4 K (2 : Fin 4) true + c • plusVec 4 K (1 : Fin 4) true := by
  rw [eta_xC_zero]
  simp []

private theorem eta_yC_zero_e1 (c : K) :
    ((eta K (yC .D4 K (0 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true + c • plusVec 4 K (2 : Fin 4) true := by
  rw [eta_yC_zero]
  simp []

private theorem eta_yC_zero_e2 (c : K) :
    ((eta K (yC .D4 K (0 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (2 : Fin 4) true) =
      plusVec 4 K (2 : Fin 4) true := by
  rw [eta_yC_zero]
  simp []

private theorem eta_xC_one_e1 (c : K) :
    ((eta K (xC .D4 K (1 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [eta_xC_one]
  simp []

private theorem eta_yC_one_e1 (c : K) :
    ((eta K (yC .D4 K (1 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [eta_yC_one]
  simp []

private theorem eta_xC_two_e1 (c : K) :
    ((eta K (xC .D4 K (2 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [eta_xC_two]
  simp []

private theorem eta_yC_two_e1 (c : K) :
    ((eta K (yC .D4 K (2 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [eta_yC_two]
  simp []

private theorem eta_xC_three_e1 (c : K) :
    ((eta K (xC .D4 K (3 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [eta_xC_three]
  simp []

private theorem eta_yC_three_e1 (c : K) :
    ((eta K (yC .D4 K (3 : Fin 4) c) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [eta_yC_three]
  simp []

private theorem eta_weyl_zero_e1 (z : Kˣ) :
    ((eta K (⟨weylElt .D4 K (0 : Fin 4) z, weylElt_mem_adjointGroup (τ := Tag.D4) (0 : Fin 4) z⟩ :
        adjointGroup .D4 K) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      ((z⁻¹ : Kˣ) : K) • plusVec 4 K (2 : Fin 4) true := by
  rw [weylEltC_eq, eta_mul_apply, eta_mul_apply]
  rw [eta_xC_zero_e1, eta_yC_zero_e1]
  rw [map_add, map_smul, eta_xC_zero_e1, eta_xC_zero_e2]
  simp [CharTwo.neg_eq, smul_add,
    add_comm]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem eta_weyl_zero_e2 (z : Kˣ) :
    ((eta K (⟨weylElt .D4 K (0 : Fin 4) z, weylElt_mem_adjointGroup (τ := Tag.D4) (0 : Fin 4) z⟩ :
        adjointGroup .D4 K) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (2 : Fin 4) true) =
      (z : K) • plusVec 4 K (1 : Fin 4) true := by
  rw [weylEltC_eq, eta_mul_apply, eta_mul_apply, eta_xC_zero_e2]
  simp only [map_add, map_smul, eta_yC_zero_e2, eta_yC_zero_e1, eta_xC_zero_e2,
    eta_xC_zero_e1]
  simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq, smul_add,
    add_zero, add_comm, add_left_comm]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem eta_weyl_one_e1 (z : Kˣ) :
    ((eta K (⟨weylElt .D4 K (1 : Fin 4) z, weylElt_mem_adjointGroup (τ := Tag.D4) (1 : Fin 4) z⟩ :
        adjointGroup .D4 K) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [weylEltC_eq, eta_mul_apply, eta_mul_apply, eta_xC_one_e1, eta_yC_one_e1, eta_xC_one_e1]

private theorem eta_weyl_two_e1 (z : Kˣ) :
    ((eta K (⟨weylElt .D4 K (2 : Fin 4) z, weylElt_mem_adjointGroup (τ := Tag.D4) (2 : Fin 4) z⟩ :
        adjointGroup .D4 K) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [weylEltC_eq, eta_mul_apply, eta_mul_apply, eta_xC_two_e1, eta_yC_two_e1, eta_xC_two_e1]

private theorem eta_weyl_three_e1 (z : Kˣ) :
    ((eta K (⟨weylElt .D4 K (3 : Fin 4) z, weylElt_mem_adjointGroup (τ := Tag.D4) (3 : Fin 4) z⟩ :
        adjointGroup .D4 K) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [weylEltC_eq, eta_mul_apply, eta_mul_apply, eta_xC_three_e1, eta_yC_three_e1, eta_xC_three_e1]

private theorem eta_weyl_ne_zero_e1 {i : Fin 4} (hi : i ≠ 0) (z : Kˣ) :
    ((eta K (⟨weylElt .D4 K i z, weylElt_mem_adjointGroup (τ := Tag.D4) i z⟩ :
        adjointGroup .D4 K) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  fin_cases i
  · exact absurd rfl hi
  · exact eta_weyl_one_e1 z
  · exact eta_weyl_two_e1 z
  · exact eta_weyl_three_e1 z

private theorem eta_dC_zero_e1 (z : Kˣ) :
    ((eta K (dC .D4 K (0 : Fin 4) z) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      (z : K) • plusVec 4 K (1 : Fin 4) true := by
  rw [dC_eq, eta_mul_apply, eta_weyl_zero_e1 (z := -1), map_smul, eta_weyl_zero_e2]
  have hneg : (((-1 : Kˣ)⁻¹ : Kˣ) : K) = 1 := by
    have h1 : ((-1 : Kˣ)) = 1 :=
      Units.ext (by rw [Units.val_neg, Units.val_one, CharTwo.neg_eq])
    rw [h1, inv_one, Units.val_one]
  rw [hneg, one_smul]

private theorem eta_dC_ne_zero_e1 {i : Fin 4} (hi : i ≠ 0) (z : Kˣ) :
    ((eta K (dC .D4 K i z) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K (1 : Fin 4) true) =
      plusVec 4 K (1 : Fin 4) true := by
  rw [dC_eq, eta_mul_apply, eta_weyl_ne_zero_e1 hi, eta_weyl_ne_zero_e1 hi]

private theorem natMat_dC_zero_e1 (z : Kˣ) :
    natMat K (dC .D4 K (0 : Fin 4) z) *ᵥ
        (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
      (z : K) • (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
  rw [natMat_mulVec]
  simpa [plusVec] using eta_dC_zero_e1 z

private theorem natMat_dC_zero_col (z : Kˣ) (j : Fin 4 ⊕ Fin 4) (hj : j ≠ Sum.inl 1) :
    natMat K (dC .D4 K (0 : Fin 4) z) j (Sum.inl 1) = 0 := by
  have h := congrFun (natMat_dC_zero_e1 z) j
  rw [Matrix.mulVec, dotProduct] at h
  rw [Finset.sum_eq_single (Sum.inl (1 : Fin 4))] at h
  · simpa [Pi.single_eq_same, Pi.single_eq_of_ne hj] using h
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

private theorem natMat_dC_zero_diag (z : Kˣ) :
    natMat K (dC .D4 K (0 : Fin 4) z) (Sum.inl 1) (Sum.inl 1) = (z : K) := by
  have h := congrFun (natMat_dC_zero_e1 z) (Sum.inl 1)
  rw [Matrix.mulVec, dotProduct] at h
  rw [Finset.sum_eq_single (Sum.inl (1 : Fin 4))] at h
  · simpa [Pi.single_eq_same] using h
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

theorem chiT_dC_zero (S : Finset ℕ) (z : Kˣ) :
    chiT (K := K) k S (dC .D4 K (0 : Fin 4) z) = (algebraMap K k (z : K)) ^ (∑ b ∈ S, 2 ^ b) := by
  classical
  have hsingle := frobTensorRep_single_of_col (k := k) (M := natMat K) (S := S)
    (g := dC .D4 K (0 : Fin 4) z) (v := Sum.inl 1)
    (fun j hj => natMat_dC_zero_col z j hj)
  simp only [chiT, tensorD4, hwVec]
  rw [hsingle]
  simp
  have hdiag : natMat K (dC .D4 K (0 : Fin 4) z) (Sum.inl 1) (Sum.inl 1) = (z : K) :=
    natMat_dC_zero_diag z
  simp only [hdiag]
  simp only [frobHom_apply]
  rw [Finset.prod_pow_eq_pow_sum]
  simp [Finset.sum_attach]

private theorem natMat_dC_ne_e1 {i : Fin 4} (hi : i ≠ 0) (z : Kˣ) :
    natMat K (dC .D4 K i z) *ᵥ
        (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
      (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
  rw [natMat_mulVec]
  simpa [plusVec] using eta_dC_ne_zero_e1 hi z

private theorem natMat_dC_ne_col {i : Fin 4} (hi : i ≠ 0) (z : Kˣ)
    (j : Fin 4 ⊕ Fin 4) (hj : j ≠ Sum.inl 1) :
    natMat K (dC .D4 K i z) j (Sum.inl 1) = 0 := by
  have h := congrFun (natMat_dC_ne_e1 hi z) j
  rw [Matrix.mulVec, dotProduct] at h
  rw [Finset.sum_eq_single (Sum.inl (1 : Fin 4))] at h
  · simpa [Pi.single_eq_same, Pi.single_eq_of_ne hj] using h
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

private theorem natMat_dC_ne_diag {i : Fin 4} (hi : i ≠ 0) (z : Kˣ) :
    natMat K (dC .D4 K i z) (Sum.inl 1) (Sum.inl 1) = (1 : K) := by
  have h := congrFun (natMat_dC_ne_e1 hi z) (Sum.inl 1)
  rw [Matrix.mulVec, dotProduct] at h
  rw [Finset.sum_eq_single (Sum.inl (1 : Fin 4))] at h
  · simpa [Pi.single_eq_same] using h
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

theorem chiT_dC_of_ne (S : Finset ℕ) {i : Fin 4} (hi : i ≠ 0) (z : Kˣ) :
    chiT (K := K) k S (dC .D4 K i z) = 1 := by
  classical
  have hsingle := frobTensorRep_single_of_col (k := k) (M := natMat K) (S := S)
    (g := dC .D4 K i z) (v := Sum.inl 1)
    (fun j hj => natMat_dC_ne_col hi z j hj)
  simp only [chiT, tensorD4, hwVec]
  rw [hsingle]
  simp
  have hdiag : natMat K (dC .D4 K i z) (Sum.inl 1) (Sum.inl 1) = (1 : K) :=
    natMat_dC_ne_diag hi z
  simp only [hdiag]
  simp

private theorem prod_frobHom_zero {S : Finset ℕ} (z : K) :
    (∏ b : S, frobHom k b z) = (algebraMap K k z) ^ (∑ b ∈ S, 2 ^ b) := by
  simp only [frobHom_apply]
  rw [Finset.prod_pow_eq_pow_sum]
  simp [Finset.sum_attach]

private theorem tensorD4_dC_zero {S : Finset ℕ} (z : Kˣ) :
    tensorD4 (K := K) k S (dC .D4 K (0 : Fin 4) z) (hwVec k S) =
      chiT (K := K) k S (dC .D4 K (0 : Fin 4) z) • hwVec k S := by
  classical
  have hsingle := frobTensorRep_single_of_col (k := k) (M := natMat K) (S := S)
    (g := dC .D4 K (0 : Fin 4) z) (v := Sum.inl 1)
    (fun j hj => natMat_dC_zero_col z j hj)
  rw [tensorD4, hwVec, hsingle]
  have hdiag : natMat K (dC .D4 K (0 : Fin 4) z) (Sum.inl 1) (Sum.inl 1) = (z : K) :=
    natMat_dC_zero_diag z
  rw [hdiag, prod_frobHom_zero, chiT_dC_zero (k := k)]

private theorem natMat_dC_ne_single {i : Fin 4} (hi : i ≠ 0) (z : Kˣ)
    (j : Fin 4 ⊕ Fin 4) :
    natMat K (dC .D4 K i z) j (Sum.inl 1) = if j = Sum.inl 1 then (1 : K) else 0 := by
  by_cases hj : j = Sum.inl 1
  · subst hj
    rw [if_pos rfl]
    exact natMat_dC_ne_diag hi z
  · rw [if_neg hj]
    exact natMat_dC_ne_col hi z j hj

private theorem tensorD4_dC_ne {S : Finset ℕ} {i : Fin 4} (hi : i ≠ 0) (z : Kˣ) :
    tensorD4 (K := K) k S (dC .D4 K i z) (hwVec k S) =
      chiT (K := K) k S (dC .D4 K i z) • hwVec k S := by
  classical
  have hsingle := frobTensorRep_single_of_col_single (k := k) (M := natMat K) (S := S)
    (g := dC .D4 K i z) (v := Sum.inl 1) (v' := Sum.inl 1)
    (fun j => natMat_dC_ne_single hi z j)
  rw [tensorD4, hwVec, hsingle, chiT_dC_of_ne (k := k) S hi z, one_smul]

private theorem natMat_nC_ne_zero_e1 {i : Fin 4} (hi : i ≠ 0) :
    natMat K (nC .D4 K i) *ᵥ
        (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
      (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
  rw [natMat_mulVec]
  simpa [plusVec, nC] using eta_weyl_ne_zero_e1 hi (1 : Kˣ)

private theorem natMat_xC_ne_zero_e1 {i : Fin 4} (hi : i ≠ 0) (c : K) :
    natMat K (xC .D4 K i c) *ᵥ
        (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
      (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
  rw [natMat_mulVec]
  fin_cases i
  · exact absurd rfl hi
  · simpa [plusVec] using eta_xC_one_e1 c
  · simpa [plusVec] using eta_xC_two_e1 c
  · simpa [plusVec] using eta_xC_three_e1 c

private theorem natMat_xCnC_ne_zero_e1 {i : Fin 4} (hi : i ≠ 0) (c : K) :
    natMat K (xC .D4 K i c * nC .D4 K i) *ᵥ
        (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
      (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
  rw [map_mul, ← Matrix.mulVec_mulVec, natMat_nC_ne_zero_e1 hi, natMat_xC_ne_zero_e1 hi c]

private theorem natMat_col_of_mulVec_e1 {g : adjointGroup .D4 K}
    (hg : natMat K g *ᵥ
      (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
        (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K))
    (j : Fin 4 ⊕ Fin 4) :
    natMat K g j (Sum.inl 1) = if j = Sum.inl 1 then (1 : K) else 0 := by
  by_cases hj : j = Sum.inl 1
  · subst hj
    have h := congrFun hg (Sum.inl 1)
    rw [Matrix.mulVec, dotProduct] at h
    rw [Finset.sum_eq_single (Sum.inl (1 : Fin 4))] at h
    · simpa [Pi.single_eq_same] using h
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · rw [if_neg hj]
    have h := congrFun hg j
    rw [Matrix.mulVec, dotProduct] at h
    rw [Finset.sum_eq_single (Sum.inl (1 : Fin 4))] at h
    · simpa [Pi.single_eq_same, Pi.single_eq_of_ne hj] using h
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot

private theorem tensorD4_hwVec_fix_of_e1 {S : Finset ℕ} {g : adjointGroup .D4 K}
    (hg : natMat K g *ᵥ
      (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
        (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K)) :
    tensorD4 (K := K) k S g (hwVec k S) = hwVec k S := by
  classical
  rw [tensorD4, hwVec]
  exact frobTensorRep_single_of_col_single (k := k) (M := natMat K) (S := S) (g := g)
    (v := Sum.inl 1) (v' := Sum.inl 1) (fun j => natMat_col_of_mulVec_e1 hg j)

private theorem tensorD4_xCnC_fix {S : Finset ℕ} {i : Fin 4} (hi : i ≠ 0) (c : K) :
    tensorD4 (K := K) k S (xC .D4 K i c * nC .D4 K i) (hwVec k S) = hwVec k S :=
  tensorD4_hwVec_fix_of_e1 (k := k) (S := S) (natMat_xCnC_ne_zero_e1 hi c)

private theorem dC_mem_eigenSubgroupMod {S : Finset ℕ} (i : Fin 4) (t : Kˣ) :
    tensorD4 (K := K) k S (dC .D4 K i t) (hwVec k S) =
      chiT (K := K) k S (dC .D4 K i t) • hwVec k S := by
  by_cases hi : i = 0
  · subst hi
    exact tensorD4_dC_zero (k := k) (S := S) t
  · exact tensorD4_dC_ne (k := k) (S := S) hi t

private theorem torusGroup_le_eigenSubgroupMod (S : Finset ℕ) :
    torusGroup .D4 K ≤ eigenSubgroupMod k S := by
  rw [torusGroup, Subgroup.closure_le]
  rintro g ⟨⟨i, t⟩, rfl⟩
  exact ⟨(dC .D4 K i t).2, dC_mem_eigenSubgroupMod (k := k) (S := S) i t⟩

private theorem natMat_xC0n0_e1 (c : K) :
    natMat K (xC .D4 K (0 : Fin 4) c * nC .D4 K (0 : Fin 4)) *ᵥ
        (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
      (Pi.single (Sum.inl (2 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) +
        c • (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
  rw [map_mul, ← Matrix.mulVec_mulVec]
  have hn : natMat K (nC .D4 K (0 : Fin 4)) *ᵥ
      (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
        (Pi.single (Sum.inl (2 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
    rw [natMat_mulVec]
    simpa [plusVec, nC] using eta_weyl_zero_e1 (1 : Kˣ)
  rw [hn]
  have hx : natMat K (xC .D4 K (0 : Fin 4) c) *ᵥ
      (Pi.single (Sum.inl (2 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) =
        (Pi.single (Sum.inl (2 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) +
          c • (Pi.single (Sum.inl (1 : Fin 4)) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
    rw [natMat_mulVec]
    simpa [plusVec] using eta_xC_zero_e2 c
  rw [hx]

private theorem natMat_xC0n0_diag (c : K) :
    natMat K (xC .D4 K (0 : Fin 4) c * nC .D4 K (0 : Fin 4))
      (Sum.inl (1 : Fin 4)) (Sum.inl (1 : Fin 4)) = c := by
  have h := congrFun (natMat_xC0n0_e1 c) (Sum.inl 1)
  rw [Matrix.mulVec, dotProduct] at h
  rw [Finset.sum_eq_single (Sum.inl (1 : Fin 4))] at h
  · simpa [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply] using h
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

private theorem tensorD4_xC0n0_coord (S : Finset ℕ) (c : K) :
    tensorD4 (K := K) k S (xC .D4 K (0 : Fin 4) c * nC .D4 K (0 : Fin 4))
        (hwVec k S) (fun _ => Sum.inl (1 : Fin 4)) =
      (algebraMap K k c) ^ (∑ b ∈ S, 2 ^ b) := by
  classical
  rw [tensorD4, frobTensorRep_apply]
  rw [Finset.sum_eq_single (fun _ => Sum.inl (1 : Fin 4))]
  · rw [hwVec_coord, mul_one, frobTensorMat]
    have hdiag : natMat K (xC .D4 K (0 : Fin 4) c * nC .D4 K (0 : Fin 4))
        (Sum.inl (1 : Fin 4)) (Sum.inl (1 : Fin 4)) = c := natMat_xC0n0_diag c
    simp only [hdiag]
    exact prod_frobHom_zero (k := k) (S := S) c
  · intro x _ hx
    rw [show hwVec k S x = 0 from by rw [hwVec, Pi.single_eq_of_ne hx]]
    simp
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

private theorem sum_pow_two_eq_pred {n : ℕ} {T : Finset ℕ} (hT : ∀ b ∈ T, b < n) :
    (∑ b ∈ T, 2 ^ b = 2 ^ n - 1) ↔ T = Finset.range n := by
  have hrange : ∑ b ∈ Finset.range n, 2 ^ b = 2 ^ n - 1 := by
    have := Nat.geomSum_eq (le_refl 2) n
    simpa using this
  constructor
  · intro h
    refine Finset.geomSum_injective (le_refl 2) ?_
    show (∑ b ∈ T, 2 ^ b) = ∑ b ∈ Finset.range n, 2 ^ b
    rw [h, hrange]
  · rintro rfl
    exact hrange

private theorem sum_pow_algebraMap_eq [Fintype K] [DecidableEq K] {n a : ℕ}
    (hK : Fintype.card K = 2 ^ n) (ha : a < 2 ^ n) :
    ∑ c : K, (algebraMap K k c) ^ a = if a = 2 ^ n - 1 then 1 else 0 := by
  by_cases h : a = 2 ^ n - 1
  · rw [if_pos h]
    have ha0 : a ≠ 0 := by
      have h1 : 1 < 2 ^ n := by rw [← hK]; exact Fintype.one_lt_card
      omega
    rw [← Finset.sum_erase_add (Finset.univ : Finset K) (fun c => (algebraMap K k c) ^ a)
      (Finset.mem_univ 0)]
    rw [show (algebraMap K k (0 : K)) ^ a = 0 by simp [ha0], add_zero]
    have h1 : ∑ x ∈ Finset.univ.erase (0 : K), (algebraMap K k x) ^ a =
        ∑ x : Kˣ, (algebraMap K k (x : K)) ^ a := by
      refine Finset.sum_bij
        (fun x hx => (Units.mk0 x (by rw [Finset.mem_erase] at hx; exact hx.1) : Kˣ))
        (fun x _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro x _ y _ hxy
        exact Units.ext_iff.mp hxy
      · intro y _
        exact ⟨(y : K), Finset.mem_erase.mpr ⟨y.ne_zero, Finset.mem_univ _⟩, Units.ext rfl⟩
      · intro x _
        rfl
    rw [h1]
    have h2 : ∑ x : Kˣ, (algebraMap K k (x : K)) ^ a =
        algebraMap K k (∑ x : Kˣ, ((x : K) ^ a)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun x _ => (map_pow (algebraMap K k) (x : K) a).symm
    have hdvd : Fintype.card K - 1 ∣ a := by
      simp [hK, h]
    rw [h2, FiniteField.sum_pow_units K a, if_pos hdvd, map_neg, map_one, CharTwo.neg_eq]
  · rw [if_neg h]
    have hlt : a < Fintype.card K - 1 := by
      rw [hK]
      omega
    have h0 := FiniteField.sum_pow_lt_card_sub_one K a hlt
    have h1 := congrArg (algebraMap K k) h0
    simpa only [map_sum, map_pow, map_zero] using h1

theorem isChevType_tensorD4 {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (S : Finset ℕ) (hS : ∀ b ∈ S, b < n)
    (hne : S.Nonempty) :
    IsChevType .D4 K 2 hw (tensorD4 (K := K) k S) (hwVec k S) (chiT (K := K) k S)
      (Finset.univ.erase (0 : Fin 4)) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  refine ⟨?_, hwVec_ne_zero k S, ?_, ?_⟩
  · rw [CurtisDatum.mem_fixU]
    intro u hu
    exact tensorD4_hwVec_fix (k := k) (S := S) hu
  · intro h hh
    have hmem := torusGroup_le_eigenSubgroupMod (k := k) S hh
    obtain ⟨hg, hP⟩ := hmem
    have hh' : (⟨(h : ModGL .D4 K), hg⟩ : adjointGroup .D4 K) = h := Subtype.ext rfl
    simpa [eigenProp, hh'] using hP
  · intro i
    change i ∈ Finset.univ.erase (⟨0, by decide⟩ : Fin Tag.D4.rank) ↔
      (∀ t : Kˣ, chiT (K := K) k S (dC .D4 K i t) = 1) ∧
        ((chevDatum .D4 K 2 hw).heckeT (tensorD4 (K := K) k S) i) (hwVec k S) = 0
    rw [Finset.mem_erase]
    simp only [Finset.mem_univ, and_true]
    constructor
    · intro hi0
      refine ⟨?_, ?_⟩
      · intro t
        exact chiT_dC_of_ne (k := k) S hi0 t
      · rw [heckeT_chevDatum (ρ := tensorD4 (K := K) k S) i (hwVec k S)]
        have hterm : ∀ c : K,
            tensorD4 (K := K) k S (xC .D4 K i c * nC .D4 K i) (hwVec k S) = hwVec k S :=
          fun c => tensorD4_xCnC_fix (k := k) (S := S) hi0 c
        rw [Finset.sum_congr rfl (fun c _ => hterm c)]
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k]
        have hn : 0 < n := by
          obtain ⟨b, hb⟩ := hne
          exact Nat.lt_of_le_of_lt (Nat.zero_le b) (hS b hb)
        have hcard : (Fintype.card K : k) = 0 := by
          rw [← Nat.card_eq_fintype_card, hK, Nat.cast_pow]
          have h2 : ((2 : ℕ) : k) = 0 := CharP.cast_eq_zero k 2
          rw [h2, zero_pow (Nat.pos_iff_ne_zero.mp hn)]
        rw [hcard, zero_smul]
    · rintro ⟨hchi, hT⟩
      by_contra hi0
      subst hi0
      change ∀ t : Kˣ, chiT (K := K) k S (dC .D4 K (0 : Fin 4) t) = 1 at hchi
      change ((chevDatum .D4 K 2 hw).heckeT (tensorD4 (K := K) k S) (0 : Fin 4))
        (hwVec k S) = 0 at hT
      have hn : 0 < n := by
        obtain ⟨b, hb⟩ := hne
        exact Nat.lt_of_le_of_lt (Nat.zero_le b) (hS b hb)
      by_cases hSrange : S = Finset.range n
      · have hd : (∑ b ∈ S, 2 ^ b) = 2 ^ n - 1 := by
          rw [hSrange]
          have := Nat.geomSum_eq (le_refl 2) n
          simpa using this
        have hcoord := congrFun hT (fun _ => Sum.inl (1 : Fin 4))
        rw [heckeT_chevDatum (ρ := tensorD4 (K := K) k S) (0 : Fin 4) (hwVec k S)] at hcoord
        rw [Finset.sum_apply] at hcoord
        have hterm : ∀ c : K,
            tensorD4 (K := K) k S (xC .D4 K (0 : Fin 4) c * nC .D4 K (0 : Fin 4))
              (hwVec k S) (fun _ => Sum.inl (1 : Fin 4)) =
                (algebraMap K k c) ^ (∑ b ∈ S, 2 ^ b) :=
          fun c => tensorD4_xC0n0_coord (K := K) (k := k) S c
        simp only [hterm] at hcoord
        have hdlt : (∑ b ∈ S, 2 ^ b) < 2 ^ n := by
          rw [hd]
          have h1 : 1 < 2 ^ n := by rw [← hKF]; exact Fintype.one_lt_card
          omega
        rw [sum_pow_algebraMap_eq (K := K) (k := k) hKF hdlt, if_pos hd] at hcoord
        exact one_ne_zero hcoord
      · have hlt : (∑ b ∈ S, 2 ^ b) < 2 ^ n := Nat.geomSum_lt (le_refl 2) hS
        have hle : (∑ b ∈ S, 2 ^ b) ≤ 2 ^ n - 1 := by omega
        have hne' : (∑ b ∈ S, 2 ^ b) ≠ 2 ^ n - 1 := by
          intro h
          exact hSrange ((sum_pow_two_eq_pred hS).mp h)
        have hdlt : (∑ b ∈ S, 2 ^ b) < 2 ^ n - 1 := lt_of_le_of_ne hle hne'
        have hdpos : 0 < ∑ b ∈ S, 2 ^ b := by
          obtain ⟨b, hb⟩ := hne
          have hbpos : 0 < 2 ^ b := by positivity
          have hble : 2 ^ b ≤ ∑ x ∈ S, 2 ^ x :=
            Finset.single_le_sum (fun x _ => Nat.zero_le _) hb
          exact Nat.lt_of_lt_of_le hbpos hble
        have hdvd : ¬ (Fintype.card K - 1) ∣ (∑ b ∈ S, 2 ^ b) := by
          intro hdiv
          have hle' : 2 ^ n - 1 ≤ ∑ b ∈ S, 2 ^ b := by
            rw [hKF] at hdiv
            exact Nat.le_of_dvd hdpos hdiv
          omega
        have hex : ∃ t : Kˣ, (algebraMap K k (t : K)) ^ (∑ b ∈ S, 2 ^ b) ≠ 1 := by
          by_contra hall
          push Not at hall
          have hsum0 : ∑ t : Kˣ, (algebraMap K k (t : K)) ^ (∑ b ∈ S, 2 ^ b) = 0 := by
            simp only [← map_pow]
            rw [← map_sum]
            rw [FiniteField.sum_pow_units K (∑ b ∈ S, 2 ^ b), if_neg hdvd, map_zero]
          have hsum1 : ∑ t : Kˣ, (algebraMap K k (t : K)) ^ (∑ b ∈ S, 2 ^ b) =
              ((Fintype.card K - 1 : ℕ) : k) := by
            simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_units]
            norm_num
          have hzero : ((Fintype.card K - 1 : ℕ) : k) = 0 := by
            rw [← hsum1, hsum0]
          have hnezero : ((Fintype.card K - 1 : ℕ) : k) ≠ 0 := by
            rw [← Nat.card_eq_fintype_card, hK]
            intro hzero
            rw [CharP.cast_eq_zero_iff k 2] at hzero
            have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
            have h2n1 : 2 ∣ 1 := by
              have hsub := Nat.dvd_sub h2n hzero
              have hpow : 2 ^ n - (2 ^ n - 1) = 1 := by
                have h1 : 0 < 2 ^ n := by positivity
                omega
              rwa [hpow] at hsub
            norm_num at h2n1
          exact hnezero hzero
        obtain ⟨t, ht⟩ := hex
        have hchi_t := hchi t
        rw [chiT_dC_zero (k := k) S t] at hchi_t
        exact ht hchi_t

theorem finrank_tensorD4 (S : Finset ℕ) :
    Module.finrank k ((S → Fin 4 ⊕ Fin 4) → k) = 8 ^ S.card := by
  rw [finrank_frobTensor]
  norm_num

theorem exists_equiv_frobNatRep (b : ℕ) :
    ∃ β : ((({b} : Finset ℕ) → Fin 4 ⊕ Fin 4) → k) ≃ₗ[k] (Fin 4 ⊕ Fin 4 → k),
      ∀ (g : adjointGroup .D4 K) (w : (({b} : Finset ℕ) → Fin 4 ⊕ Fin 4) → k),
        β (tensorD4 (K := K) k {b} g w) = frobNatRep (K := K) k b g (β w) := by
  classical
  let e : (({b} : Finset ℕ) → Fin 4 ⊕ Fin 4) ≃ (Fin 4 ⊕ Fin 4) :=
    { toFun := fun w => w ⟨b, by simp⟩
      invFun := fun v => fun _ => v
      left_inv := by
        intro w
        funext x
        have hx : x = (⟨b, by simp⟩ : {x // x ∈ ({b} : Finset ℕ)}) :=
          Subtype.ext (by simpa only [Finset.mem_singleton] using x.2)
        rw [hx]
      right_inv := fun v => rfl }
  have huniq : Unique ({x // x ∈ ({b} : Finset ℕ)}) :=
    { default := ⟨b, by simp⟩
      uniq := by
        intro x
        exact Subtype.ext (by simpa only [Finset.mem_singleton] using x.2) }
  refine ⟨LinearEquiv.funCongrLeft k k e.symm, ?_⟩
  intro g w
  funext x'
  rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, tensorD4, frobTensorRep_apply]
  have hterm : ∀ x : ({b} : Finset ℕ) → Fin 4 ⊕ Fin 4,
      frobTensorMat k (natMat K) ({b} : Finset ℕ) g (e.symm x') x * w x =
        frobHom k b (natMat K g x' (x ⟨b, by simp⟩)) * w x := by
    intro x
    rw [frobTensorMat]
    have huniv : (Finset.univ : Finset {y // y ∈ ({b} : Finset ℕ)}) = {⟨b, by simp⟩} := by
      ext y
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subtype.ext (by simpa only [Finset.mem_singleton] using y.2)
    rw [huniv, Finset.prod_singleton]
    simp [e]
  simp only [hterm]
  rw [show (∑ x : ({b} : Finset ℕ) → Fin 4 ⊕ Fin 4,
      frobHom k b (natMat K g x' (x ⟨b, by simp⟩)) * w x) =
      ∑ v : Fin 4 ⊕ Fin 4, frobHom k b (natMat K g x' v) * w (e.symm v) from ?_]
  · simp [frobNatRep, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, e,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  · refine (Fintype.sum_equiv e.symm (fun v : Fin 4 ⊕ Fin 4 =>
      frobHom k b (natMat K g x' v) * w (e.symm v))
      (fun x : ({b} : Finset ℕ) → Fin 4 ⊕ Fin 4 =>
        frobHom k b (natMat K g x' (x ⟨b, by simp⟩)) * w x) ?_).symm
    intro v
    simp [e]

end Model

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
