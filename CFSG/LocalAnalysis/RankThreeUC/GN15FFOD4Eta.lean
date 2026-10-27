module

public import CFSG.LocalAnalysis.StandardType.GGD4AdjointOm8
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4WeylRank
public import CFSG.LieType.SpinGeom.Elem

public section

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

@[expose] def nPerm : Fin 4 → Equiv.Perm (Fin 4 ⊕ Fin 4) :=
  ![Equiv.swap (.inl 1) (.inl 2) * Equiv.swap (.inr 1) (.inr 2),
    Equiv.swap (.inl 0) (.inl 3) * Equiv.swap (.inr 0) (.inr 3),
    Equiv.swap (.inl 2) (.inl 3) * Equiv.swap (.inr 2) (.inr 3),
    Equiv.swap (.inl 0) (.inr 3) * Equiv.swap (.inl 3) (.inr 0)]

@[expose] def invPerm : Fin 5 → Equiv.Perm (Fin 4 ⊕ Fin 4) :=
  ![Equiv.swap (.inl 1) (.inl 2) * Equiv.swap (.inr 1) (.inr 2),
    Equiv.swap (.inl 0) (.inr 0) * Equiv.swap (.inl 3) (.inr 3),
    Equiv.swap (.inl 0) (.inl 3) * Equiv.swap (.inl 1) (.inl 2) *
      (Equiv.swap (.inr 0) (.inr 3) * Equiv.swap (.inr 1) (.inr 2)),
    Equiv.swap (.inl 0) (.inr 3) * Equiv.swap (.inl 1) (.inl 2) *
      (Equiv.swap (.inl 3) (.inr 0) * Equiv.swap (.inr 1) (.inr 2)),
    Equiv.swap (.inl 0) (.inr 0) * Equiv.swap (.inl 1) (.inr 1) *
      (Equiv.swap (.inl 2) (.inr 2) * Equiv.swap (.inl 3) (.inr 3))]

section EtaAux

variable {K : Type} [Field K]

private theorem funCongrLeft_single {ι : Type} [DecidableEq ι] (e : ι ≃ ι) (a : ι) :
    LinearEquiv.funCongrLeft K K e (Pi.single a 1) = Pi.single (e.symm a) 1 := by
  rw [LinearEquiv.funCongrLeft_apply]
  funext b
  rw [LinearMap.funLeft_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : b = e.symm a
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hb
    exact h (by rw [← hb, Equiv.symm_apply_apply])

private theorem funCongrLeft_mul {ι : Type} (σ τ : Equiv.Perm ι) :
    LinearEquiv.funCongrLeft K K σ * LinearEquiv.funCongrLeft K K τ =
      LinearEquiv.funCongrLeft K K (τ * σ) := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply]
  funext a
  rw [LinearEquiv.funCongrLeft_apply, LinearEquiv.funCongrLeft_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, LinearMap.funLeft_apply,
    LinearMap.funLeft_apply, Equiv.Perm.mul_apply]

private theorem funCongrLeft_prod_map (l : List (Fin 4)) :
    (l.map (fun j => LinearEquiv.funCongrLeft K K (nPerm j))).prod =
      LinearEquiv.funCongrLeft K K (((l.map nPerm).reverse).prod) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.reverse_cons,
      List.prod_append, List.prod_singleton, funCongrLeft_mul]

end EtaAux

private theorem nPerm_symm (j : Fin 4) : (nPerm j).symm = nPerm j := by
  apply Equiv.ext
  intro a
  fin_cases j <;> rcases a with k | k <;> fin_cases k <;> decide

section EtaCharTwoAux

variable {K : Type} [Field K] [CharP K 2]

private theorem act_weyl8_pvec {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (k : Fin 4)
    (r : Bool) :
    CFSG.StandardType.D4Rank.act (weyl8 (K := K) i j s t) (CFSG.StandardType.AutOm.pvec k r) =
      if k = i then (if r = s then CFSG.StandardType.AutOm.pvec j (!t) else CFSG.StandardType.AutOm.pvec j t)
      else if k = j then (if r = t then CFSG.StandardType.AutOm.pvec i (!s) else CFSG.StandardType.AutOm.pvec i s)
      else CFSG.StandardType.AutOm.pvec k r := by
  by_cases hki : k = i
  · subst hki
    rw [if_pos rfl]
    by_cases hrs : r = s
    · rw [if_pos hrs, hrs]
      exact act_weyl8_iu hij s t
    · have hns : r = !s := by cases r <;> cases s <;> simp_all
      rw [if_neg hrs, hns]
      exact act_weyl8_inu hij s t
  · rw [if_neg hki]
    by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl]
      by_cases hrt : r = t
      · rw [if_pos hrt, hrt]
        exact act_weyl8_jt hij s t
      · have hnt : r = !t := by cases r <;> cases t <;> simp_all
        rw [if_neg hrt, hnt]
        exact act_weyl8_jnt hij s t
    · rw [if_neg hkj]
      exact act_weyl8_other (K := K) hij hki hkj s t r

end EtaCharTwoAux

section EtaPinnedAux

variable {K : Type} [Field K] [CharP K 2]

private theorem weylElt_one_eq_pinned (j : Fin Tag.D4.rank) :
    CFSG.Blueprint.Chevalley.weylElt .D4 K j 1 =
      pinnedX .D4 K (Pi.single j 1) 1 * pinnedX .D4 K (-Pi.single j 1) 1 *
        pinnedX .D4 K (Pi.single j 1) 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, pinnedX_single, pinnedX_neg_single]
  simp [CharTwo.neg_eq]

private theorem nC_eq_pinned (j : Fin Tag.D4.rank) :
    nC .D4 K j =
      (⟨pinnedX .D4 K (Pi.single j 1) 1, pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .D4 K) *
      (⟨pinnedX .D4 K (-Pi.single j 1) 1, pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .D4 K) *
      (⟨pinnedX .D4 K (Pi.single j 1) 1, pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup .D4 K) := by
  apply Subtype.ext
  change CFSG.Blueprint.Chevalley.weylElt .D4 K j 1 =
    pinnedX .D4 K (Pi.single j 1) 1 * pinnedX .D4 K (-Pi.single j 1) 1 *
      pinnedX .D4 K (Pi.single j 1) 1
  exact weylElt_one_eq_pinned j

end EtaPinnedAux

section InvWordAux


private theorem invWord_isReduced (i : Fin 5) :
    (coxeterSystem .D4).IsReduced (invWord i) := by
  apply isReduced_of_reducedCheck
  revert i
  decide +kernel

end InvWordAux

private theorem invPerm_eq_reverse_prod (i : Fin 5) :
    ((((invWord i).map nPerm).reverse).prod) = invPerm i := by
  apply Equiv.ext
  intro a
  revert i a
  decide +kernel

section Eta


variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def eta : adjointGroup .D4 K ≃* orthElementaryGroup (quadPlus 4 K) :=
  (CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose.trans
    (((statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) :
        StatedOmega (StatedQuadPlus 4 K) ≃* matrixDerived (coordinateQuadPlus 4 K))).symm.trans
      (plusDerivedEquiv 4 K (by norm_num)))

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

private theorem choose_nC_eq (j : Fin Tag.D4.rank) (i j' : Fin 4) (s t : Bool)
    (hipos : bLinv (Pi.single j 1) = fromStd (lv i j' s t))
    (hineg : bLinv (-Pi.single j 1) = fromStd (lv i j' (!s) (!t))) :
    (CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose (nC .D4 K j) =
      weyl8 i j' s t := by
  rw [nC_eq_pinned]
  simp only [map_mul]
  rw [show (CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose
        ⟨pinnedX .D4 K (Pi.single j 1) 1, pinnedX_mem_adjointGroup _ 1⟩ =
      X8 (bLinv (Pi.single j 1)) 1 from
    (CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose_spec
      (Pi.single j 1) (mem_rootFinset.2 (isRoot_single _ j)) 1]
  rw [show (CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose
        ⟨pinnedX .D4 K (-Pi.single j 1) 1, pinnedX_mem_adjointGroup _ 1⟩ =
      X8 (bLinv (-Pi.single j 1)) 1 from
    (CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose_spec
      (-Pi.single j 1) (mem_rootFinset.2 (isRoot_neg_single _ j)) 1]
  rw [hipos, hineg]
  rfl

private theorem eta_nC_frame_zero_vec (k : Fin 4) (r : Bool) :
    ((eta K (nC .D4 K (0 : Fin 4)) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K k r) =
      (LinearEquiv.funCongrLeft K K (nPerm 0)) (plusVec 4 K k r) := by
  rw [eta_apply]
  rw [show ((CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose
        (nC .D4 K (0 : Fin 4)) : Om8 K) = weyl8 1 2 true false from
    choose_nC_eq (0 : Fin 4) 1 2 true false (by decide +kernel) (by decide +kernel)]
  cases r
  case false =>
    rw [plusVec_false, funCongrLeft_single, nPerm_symm]
    change (reindexVectorEquiv (plusIndexEquiv 4)).symm
        (CFSG.StandardType.D4Rank.act (weyl8 1 2 true false) (CFSG.StandardType.AutOm.pvec k false)) =
      Pi.single ((nPerm 0) (Sum.inr k)) 1
    rw [act_weyl8_pvec (K := K) (i := 1) (j := 2) (s := true) (t := false) (k := k)
      (r := false) (by decide)]
    fin_cases k <;>
      simp [CFSG.StandardType.AutOm.pvec, LinearEquiv.symm_apply_apply, nPerm, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, Equiv.swap_apply_left, Equiv.swap_apply_right]
  case true =>
    rw [plusVec_true, funCongrLeft_single, nPerm_symm]
    change (reindexVectorEquiv (plusIndexEquiv 4)).symm
        (CFSG.StandardType.D4Rank.act (weyl8 1 2 true false) (CFSG.StandardType.AutOm.pvec k true)) =
      Pi.single ((nPerm 0) (Sum.inl k)) 1
    rw [act_weyl8_pvec (K := K) (i := 1) (j := 2) (s := true) (t := false) (k := k)
      (r := true) (by decide)]
    fin_cases k <;>
      simp [CFSG.StandardType.AutOm.pvec, LinearEquiv.symm_apply_apply, nPerm, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, Equiv.swap_apply_left, Equiv.swap_apply_right]

private theorem eta_nC_frame_zero (a : Fin 4 ⊕ Fin 4) :
    ((eta K (nC .D4 K (0 : Fin 4)) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single a 1) =
      (LinearEquiv.funCongrLeft K K (nPerm 0)) (Pi.single a 1) := by
  rcases a with k | k
  · rw [show Pi.single (Sum.inl k) 1 = plusVec 4 K k true from rfl]
    exact eta_nC_frame_zero_vec k true
  · rw [show Pi.single (Sum.inr k) 1 = plusVec 4 K k false from rfl]
    exact eta_nC_frame_zero_vec k false

private theorem eta_nC_of_frame (j : Fin 4)
    (h : ∀ a : Fin 4 ⊕ Fin 4,
      ((eta K (nC .D4 K j) : orthElementaryGroup (quadPlus 4 K)) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single a 1) =
        (LinearEquiv.funCongrLeft K K (nPerm j)) (Pi.single a 1)) :
    ((eta K (nC .D4 K j) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      LinearEquiv.funCongrLeft K K (nPerm j) := by
  refine LinearEquiv.toLinearMap_injective ?_
  refine Module.Basis.ext (Pi.basisFun K (Fin 4 ⊕ Fin 4)) ?_
  intro a
  rw [Pi.basisFun_apply]
  exact h a

private theorem eta_nC_frame_one_vec (k : Fin 4) (r : Bool) :
    ((eta K (nC .D4 K (1 : Fin 4)) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K k r) =
      (LinearEquiv.funCongrLeft K K (nPerm 1)) (plusVec 4 K k r) := by
  rw [eta_apply]
  rw [show ((CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose
        (nC .D4 K (1 : Fin 4)) : Om8 K) = weyl8 0 3 false true from
    choose_nC_eq (1 : Fin 4) 0 3 false true (by decide +kernel) (by decide +kernel)]
  cases r
  case false =>
    rw [plusVec_false, funCongrLeft_single, nPerm_symm]
    change (reindexVectorEquiv (plusIndexEquiv 4)).symm
        (CFSG.StandardType.D4Rank.act (weyl8 0 3 false true) (CFSG.StandardType.AutOm.pvec k false)) =
      Pi.single ((nPerm 1) (Sum.inr k)) 1
    rw [act_weyl8_pvec (K := K) (i := 0) (j := 3) (s := false) (t := true) (k := k)
      (r := false) (by decide)]
    fin_cases k <;>
      simp [CFSG.StandardType.AutOm.pvec, LinearEquiv.symm_apply_apply, nPerm, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, Equiv.swap_apply_left, Equiv.swap_apply_right]
  case true =>
    rw [plusVec_true, funCongrLeft_single, nPerm_symm]
    change (reindexVectorEquiv (plusIndexEquiv 4)).symm
        (CFSG.StandardType.D4Rank.act (weyl8 0 3 false true) (CFSG.StandardType.AutOm.pvec k true)) =
      Pi.single ((nPerm 1) (Sum.inl k)) 1
    rw [act_weyl8_pvec (K := K) (i := 0) (j := 3) (s := false) (t := true) (k := k)
      (r := true) (by decide)]
    fin_cases k <;>
      simp [CFSG.StandardType.AutOm.pvec, LinearEquiv.symm_apply_apply, nPerm, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, Equiv.swap_apply_left, Equiv.swap_apply_right]

private theorem eta_nC_frame_one (a : Fin 4 ⊕ Fin 4) :
    ((eta K (nC .D4 K (1 : Fin 4)) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single a 1) =
      (LinearEquiv.funCongrLeft K K (nPerm 1)) (Pi.single a 1) := by
  rcases a with k | k
  · rw [show Pi.single (Sum.inl k) 1 = plusVec 4 K k true from rfl]
    exact eta_nC_frame_one_vec k true
  · rw [show Pi.single (Sum.inr k) 1 = plusVec 4 K k false from rfl]
    exact eta_nC_frame_one_vec k false

private theorem eta_nC_frame_two_vec (k : Fin 4) (r : Bool) :
    ((eta K (nC .D4 K (2 : Fin 4)) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K k r) =
      (LinearEquiv.funCongrLeft K K (nPerm 2)) (plusVec 4 K k r) := by
  rw [eta_apply]
  rw [show ((CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose
        (nC .D4 K (2 : Fin 4)) : Om8 K) = weyl8 2 3 true false from
    choose_nC_eq (2 : Fin 4) 2 3 true false (by decide +kernel) (by decide +kernel)]
  cases r
  case false =>
    rw [plusVec_false, funCongrLeft_single, nPerm_symm]
    change (reindexVectorEquiv (plusIndexEquiv 4)).symm
        (CFSG.StandardType.D4Rank.act (weyl8 2 3 true false) (CFSG.StandardType.AutOm.pvec k false)) =
      Pi.single ((nPerm 2) (Sum.inr k)) 1
    rw [act_weyl8_pvec (K := K) (i := 2) (j := 3) (s := true) (t := false) (k := k)
      (r := false) (by decide)]
    fin_cases k <;>
      simp [CFSG.StandardType.AutOm.pvec, LinearEquiv.symm_apply_apply, nPerm, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, Equiv.swap_apply_left, Equiv.swap_apply_right]
  case true =>
    rw [plusVec_true, funCongrLeft_single, nPerm_symm]
    change (reindexVectorEquiv (plusIndexEquiv 4)).symm
        (CFSG.StandardType.D4Rank.act (weyl8 2 3 true false) (CFSG.StandardType.AutOm.pvec k true)) =
      Pi.single ((nPerm 2) (Sum.inl k)) 1
    rw [act_weyl8_pvec (K := K) (i := 2) (j := 3) (s := true) (t := false) (k := k)
      (r := true) (by decide)]
    fin_cases k <;>
      simp [CFSG.StandardType.AutOm.pvec, LinearEquiv.symm_apply_apply, nPerm, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, Equiv.swap_apply_left, Equiv.swap_apply_right]

private theorem eta_nC_frame_two (a : Fin 4 ⊕ Fin 4) :
    ((eta K (nC .D4 K (2 : Fin 4)) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single a 1) =
      (LinearEquiv.funCongrLeft K K (nPerm 2)) (Pi.single a 1) := by
  rcases a with k | k
  · rw [show Pi.single (Sum.inl k) 1 = plusVec 4 K k true from rfl]
    exact eta_nC_frame_two_vec k true
  · rw [show Pi.single (Sum.inr k) 1 = plusVec 4 K k false from rfl]
    exact eta_nC_frame_two_vec k false

private theorem eta_nC_frame_three_vec (k : Fin 4) (r : Bool) :
    ((eta K (nC .D4 K (3 : Fin 4)) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (plusVec 4 K k r) =
      (LinearEquiv.funCongrLeft K K (nPerm 3)) (plusVec 4 K k r) := by
  rw [eta_apply]
  rw [show ((CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)).choose
        (nC .D4 K (3 : Fin 4)) : Om8 K) = weyl8 0 3 true true from
    choose_nC_eq (3 : Fin 4) 0 3 true true (by decide +kernel) (by decide +kernel)]
  cases r
  case false =>
    rw [plusVec_false, funCongrLeft_single, nPerm_symm]
    change (reindexVectorEquiv (plusIndexEquiv 4)).symm
        (CFSG.StandardType.D4Rank.act (weyl8 0 3 true true) (CFSG.StandardType.AutOm.pvec k false)) =
      Pi.single ((nPerm 3) (Sum.inr k)) 1
    rw [act_weyl8_pvec (K := K) (i := 0) (j := 3) (s := true) (t := true) (k := k)
      (r := false) (by decide)]
    fin_cases k <;>
      simp [CFSG.StandardType.AutOm.pvec, LinearEquiv.symm_apply_apply, nPerm, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, Equiv.swap_apply_right]
  case true =>
    rw [plusVec_true, funCongrLeft_single, nPerm_symm]
    change (reindexVectorEquiv (plusIndexEquiv 4)).symm
        (CFSG.StandardType.D4Rank.act (weyl8 0 3 true true) (CFSG.StandardType.AutOm.pvec k true)) =
      Pi.single ((nPerm 3) (Sum.inl k)) 1
    rw [act_weyl8_pvec (K := K) (i := 0) (j := 3) (s := true) (t := true) (k := k)
      (r := true) (by decide)]
    fin_cases k <;>
      simp [CFSG.StandardType.AutOm.pvec, LinearEquiv.symm_apply_apply, nPerm, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, Equiv.swap_apply_left]

private theorem eta_nC_frame_three (a : Fin 4 ⊕ Fin 4) :
    ((eta K (nC .D4 K (3 : Fin 4)) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (Pi.single a 1) =
      (LinearEquiv.funCongrLeft K K (nPerm 3)) (Pi.single a 1) := by
  rcases a with k | k
  · rw [show Pi.single (Sum.inl k) 1 = plusVec 4 K k true from rfl]
    exact eta_nC_frame_three_vec k true
  · rw [show Pi.single (Sum.inr k) 1 = plusVec 4 K k false from rfl]
    exact eta_nC_frame_three_vec k false

theorem eta_nC (j : Fin 4) :
    ((eta K (nC .D4 K j) : orthElementaryGroup (quadPlus 4 K)) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      LinearEquiv.funCongrLeft K K (nPerm j) := by
  fin_cases j
  · exact eta_nC_of_frame 0 eta_nC_frame_zero
  · exact eta_nC_of_frame 1 eta_nC_frame_one
  · exact eta_nC_of_frame 2 eta_nC_frame_two
  · exact eta_nC_of_frame 3 eta_nC_frame_three

private theorem eta_weylElement (j : Fin 4) :
    eta K (weylElement .D4 K j) = LinearEquiv.funCongrLeft K K (nPerm j) := by
  rw [show weylElement .D4 K j = nC .D4 K j from rfl]
  exact eta_nC j

theorem eta_nW_invWord {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
    (i : Fin 5) :
    ((eta K ((chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord i))) :
        orthElementaryGroup (quadPlus 4 K)) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      LinearEquiv.funCongrLeft K K (invPerm i) := by
  let l : List (Fin Tag.D4.rank) := invWord i
  have hred : (coxeterSystem .D4).IsReduced l := invWord_isReduced i
  have hnW : (chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord i)) =
      nrep .D4 K ((coxeterSystem .D4).wordProd l) := rfl
  rw [hnW, nrep_eq_prod .D4 K hred]
  rw [map_list_prod, List.map_map]
  change (List.map (fun j : Fin Tag.D4.rank => eta K (weylElement .D4 K j)) l).prod =
    LinearEquiv.funCongrLeft K K (invPerm i)
  rw [show ((List.map (fun j : Fin Tag.D4.rank => eta K (weylElement .D4 K j)) l).prod :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
      (List.map (fun j : Fin Tag.D4.rank => LinearEquiv.funCongrLeft K K (nPerm j)) l).prod from by
    rw [Subgroup.val_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun j _ => eta_weylElement (K := K) (j : Fin 4)]
  rw [show (List.map (fun j : Fin Tag.D4.rank => LinearEquiv.funCongrLeft K K (nPerm j)) l).prod =
      (List.map (fun j : Fin 4 => LinearEquiv.funCongrLeft K K (nPerm j)) (invWord i)).prod from rfl]
  rw [funCongrLeft_prod_map, invPerm_eq_reverse_prod]

end Eta

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
