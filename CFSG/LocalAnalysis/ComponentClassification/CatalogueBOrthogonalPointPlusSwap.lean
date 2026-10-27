module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwapOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbitBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalStabilizerRigidityAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalPointAction CatalogueBOrthogonalPointPlusBorel
open CatalogueBOrthogonalPointReindexCovariance CatalogueBStabilizerFamily
open CatalogueBOrthogonalSmallFamilyOrbit
open scoped Pointwise

section Covariant

universe u w

variable {G : Type u} [Group G] {X : Type w}

theorem pointStabilizer_map_of_covariant (rho : G →* Equiv.Perm X) (e : MulAut G)
    (σ : Equiv.Perm X) (hcov : ∀ g x, rho (e g) (σ x) = σ (rho g x)) (x : X) :
    (pointStabilizer rho x).map e.toMonoidHom = pointStabilizer rho (σ x) := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_pointStabilizer_iff, mem_pointStabilizer_iff]
  have hh := hcov (e.symm h) x
  rw [MulEquiv.apply_symm_apply] at hh
  rw [hh, σ.injective.eq_iff]

theorem smul_family_of_covariant (rho : G →* Equiv.Perm X) (e : MulAut G) (σ : Equiv.Perm X)
    (hcov : ∀ g x, rho (e g) (σ x) = σ (rho g x)) : e • family rho = family rho := by
  ext U
  constructor
  · rintro ⟨V, ⟨x, rfl⟩, rfl⟩
    exact ⟨σ x, (pointStabilizer_map_of_covariant rho e σ hcov x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨pointStabilizer rho (σ.symm x), ⟨σ.symm x, rfl⟩, ?_⟩
    change (pointStabilizer rho (σ.symm x)).map e.toMonoidHom = pointStabilizer rho x
    rw [pointStabilizer_map_of_covariant rho e σ hcov, Equiv.apply_symm_apply]

theorem mem_conjugacyFamily_self (H : Subgroup G) : H ∈ conjugacyFamily H :=
  ⟨1, Subgroup.conj_smul_eq_self_of_mem (one_mem H)⟩

end Covariant

section Stabilizers

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (Q0 : (ι → K) → K)

theorem statedProjectiveSubspaceStabilizer_eq_pointStabilizer (W : Submodule K (ι → K)) :
    statedProjectiveSubspaceStabilizer Q0 W =
      pointStabilizer (statedProjectiveSubspaceAction Q0) W :=
  Subgroup.ext fun _ => Iff.rfl

theorem statedProjectiveSubspaceStabilizer_map_conj (g : StatedProj (StatedOmega Q0))
    (W : Submodule K (ι → K)) :
    (statedProjectiveSubspaceStabilizer Q0 W).map (MulAut.conj g).toMonoidHom =
      statedProjectiveSubspaceStabilizer Q0 (statedProjectiveSubspaceAction Q0 g W) := by
  rw [statedProjectiveSubspaceStabilizer_eq_pointStabilizer,
    statedProjectiveSubspaceStabilizer_eq_pointStabilizer]
  exact pointStabilizer_conj _ g W

theorem statedProjectiveSubspaceStabilizer_comap_mk (W : Submodule K (ι → K)) :
    (statedProjectiveSubspaceStabilizer Q0 W).comap
        (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q0))) =
      statedDerivedSubspaceStabilizer Q0 W :=
  Subgroup.ext fun g => mem_statedProjectiveSubspaceStabilizer_mk Q0 W g

end Stabilizers

section Swap

variable (n : ℕ) (K : Type) [Field K]

@[expose] def plusSwapPerm (hn : 0 < n) : Equiv.Perm (Fin n ⊕ Fin n) :=
  Equiv.swap (Sum.inl ⟨n - 1, by omega⟩) (Sum.inr ⟨n - 1, by omega⟩)

theorem plusSwapPerm_mul_self (hn : 0 < n) : plusSwapPerm n hn * plusSwapPerm n hn = 1 :=
  Equiv.swap_mul_self _ _

@[expose] def plusSwapMatrix (hn : 0 < n) : GL (Fin n ⊕ Fin n) K where
  val := (plusSwapPerm n hn).permMatrix K
  inv := (plusSwapPerm n hn).permMatrix K
  val_inv := by rw [← Matrix.permMatrix_mul, plusSwapPerm_mul_self, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul, plusSwapPerm_mul_self, Matrix.permMatrix_one]

theorem coe_plusSwapMatrix (hn : 0 < n) :
    (plusSwapMatrix n K hn : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (plusSwapPerm n hn).permMatrix K := rfl

theorem plusSwapMatrix_inv (hn : 0 < n) : (plusSwapMatrix n K hn)⁻¹ = plusSwapMatrix n K hn :=
  Units.ext rfl

theorem plusSwapMatrix_mul_self (hn : 0 < n) :
    plusSwapMatrix n K hn * plusSwapMatrix n K hn = 1 :=
  Units.ext (plusSwapMatrix n K hn).val_inv

theorem toLinEquiv_plusSwapMatrix (hn : 0 < n) :
    toLinEquiv (Fin n ⊕ Fin n) K (plusSwapMatrix n K hn) = swapPair K ⟨n - 1, by omega⟩ := by
  refine LinearEquiv.ext fun v => funext fun c => ?_
  rw [toLinEquiv_apply, coe_plusSwapMatrix, Matrix.permMatrix_mulVec, swapPair_apply]
  rfl

theorem statedQuadPlus_plusSwapMatrix_mulVec (hn : 0 < n) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n K
        ((plusSwapMatrix n K hn : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) =
      StatedQuadPlus n K v := by
  rw [← coe_quadPlus, ← toLinEquiv_apply, toLinEquiv_plusSwapMatrix]
  exact quadPlus_swapPair _ v

theorem plusSwapMatrix_mem_closure (hn : 0 < n) :
    plusSwapMatrix n K hn ∈ Subgroup.closure {A : GL (Fin n ⊕ Fin n) K |
      ∀ v, StatedQuadPlus n K ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) =
        StatedQuadPlus n K v} :=
  Subgroup.subset_closure (statedQuadPlus_plusSwapMatrix_mulVec n K hn)

theorem statedOmega_map_conj_plusSwapMatrix (hn : 0 < n) :
    (StatedOmega (StatedQuadPlus n K)).map (MulAut.conj (plusSwapMatrix n K hn)).toMonoidHom =
      StatedOmega (StatedQuadPlus n K) := by
  rw [StatedOmega, Subgroup.map_commutator]
  congr 1 <;> exact Subgroup.conj_smul_eq_self_of_mem (plusSwapMatrix_mem_closure n K hn)

theorem plusSwapMatrix_conj_mem (hn : 0 < n) {A : GL (Fin n ⊕ Fin n) K}
    (hA : A ∈ StatedOmega (StatedQuadPlus n K)) :
    plusSwapMatrix n K hn * A * (plusSwapMatrix n K hn)⁻¹ ∈ StatedOmega (StatedQuadPlus n K) := by
  rw [← statedOmega_map_conj_plusSwapMatrix n K hn]
  exact Subgroup.mem_map_of_mem _ hA

theorem plusSwapMatrix_conj_scalar (hn : 0 < n) {A : GL (Fin n ⊕ Fin n) K}
    (hA : A ∈ StatedScalars (Fin n ⊕ Fin n) K) :
    plusSwapMatrix n K hn * A * (plusSwapMatrix n K hn)⁻¹ = A := by
  have hc : A ∈ Subgroup.center (GL (Fin n ⊕ Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hA
  rw [Subgroup.mem_center_iff.mp hc (plusSwapMatrix n K hn), mul_inv_cancel_right]

theorem statedScalars_map_conj_plusSwapMatrix (hn : 0 < n) :
    (StatedScalars (Fin n ⊕ Fin n) K).map (MulAut.conj (plusSwapMatrix n K hn)).toMonoidHom =
      StatedScalars (Fin n ⊕ Fin n) K :=
  Subgroup.Normal.map_conj_eq _ _

@[expose] def plusSwapDerived (hn : 0 < n) : MulAut (StatedOmega (StatedQuadPlus n K)) :=
  ((MulAut.conj (plusSwapMatrix n K hn)).subgroupMap (StatedOmega (StatedQuadPlus n K))).trans
    (MulEquiv.subgroupCongr (statedOmega_map_conj_plusSwapMatrix n K hn))

theorem plusSwapDerived_val (hn : 0 < n) (A : StatedOmega (StatedQuadPlus n K)) :
    (plusSwapDerived n K hn A : GL (Fin n ⊕ Fin n) K) =
      plusSwapMatrix n K hn * A * (plusSwapMatrix n K hn)⁻¹ := rfl

theorem plusSwapDerived_scalar (hn : 0 < n) {A : StatedOmega (StatedQuadPlus n K)}
    (hA : A ∈ (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))) :
    plusSwapDerived n K hn A = A :=
  Subtype.ext ((plusSwapDerived_val n K hn A).trans (plusSwapMatrix_conj_scalar n K hn hA))

theorem plusSwapDerived_scalars (hn : 0 < n) :
    ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))).map
        (plusSwapDerived n K hn).toMonoidHom =
      (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K)) := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    change plusSwapDerived n K hn B ∈ _
    rw [plusSwapDerived_scalar n K hn hB]
    exact hB
  · intro hA
    exact ⟨A, hA, plusSwapDerived_scalar n K hn hA⟩

@[expose] def plusSwapAut (hn : 0 < n) : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
  QuotientGroup.congr _ _ (plusSwapDerived n K hn) (plusSwapDerived_scalars n K hn)

theorem plusSwapAut_mk (hn : 0 < n) (A : StatedOmega (StatedQuadPlus n K)) :
    plusSwapAut n K hn (QuotientGroup.mk' _ A) =
      QuotientGroup.mk' _ (plusSwapDerived n K hn A) :=
  QuotientGroup.congr_mk' _ _ _ _ A

theorem plusSwapAut_mk_conj (hn : 0 < n) (A : StatedOmega (StatedQuadPlus n K)) :
    plusSwapAut n K hn (QuotientGroup.mk' _ A) =
      QuotientGroup.mk' _ ⟨plusSwapMatrix n K hn * A * (plusSwapMatrix n K hn)⁻¹,
        plusSwapMatrix_conj_mem n K hn A.property⟩ :=
  plusSwapAut_mk n K hn A

theorem map_plusSwapDerived (hn : 0 < n) (A : StatedOmega (StatedQuadPlus n K))
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    (W.map (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap).map
        (toLinEquiv _ K (plusSwapDerived n K hn A).val).toLinearMap =
      (W.map (toLinEquiv _ K A.val).toLinearMap).map
        (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap := by
  rw [plusSwapDerived_val, map_mul, map_mul, map_inv, ← map_mul_linearEquiv,
    ← map_mul_linearEquiv, inv_mul_cancel_right]

theorem statedProjectiveSubspaceAction_plusSwapAut (hn : 0 < n)
    (g : StatedProj (StatedOmega (StatedQuadPlus n K))) (W : Submodule K (Fin n ⊕ Fin n → K)) :
    statedProjectiveSubspaceAction (StatedQuadPlus n K) (plusSwapAut n K hn g)
        (W.map (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap) =
      (statedProjectiveSubspaceAction (StatedQuadPlus n K) g W).map
        (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [plusSwapAut_mk, statedProjectiveSubspaceAction_mk_apply,
    statedProjectiveSubspaceAction_mk_apply]
  exact map_plusSwapDerived n K hn A W

theorem statedProjectiveSubspaceStabilizer_map_plusSwapAut (hn : 0 < n)
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W).map
        (plusSwapAut n K hn).toMonoidHom =
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
        (W.map (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap) := by
  ext x
  rw [Subgroup.mem_map_equiv]
  change statedProjectiveSubspaceAction _ ((plusSwapAut n K hn).symm x) W = W ↔
    statedProjectiveSubspaceAction _ x
        (W.map (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap) =
      W.map (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap
  have h := statedProjectiveSubspaceAction_plusSwapAut n K hn ((plusSwapAut n K hn).symm x) W
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  exact (Submodule.map_injective_of_injective
    (toLinEquiv _ K (plusSwapMatrix n K hn)).injective).eq_iff.symm

theorem map_flag_plusSwapMatrix (hn : 0 < n) :
    (flag n K n).map (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap = Xstar n K hn := by
  rw [toLinEquiv_plusSwapMatrix]
  exact map_swapPair_flag hn

theorem map_Xstar_plusSwapMatrix (hn : 0 < n) :
    (Xstar n K hn).map (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap = flag n K n := by
  rw [toLinEquiv_plusSwapMatrix]
  exact map_swapPair_Xstar hn

theorem statedPointAction_plusSwapAut (hn : 0 < n)
    (g : StatedProj (StatedOmega (StatedQuadPlus n K))) (L : Points (quadPlus n K)) :
    statedPointAction (coe_quadPlus n K) (plusSwapAut n K hn g)
        (orthogonalPointAction (quadPlus n K) (swapIso K ⟨n - 1, by omega⟩) L) =
      orthogonalPointAction (quadPlus n K) (swapIso K ⟨n - 1, by omega⟩)
        (statedPointAction (coe_quadPlus n K) g L) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  apply Subtype.ext
  rw [plusSwapAut_mk, statedPointAction_mk_submodule, orthogonalPointAction_submodule,
    orthogonalPointAction_submodule, statedPointAction_mk_submodule, coe_swapIso,
    ← toLinEquiv_plusSwapMatrix n K hn]
  exact map_plusSwapDerived n K hn A L.val

theorem plusSwapAut_smul_statedPointFamily (hn : 0 < n) :
    plusSwapAut n K hn • statedPointFamily (coe_quadPlus n K) =
      statedPointFamily (coe_quadPlus n K) :=
  smul_family_of_covariant (statedPointAction (coe_quadPlus n K)) (plusSwapAut n K hn)
    (orthogonalPointAction (quadPlus n K) (swapIso K ⟨n - 1, by omega⟩))
    (statedPointAction_plusSwapAut n K hn)

theorem plusSwapAut_smul_conjugacyFamily (hn : 0 < n) (W : Submodule K (Fin n ⊕ Fin n → K)) :
    plusSwapAut n K hn •
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) W) =
      conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
        (W.map (toLinEquiv _ K (plusSwapMatrix n K hn)).toLinearMap)) := by
  rw [conjugacyFamily_covariance, statedProjectiveSubspaceStabilizer_map_plusSwapAut]

theorem plusSwapAut_smul_conjugacyFamily_flag (hn : 0 < n) :
    plusSwapAut n K hn •
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n)) =
      conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K hn)) := by
  rw [plusSwapAut_smul_conjugacyFamily, map_flag_plusSwapMatrix]

theorem plusSwapAut_smul_conjugacyFamily_Xstar (hn : 0 < n) :
    plusSwapAut n K hn •
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K hn)) =
      conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n)) := by
  rw [plusSwapAut_smul_conjugacyFamily, map_Xstar_plusSwapMatrix]

theorem conjugacyFamily_flag_ne_Xstar [Finite K] (hn : 3 ≤ n) :
    conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n)) ≠
      conjugacyFamily
        (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K (by omega))) := by
  intro h
  have hmem := mem_conjugacyFamily_self
    (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K (by omega)))
  rw [← h] at hmem
  obtain ⟨g, hg⟩ := hmem
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hP : statedProjectiveSubspaceStabilizer (StatedQuadPlus n K)
        ((flag n K n).map (toLinEquiv _ K A.val).toLinearMap) =
      statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K (by omega)) := by
    rw [← statedProjectiveSubspaceAction_mk_apply, ← statedProjectiveSubspaceStabilizer_map_conj]
    exact hg
  have hD := congrArg (Subgroup.comap (QuotientGroup.mk'
    ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedOmega (StatedQuadPlus n K))))) hP
  rw [statedProjectiveSubspaceStabilizer_comap_mk,
    statedProjectiveSubspaceStabilizer_comap_mk] at hD
  have hE := congrArg (Subgroup.map (statedOmegaEquiv (coe_quadPlus n K)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn)).toMonoidHom) hD
  rw [statedDerivedSubspaceStabilizer_map_elementary,
    statedDerivedSubspaceStabilizer_map_elementary] at hE
  obtain ⟨hX, hXs, -, -, -, hdisj, -⟩ := orthogonal_geometry_split_maximal_family_orbits (K := K) hn
  have hdim : Module.finrank K (Fin n ⊕ Fin n → K) =
      2 * Module.finrank K (Xstar n K (by omega)) := by
    rw [hXs.1, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hNdim : Module.finrank K ((flag n K n).map (toLinEquiv _ K A.val).toLinearMap) =
      Module.finrank K (Xstar n K (by omega)) := by
    rw [LinearEquiv.finrank_map_eq, hX.1, hXs.1]
  have heq := (CatalogueBOrthogonalStabilizerRigidity.elementaryStabilizer_eq_iff
    (nondegenerate_polarBilin_quadPlus n K) hXs.2 hdim (by rw [hXs.1]; omega) hNdim).mp hE.symm
  have hA : toLinEquiv _ K A.val ∈ orthElementaryGroup (quadPlus n K) :=
    (plusDerivedEquiv n K hn A).property
  exact Set.disjoint_left.mp hdisj (mem_orbit_elementary.2 ⟨_, hA, heq.symm⟩)
    (MulAction.mem_orbit_self _)

theorem statedPointFamily_orbit_card [Finite K] (hn : 3 ≤ n)
    (hO : MulAction.orbit (MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))))
        (statedPointFamily (coe_quadPlus n K)) ⊆
      {statedPointFamily (coe_quadPlus n K),
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n)),
        conjugacyFamily
          (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K (by omega)))}) :
    Nat.card (MulAction.orbit (MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))))
        (statedPointFamily (coe_quadPlus n K))) = 1 ∨
      Nat.card (MulAction.orbit (MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))))
        (statedPointFamily (coe_quadPlus n K))) = 3 :=
  orbit_card_eq_one_or_three hO (plusSwapAut_smul_statedPointFamily n K (by omega))
    (plusSwapAut_smul_conjugacyFamily_flag n K (by omega))
    (plusSwapAut_smul_conjugacyFamily_Xstar n K (by omega)) (conjugacyFamily_flag_ne_Xstar n K hn)

theorem exists_conj_smul_statedPointFamily [Finite K] (hn : 3 ≤ n)
    (hO : MulAction.orbit (MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))))
        (statedPointFamily (coe_quadPlus n K)) ⊆
      {statedPointFamily (coe_quadPlus n K),
        conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n)),
        conjugacyFamily
          (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K (by omega)))})
    (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K)))) (hα : α * α = 1) :
    ∃ β : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))),
      (β⁻¹ * α * β) • statedPointFamily (coe_quadPlus n K) =
        statedPointFamily (coe_quadPlus n K) :=
  exists_conj_smul_eq_self_of_orbit_swap hO (plusSwapAut_smul_statedPointFamily n K (by omega))
    (plusSwapAut_smul_conjugacyFamily_flag n K (by omega))
    (plusSwapAut_smul_conjugacyFamily_Xstar n K (by omega)) (conjugacyFamily_flag_ne_Xstar n K hn)
    α hα

end Swap

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
