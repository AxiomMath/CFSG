module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankTwoLevi
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoNormalizer
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open Module Submodule
open scoped Pointwise LinearAlgebra.Projectivization

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

section Conj

variable {h : UnitaryFieldData p f K}

theorem inv_le_iff_of_forall {ψ : Equiv.Perm (hypIsotropicLines h r ε)}
    {W : Submodule K (HypIndex r ε → K)}
    (hW : ∀ L : hypIsotropicLines h r ε, ((ψ L : Submodule K (HypIndex r ε → K)) ≤ W ↔
      (L : Submodule K (HypIndex r ε → K)) ≤ W)) (L : hypIsotropicLines h r ε) :
    ((ψ⁻¹ L : hypIsotropicLines h r ε) : Submodule K (HypIndex r ε → K)) ≤ W ↔
      (L : Submodule K (HypIndex r ε → K)) ≤ W := by
  rw [← hW (ψ⁻¹ L), Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

theorem conj_mem_xyPointStab {ψ : Equiv.Perm (hypIsotropicLines h r ε)}
    (hψ : ψ ∈ lineNormalizer h r ε)
    (hX : ∀ L : hypIsotropicLines h r ε, ((ψ L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε ↔
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε))
    (hY : ∀ L : hypIsotropicLines h r ε, ((ψ L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε ↔
      (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε))
    {x : Equiv.Perm (hypIsotropicLines h r ε)} (hx : x ∈ xyPointStab h r ε) :
    ψ * x * ψ⁻¹ ∈ xyPointStab h r ε := by
  obtain ⟨hxG, hxX, hxY⟩ := (mem_xyPointStab h).mp hx
  refine (mem_xyPointStab h).mpr ⟨(Subgroup.mem_normalizer_iff.mp hψ x).mp hxG,
    fun L => ?_, fun L => ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hX, hxX]
    exact inv_le_iff_of_forall hX L
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hY, hxY]
    exact inv_le_iff_of_forall hY L

theorem conj_mem_leviPointGroup (hε : ε ≤ 1) {ψ : Equiv.Perm (hypIsotropicLines h 2 ε)}
    (hψ : ψ ∈ lineNormalizer h 2 ε)
    (hX : ∀ L : hypIsotropicLines h 2 ε, ((ψ L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε ↔
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε))
    (hY : ∀ L : hypIsotropicLines h 2 ε, ((ψ L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε ↔
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε))
    {x : Equiv.Perm (hypIsotropicLines h 2 ε)} (hx : x ∈ leviPointGroup h 2 ε) :
    ψ * x * ψ⁻¹ ∈ leviPointGroup h 2 ε := by
  have hD := (unitary_rank_two_opposite_levi h hε).1
  rw [← hD] at hx ⊢
  have hmap : (xyPointStab h 2 ε).map (MulAut.conj ψ).toMonoidHom ≤ xyPointStab h 2 ε :=
    Subgroup.map_le_iff_le_comap.mpr fun y hy => conj_mem_xyPointStab hψ hX hY hy
  have hcomm := Subgroup.commutator_mono hmap hmap
  rw [← Subgroup.map_commutator] at hcomm
  exact hcomm ⟨x, hx, rfl⟩

end Conj

section XPtPerm

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def xPtEquiv (ε : ℕ) : ℙ K (Fin r → K) ≃
    {L : hypIsotropicLines h r ε // (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε} :=
  Equiv.ofBijective (fun U => ⟨xPt h ε U, xPt_le h U⟩)
    ⟨fun _ _ hU => xPt_injective h (congrArg Subtype.val hU), fun L => by
      obtain ⟨U, hU⟩ := exists_xPt_eq h L.1 L.2
      exact ⟨U, Subtype.ext hU⟩⟩

variable {h}

@[expose] noncomputable def xPtPerm {ψ : Equiv.Perm (hypIsotropicLines h r ε)}
    (hX : ∀ L : hypIsotropicLines h r ε, ((ψ L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε ↔
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε)) : Equiv.Perm (ℙ K (Fin r → K)) :=
  (xPtEquiv h ε).symm.permCongr (ψ.subtypePerm hX)

theorem xPt_xPtPerm {ψ : Equiv.Perm (hypIsotropicLines h r ε)}
    (hX : ∀ L : hypIsotropicLines h r ε, ((ψ L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε ↔
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε)) (U : ℙ K (Fin r → K)) :
    xPt h ε (xPtPerm hX U) = ψ (xPt h ε U) := by
  change (((xPtEquiv h ε) ((xPtEquiv h ε).symm (ψ.subtypePerm hX (xPtEquiv h ε U))) :
    {L : hypIsotropicLines h r ε // (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε}) :
      hypIsotropicLines h r ε) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem xPtPerm_smul {ψ : Equiv.Perm (hypIsotropicLines h r ε)}
    (hX : ∀ L : hypIsotropicLines h r ε, ((ψ L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε ↔
      (L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε))
    {A B : SpecialLinearGroup (Fin r) K}
    (hAB : ψ * hypProjLineAction h r ε (hypProj h r ε (leviSU h ε A)) =
      hypProjLineAction h r ε (hypProj h r ε (leviSU h ε B)) * ψ) (U : ℙ K (Fin r → K)) :
    xPtPerm hX (A • U) = B • xPtPerm hX U := by
  apply xPt_injective h (ε := ε)
  rw [xPt_xPtPerm, ← leviSU_smul_xPt h, ← leviSU_smul_xPt h, xPt_xPtPerm]
  exact congrArg (fun g : Equiv.Perm (hypIsotropicLines h r ε) => g (xPt h ε U)) hAB

end XPtPerm

section Coordinates

theorem coordinatePSLAction_mk_apply (A : SpecialLinearGroup (Fin 2) K) (x : Omega K) :
    coordinatePSLAction K (QuotientGroup.mk A) x =
      (coordinateEquiv K).symm (A • coordinateEquiv K x) :=
  (coordinateEquiv K).injective (by
    rw [coordinatePSLAction_point, Equiv.apply_symm_apply]
    rfl)

theorem permCongr_mul_coordinatePSLAction {π : Equiv.Perm (ℙ K (Fin 2 → K))}
    {A B : SpecialLinearGroup (Fin 2) K} (hAB : ∀ U, π (A • U) = B • π U) :
    (coordinateEquiv K).symm.permCongr π * coordinatePSLAction K (QuotientGroup.mk A) =
      coordinatePSLAction K (QuotientGroup.mk B) * (coordinateEquiv K).symm.permCongr π := by
  refine Equiv.ext fun x => ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, coordinatePSLAction_mk_apply,
    coordinatePSLAction_mk_apply, Equiv.permCongr_apply, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, hAB]

theorem permCongr_mem_normalizer {π : Equiv.Perm (ℙ K (Fin 2 → K))}
    (h1 : ∀ A : SpecialLinearGroup (Fin 2) K, ∃ B : SpecialLinearGroup (Fin 2) K,
      ∀ U, π (A • U) = B • π U)
    (h2 : ∀ B : SpecialLinearGroup (Fin 2) K, ∃ A : SpecialLinearGroup (Fin 2) K,
      ∀ U, π (A • U) = B • π U) :
    (coordinateEquiv K).symm.permCongr π ∈
      Subgroup.normalizer (coordinateG K : Set (Equiv.Perm (Omega K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [← coordinatePSLAction_range_eq_G]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨B, hB⟩ := h1 A
    refine ⟨QuotientGroup.mk B, ?_⟩
    rw [permCongr_mul_coordinatePSLAction hB, mul_inv_cancel_right]
  · rintro ⟨y, hy⟩
    obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨A, hA⟩ := h2 B
    refine ⟨QuotientGroup.mk A, mul_left_cancel (a := (coordinateEquiv K).symm.permCongr π) ?_⟩
    rw [permCongr_mul_coordinatePSLAction hA, hy, inv_mul_cancel_right]

theorem submodule_pgl_smul (A : GL (Fin 2) K) (V : ℙ K (Fin 2 → K)) :
    (Matrix.ProjGenLinGroup.mk A • V).submodule =
      V.submodule.map (mulVecLin (A : Matrix (Fin 2) (Fin 2) K)) := by
  induction V using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.PGL.mk_smul_mk, Projectivization.submodule_mk,
      Projectivization.submodule_mk, Submodule.map_span, Set.image_singleton]
    rfl

theorem submodule_coordinateEquiv_fieldExtension (σ : K ≃+* K) (x : Omega K) :
    (coordinateEquiv K (fieldExtension K σ x)).submodule =
      LinearFlag.coordImage σ (coordinateEquiv K x).submodule := by
  cases x with
  | none =>
    rw [fieldExtension_none, coordinateEquiv_none, CFSG.GorensteinWalter.psl2ProjectiveInfinity,
      Projectivization.submodule_mk, ProjectiveGeometry.coordImage_span_singleton]
    rw [show (fun i => σ ((![1, 0] : Fin 2 → K) i)) = ![1, 0] by
      funext i
      fin_cases i <;> simp]
  | some a =>
    rw [fieldExtension_some, coordinateEquiv_some, coordinateEquiv_some,
      CFSG.GorensteinWalter.psl2AffinePoint, CFSG.GorensteinWalter.psl2AffinePoint,
      Projectivization.submodule_mk, Projectivization.submodule_mk,
      ProjectiveGeometry.coordImage_span_singleton]
    rw [show (fun i => σ ((![a, 1] : Fin 2 → K) i)) = ![σ a, 1] by
      funext i
      fin_cases i <;> simp]

end Coordinates

theorem exists_semilinear_on_hypX (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {ψ : Equiv.Perm (hypIsotropicLines h 2 ε)} (hψ : ψ ∈ lineNormalizer h 2 ε)
    (hX : ∀ L : hypIsotropicLines h 2 ε, ((ψ L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε ↔
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε))
    (hY : ∀ L : hypIsotropicLines h 2 ε, ((ψ L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε ↔
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε)) :
    ∃ (A₀ : GL (Fin 2) K) (σ : K ≃+* K), ∀ L : hypIsotropicLines h 2 ε,
      (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε →
      (ψ L : Submodule K (HypIndex 2 ε → K)) =
        (⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀), σ⟩ : SemiGL (HypIndex 2 ε) K) •
          (L : Submodule K (HypIndex 2 ε → K)) := by
  have := h.finite
  have hcomm : ∀ {ψ' : Equiv.Perm (hypIsotropicLines h 2 ε)}, ψ' ∈ lineNormalizer h 2 ε →
      (∀ L : hypIsotropicLines h 2 ε, ((ψ' L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε ↔
        (L : Submodule K (HypIndex 2 ε → K)) ≤ hypX K 2 ε)) →
      (∀ L : hypIsotropicLines h 2 ε, ((ψ' L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε ↔
        (L : Submodule K (HypIndex 2 ε → K)) ≤ hypY K 2 ε)) →
      ∀ A : SpecialLinearGroup (Fin 2) K, ∃ B : SpecialLinearGroup (Fin 2) K,
        ψ' * hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε A)) =
          hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε B)) * ψ' := by
    intro ψ' hψ' hX' hY' A
    obtain ⟨B, hB⟩ := conj_mem_leviPointGroup hε hψ' hX' hY' (x := hypProjLineAction h 2 ε
      (hypProj h 2 ε (leviSU h ε A))) ⟨A, rfl⟩
    refine ⟨B, ?_⟩
    change hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε B)) = _ at hB
    rw [hB, inv_mul_cancel_right]
  have h1 : ∀ A : SpecialLinearGroup (Fin 2) K, ∃ B : SpecialLinearGroup (Fin 2) K,
      ∀ U, xPtPerm hX (A • U) = B • xPtPerm hX U := fun A => by
    obtain ⟨B, hB⟩ := hcomm hψ hX hY A
    exact ⟨B, xPtPerm_smul hX hB⟩
  have h2 : ∀ B : SpecialLinearGroup (Fin 2) K, ∃ A : SpecialLinearGroup (Fin 2) K,
      ∀ U, xPtPerm hX (A • U) = B • xPtPerm hX U := fun B => by
    obtain ⟨A, hA⟩ := hcomm (inv_mem hψ) (inv_le_iff_of_forall hX) (inv_le_iff_of_forall hY) B
    refine ⟨A, xPtPerm_smul hX ?_⟩
    calc ψ * hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε A)) =
        ψ * (hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε A)) * ψ⁻¹) * ψ := by group
      _ = ψ * (ψ⁻¹ * hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε B))) * ψ := by rw [hA]
      _ = hypProjLineAction h 2 ε (hypProj h 2 ε (leviSU h ε B)) * ψ := by group
  obtain ⟨d, σ, hd⟩ := coordinateNormalizer_decomposition K _ (permCongr_mem_normalizer h1 h2)
  obtain ⟨A₀, hA₀⟩ : (d : Equiv.Perm (Omega K)) ∈ (coordinateGLAction K).range := by
    rw [coordinateGLAction_range]
    exact d.2
  refine ⟨A₀, σ, fun L hL => ?_⟩
  obtain ⟨U, rfl⟩ := exists_xPt_eq h L hL
  rw [← xPt_xPtPerm hX, coe_xPt, coe_xPt, levi_smul_map_hypXEmb]
  congr 1
  have hπU : xPtPerm hX U = coordinateEquiv K (coordinateGLAction K A₀
      (fieldExtension K σ ((coordinateEquiv K).symm U))) := by
    have := congrArg (fun g : Equiv.Perm (Omega K) => g ((coordinateEquiv K).symm U)) hd
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
      Equiv.Perm.mul_apply, ← hA₀] at this
    rw [← this, Equiv.apply_symm_apply]
  rw [hπU, (linear_two_projective_identification K).2.2.2.2.2.1 A₀, submodule_pgl_smul,
    submodule_coordinateEquiv_fieldExtension, Equiv.apply_symm_apply]

section Isometry

theorem exists_isometry_of_opposite (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {W W' : Submodule K (HypIndex r ε → K)}
    (hW : ∀ v ∈ W, ∀ w ∈ W, hypForm h r ε v w = 0)
    (hW' : ∀ v ∈ W', ∀ w ∈ W', hypForm h r ε v w = 0)
    (hWd : finrank K W = r) (hW'd : finrank K W' = r) (hWW' : W ⊓ W' = ⊥) :
    ∃ g : (HypIndex r ε → K) ≃ₗ[K] (HypIndex r ε → K),
      (∀ u v, hypForm h r ε (g u) (g v) = hypForm h r ε u v) ∧
      (hypX K r ε).map (g : (HypIndex r ε → K) →ₗ[K] (HypIndex r ε → K)) = W ∧
      (hypY K r ε).map (g : (HypIndex r ε → K) →ₗ[K] (HypIndex r ε → K)) = W' := by
  obtain ⟨w, hw, hwX, hwY⟩ := exists_wittBasis_of_opposite h ε hε r (hypForm_isSymm h)
    (hypForm_separatingLeft h) finrank_hypIndex_fun W W' hW hW' hWd hW'd hWW'
  set g := (Pi.basisFun K (HypIndex r ε)).equiv w (Equiv.refl _) with hg
  have hgb : ∀ x, g (Pi.basisFun K (HypIndex r ε) x) = w x := fun x => by
    rw [hg, Module.Basis.equiv_apply, Equiv.refl_apply]
  refine ⟨g, isometry_basis_equiv (Pi.basisFun K (HypIndex r ε)) w fun x y => by
    rw [hw, Pi.basisFun_apply, Pi.basisFun_apply, gramForm_single], ?_, ?_⟩
  · rw [hypX_eq_span, Submodule.map_span, ← hwX, Set.image_image]
    congr 1
    exact Set.image_congr fun x _ => hgb x
  · rw [hypY_eq_span, Submodule.map_span, ← hwY, Set.image_image]
    congr 1
    exact Set.image_congr fun x _ => hgb x

theorem isometry_mem_semilinearSimilitudes (h : UnitaryFieldData p f K)
    {g : (HypIndex r ε → K) ≃ₗ[K] (HypIndex r ε → K)}
    (hg : ∀ u v, hypForm h r ε (g u) (g v) = hypForm h r ε u v) :
    (⟨glOfLinearEquiv g, 1⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε :=
  ⟨1, one_ne_zero, map_one _, by
    rw [one_smul]
    exact (gramForm_isometry_iff h _ _).mp fun u v => by
      rw [glOfLinearEquiv_mulVec, glOfLinearEquiv_mulVec]
      exact hg u v⟩

theorem isometry_smul (g : (HypIndex r ε → K) ≃ₗ[K] (HypIndex r ε → K))
    (A : Submodule K (HypIndex r ε → K)) :
    (⟨glOfLinearEquiv g, 1⟩ : SemiGL (HypIndex r ε) K) • A =
      A.map (g : (HypIndex r ε → K) →ₗ[K] (HypIndex r ε → K)) := by
  rw [semiGL_smul_eq_map]
  ext v
  simp only [Submodule.mem_map]
  refine exists_congr fun u => and_congr_right fun _ => ?_
  rw [semiLin_apply]
  rw [show ((glOfLinearEquiv g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
    (fun a => (1 : K ≃+* K) (u a)) = g u from glOfLinearEquiv_mulVec g u]
  rfl

theorem coe_semilinearPointAction {h : UnitaryFieldData p f K} (x : semilinearSimilitudes h r ε)
    (L : hypIsotropicLines h r ε) :
    ((semilinearPointAction h r ε x L : hypIsotropicLines h r ε) :
      Submodule K (HypIndex r ε → K)) =
      (x : SemiGL (HypIndex r ε) K) • (L : Submodule K (HypIndex r ε → K)) :=
  rfl

theorem semiGL_smul_le_smul_iff (x : SemiGL (HypIndex r ε) K)
    (A B : Submodule K (HypIndex r ε → K)) : x • A ≤ x • B ↔ A ≤ B := by
  have hmono : ∀ (y : SemiGL (HypIndex r ε) K) {A B : Submodule K (HypIndex r ε → K)},
      A ≤ B → y • A ≤ y • B := fun y A B hAB => by
    rw [semiGL_smul_eq_map, semiGL_smul_eq_map]
    exact Submodule.map_mono hAB
  refine ⟨fun hAB => ?_, hmono x⟩
  have := hmono x⁻¹ hAB
  rwa [inv_smul_smul, inv_smul_smul] at this

theorem semiLin_injective (x : SemiGL (HypIndex r ε) K) : Function.Injective (semiLin x) := by
  intro v v' hv
  rw [semiLin_apply, semiLin_apply] at hv
  have h1 := congrArg (fun u => ((x.left⁻¹ : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ u) hv
  simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h1
  funext a
  exact x.right.injective (congrFun h1 a)

end Isometry

theorem unitary_rank_two_maximal_restriction (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {W W' : Submodule K (HypIndex 2 ε → K)}
    (hW : ∀ v ∈ W, ∀ w ∈ W, hypForm h 2 ε v w = 0)
    (hW' : ∀ v ∈ W', ∀ w ∈ W', hypForm h 2 ε v w = 0)
    (hWd : finrank K W = 2) (hW'd : finrank K W' = 2) (hWW' : W ⊓ W' = ⊥)
    {φ : Equiv.Perm (hypIsotropicLines h 2 ε)} (hφ : φ ∈ lineNormalizer h 2 ε)
    (hφW : ∀ L : hypIsotropicLines h 2 ε, ((φ L : Submodule K (HypIndex 2 ε → K)) ≤ W ↔
      (L : Submodule K (HypIndex 2 ε → K)) ≤ W))
    (hφW' : ∀ L : hypIsotropicLines h 2 ε, ((φ L : Submodule K (HypIndex 2 ε → K)) ≤ W' ↔
      (L : Submodule K (HypIndex 2 ε → K)) ≤ W')) :
    ∃ (σ : K ≃+* K) (T : W →ₛₗ[(σ : K →+* K)] W), Function.Bijective T ∧
      ∀ (w : W) (L : hypIsotropicLines h 2 ε),
        (L : Submodule K (HypIndex 2 ε → K)) = K ∙ (w : HypIndex 2 ε → K) →
        (φ L : Submodule K (HypIndex 2 ε → K)) = K ∙ (T w : HypIndex 2 ε → K) := by
  obtain ⟨g, hgiso, hgX, hgY⟩ := exists_isometry_of_opposite h hε hW hW' hWd hW'd hWW'
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : semilinearSimilitudes h 2 ε,
      (x₀ : SemiGL (HypIndex 2 ε) K) = ⟨glOfLinearEquiv g, 1⟩ :=
    ⟨⟨_, isometry_mem_semilinearSimilitudes h hgiso⟩, rfl⟩
  have hx₀A : ∀ A : Submodule K (HypIndex 2 ε → K), (x₀ : SemiGL (HypIndex 2 ε) K) • A =
      A.map (g : (HypIndex 2 ε → K) →ₗ[K] (HypIndex 2 ε → K)) := fun A => by
    rw [hx₀]
    exact isometry_smul g A
  have hx₀A' : ∀ A : Submodule K (HypIndex 2 ε → K),
      ((x₀⁻¹ : semilinearSimilitudes h 2 ε) : SemiGL (HypIndex 2 ε) K) • A =
        A.map (g.symm : (HypIndex 2 ε → K) →ₗ[K] (HypIndex 2 ε → K)) := fun A => by
    rw [InvMemClass.coe_inv, inv_smul_eq_iff, hx₀A]
    ext v
    simp
  have hx₀X : (x₀ : SemiGL (HypIndex 2 ε) K) • hypX K 2 ε = W := by rw [hx₀A, hgX]
  have hx₀Y : (x₀ : SemiGL (HypIndex 2 ε) K) • hypY K 2 ε = W' := by rw [hx₀A, hgY]
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : Equiv.Perm (hypIsotropicLines h 2 ε),
      η₀ = semilinearPointAction h 2 ε x₀ := ⟨_, rfl⟩
  have hη₀N : η₀ ∈ lineNormalizer h 2 ε := by
    rw [hη₀]
    exact semilinearPointGroup_le_normalizer ⟨x₀, rfl⟩
  have hη₀L : ∀ L : hypIsotropicLines h 2 ε, (η₀ L : Submodule K (HypIndex 2 ε → K)) =
      (x₀ : SemiGL (HypIndex 2 ε) K) • (L : Submodule K (HypIndex 2 ε → K)) := fun L => by
    rw [hη₀]
    rfl
  have hη₀L' : ∀ L : hypIsotropicLines h 2 ε, (η₀⁻¹ L : Submodule K (HypIndex 2 ε → K)) =
      ((x₀⁻¹ : semilinearSimilitudes h 2 ε) : SemiGL (HypIndex 2 ε) K) •
        (L : Submodule K (HypIndex 2 ε → K)) := fun L => by
    rw [hη₀, ← map_inv]
    rfl
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Equiv.Perm (hypIsotropicLines h 2 ε), ψ = η₀⁻¹ * φ * η₀ :=
    ⟨_, rfl⟩
  have hψN : ψ ∈ lineNormalizer h 2 ε := by
    rw [hψdef]
    exact mul_mem (mul_mem (inv_mem hη₀N) hφ) hη₀N
  have hψL : ∀ L : hypIsotropicLines h 2 ε, (ψ L : Submodule K (HypIndex 2 ε → K)) =
      ((x₀⁻¹ : semilinearSimilitudes h 2 ε) : SemiGL (HypIndex 2 ε) K) •
        (φ (η₀ L) : Submodule K (HypIndex 2 ε → K)) := fun L => by
    rw [hψdef, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hη₀L']
  have hpts : ∀ {Z W₁ : Submodule K (HypIndex 2 ε → K)},
      (x₀ : SemiGL (HypIndex 2 ε) K) • Z = W₁ →
      (∀ L : hypIsotropicLines h 2 ε, ((φ L : Submodule K (HypIndex 2 ε → K)) ≤ W₁ ↔
        (L : Submodule K (HypIndex 2 ε → K)) ≤ W₁)) →
      ∀ L : hypIsotropicLines h 2 ε, ((ψ L : Submodule K (HypIndex 2 ε → K)) ≤ Z ↔
        (L : Submodule K (HypIndex 2 ε → K)) ≤ Z) := by
    intro Z W₁ hZ hφZ L
    rw [hψL, ← semiGL_smul_le_smul_iff (x₀ : SemiGL (HypIndex 2 ε) K), InvMemClass.coe_inv,
      smul_inv_smul, hZ, hφZ, ← hZ, hη₀L, semiGL_smul_le_smul_iff]
  obtain ⟨A₀, σ, hA₀⟩ := exists_semilinear_on_hypX h hε hψN (hpts hx₀X hφW) (hpts hx₀Y hφW')
  set x₁ : SemiGL (HypIndex 2 ε) K := ⟨glOfLinearEquiv (hypLeviEquiv (ε := ε) h A₀), σ⟩ with hx₁
  have hsymmW : ∀ v ∈ W, g.symm v ∈ hypX K 2 ε := fun v hv => by
    rw [← hgX] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hu
  have hx₁X : ∀ u : Fin 2 → K, semiLin x₁ (hypXEmb 2 ε u) =
      hypXEmb 2 ε ((A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (u i)) :=
    semiLin_levi_hypXEmb h A₀ σ
  have hmem : ∀ c : W, g (semiLin x₁ (g.symm c)) ∈ W := fun c => by
    obtain ⟨u, hu⟩ := hsymmW c c.2
    rw [← hu, hx₁X, ← hgX]
    exact Submodule.mem_map_of_mem ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : W →ₛₗ[(σ : K →+* K)] W,
      ∀ c : W, (T c : HypIndex 2 ε → K) = g (semiLin x₁ (g.symm c)) :=
    ⟨(((g : (HypIndex 2 ε → K) →ₗ[K] (HypIndex 2 ε → K)).comp
      ((semiLin x₁ : (HypIndex 2 ε → K) →ₛₗ[(σ : K →+* K)] (HypIndex 2 ε → K)).comp
        (g.symm : (HypIndex 2 ε → K) →ₗ[K] (HypIndex 2 ε → K)))).domRestrict W).codRestrict W
          hmem, fun c => rfl⟩
  refine ⟨σ, T, ⟨fun c c' hcc' => ?_, fun c => ?_⟩, fun w L hL => ?_⟩
  · have := congrArg Subtype.val hcc'
    rw [hT, hT] at this
    exact Subtype.ext (g.symm.injective (semiLin_injective x₁ (g.injective this)))
  · obtain ⟨a, ha⟩ := hsymmW c c.2
    set a' : Fin 2 → K := fun i => σ.symm ((((A₀⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ a) i) with ha'
    have hpre : semiLin x₁ (hypXEmb 2 ε a') = g.symm c := by
      rw [hx₁X, ← ha]
      congr 1
      simp only [ha', RingEquiv.apply_symm_apply]
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hgW : g (hypXEmb 2 ε a') ∈ W := by
      rw [← hgX]
      exact Submodule.mem_map_of_mem ⟨_, rfl⟩
    refine ⟨⟨_, hgW⟩, Subtype.ext ?_⟩
    rw [hT, LinearEquiv.symm_apply_apply, hpre, LinearEquiv.apply_symm_apply]
  ·
    have hφL : φ L = η₀ (ψ (η₀⁻¹ L)) := by
      rw [hψdef]
      change φ L = η₀ (η₀⁻¹ (φ (η₀ (η₀⁻¹ L))))
      rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hM : ((η₀⁻¹ L : hypIsotropicLines h 2 ε) : Submodule K (HypIndex 2 ε → K)) =
        K ∙ g.symm w := by
      rw [hη₀L', hx₀A', hL, Submodule.map_span, Set.image_singleton]
      rfl
    have hMX : ((η₀⁻¹ L : hypIsotropicLines h 2 ε) : Submodule K (HypIndex 2 ε → K)) ≤
        hypX K 2 ε := by
      rw [hM, span_singleton_le_iff_mem]
      exact hsymmW w w.2
    rw [hφL, hη₀L, hA₀ _ hMX, hM, semiGL_smul_eq_map x₁, Submodule.map_span,
      Set.image_singleton, hx₀A, Submodule.map_span, Set.image_singleton, hT]
    rfl

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
