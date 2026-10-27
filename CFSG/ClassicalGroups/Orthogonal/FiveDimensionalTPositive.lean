module

public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroProjective
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut
public import CFSG.GroupTheory.SubgroupOfLattice
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction

public noncomputable section

open Matrix QuadraticMap
open scoped commutatorElement
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonal

namespace CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

abbrev tOp (F : FrameData Q) : Module.End K V := (F.t : V →ₗ[K] V)

abbrev Wplus (F : FrameData Q) : Submodule K V := tOp F |>.eigenspace 1

abbrev Uminus (F : FrameData Q) : Submodule K V := tOp F |>.eigenspace (-1)

theorem tOp_mul_self (F : FrameData Q) :
    tOp F * tOp F = (1 : K) ^ 2 • (1 : Module.End K V) := by
  rw [one_pow, one_smul]
  exact congrArg (fun g : V ≃ₗ[K] V => (g : V →ₗ[K] V)) F.t_mul_self

theorem tOp_selfAdjoint (F : FrameData Q) (x y : V) :
    Q.polarBilin (tOp F x) y = Q.polarBilin x (tOp F y) := by
  have ht2 : ∀ v, tOp F (tOp F v) = v := by
    intro v
    have h := congrArg (fun g : V ≃ₗ[K] V => (g : V →ₗ[K] V)) F.t_mul_self
    exact LinearMap.congr_fun h v
  calc Q.polarBilin (tOp F x) y
      = Q.polarBilin (tOp F x) (tOp F (tOp F y)) := by rw [ht2]
    _ = Q.polarBilin x (tOp F y) :=
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem F.t_mem x (tOp F y)

theorem Wplus_nondegenerate (F : FrameData Q) :
    (Q.comp (Wplus F).subtype).Nondegenerate := by
  let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
  have hsym : LinearMap.BilinForm.IsSymm (polarBilin Q) :=
    LinearMap.BilinForm.isSymm_iff.mpr (CFSG.RankThree.Classical.isSymm_polarBilin Q)
  have h := (positive_adjoint_eigenspaces_nondegenerate (Q.polarBilin) F.nondeg hsym
    (tOp F) 1 one_ne_zero F.two_ne_zero (tOp_mul_self F) (tOp_selfAdjoint F)).1
  exact QuadraticMap.nondegenerate_polar_iff.mp h

theorem Wplus_polar_nondegenerate (F : FrameData Q) :
    (Q.comp (Wplus F).subtype).polarBilin.Nondegenerate := by
  let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
  exact QuadraticMap.nondegenerate_polar_iff.mpr (Wplus_nondegenerate F)

theorem isCompl_Wplus (F : FrameData Q) :
    IsCompl (Wplus F) (orthPerp Q (Wplus F)) :=
  isCompl_orthPerp (Q := Q) (R := Wplus F) (Wplus_polar_nondegenerate F)

theorem Uminus_nondegenerate (F : FrameData Q) :
    (Q.comp (Uminus F).subtype).Nondegenerate := by
  let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
  have hsym : LinearMap.BilinForm.IsSymm (polarBilin Q) :=
    LinearMap.BilinForm.isSymm_iff.mpr (CFSG.RankThree.Classical.isSymm_polarBilin Q)
  have h := (positive_adjoint_eigenspaces_nondegenerate (Q.polarBilin) F.nondeg hsym
    (tOp F) 1 one_ne_zero F.two_ne_zero (tOp_mul_self F) (tOp_selfAdjoint F)).2
  exact QuadraticMap.nondegenerate_polar_iff.mp h

theorem Uminus_polar_nondegenerate (F : FrameData Q) :
    (Q.comp (Uminus F).subtype).polarBilin.Nondegenerate := by
  let _ : Invertible (2 : K) := invertibleOfNonzero F.two_ne_zero
  exact QuadraticMap.nondegenerate_polar_iff.mpr (Uminus_nondegenerate F)


theorem finrank_Wplus (F : FrameData Q) : Module.finrank K (Wplus F) = 3 := by
  let g : Fin 3 → Fin 5 := ![2, 3, 4]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [g] at hij ⊢
  have hli : LinearIndependent K (fun i : Fin 3 => F.e (g i)) :=
    F.e.linearIndependent.comp g hg
  let S : Submodule K V := Submodule.span K (Set.range (fun i : Fin 3 => F.e (g i)))
  have hSle : S ≤ Wplus F := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    fin_cases i
    · change F.e 2 ∈ Module.End.eigenspace (tOp F) 1
      rw [Module.End.mem_eigenspace_iff]; simp [tOp, F.t_e]
    · change F.e 3 ∈ Module.End.eigenspace (tOp F) 1
      rw [Module.End.mem_eigenspace_iff]; simp [tOp, F.t_e]
    · change F.e 4 ∈ Module.End.eigenspace (tOp F) 1
      rw [Module.End.mem_eigenspace_iff]; simp [tOp, F.t_e]
  have hS3 : Module.finrank K S = 3 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hW3 : 3 ≤ Module.finrank K (Wplus F) := by
    rw [← hS3]
    exact Submodule.finrank_mono hSle
  let h : Fin 2 → Fin 5 := ![0, 1]
  have hh : Function.Injective h := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [h] at hij ⊢
  have hli2 : LinearIndependent K (fun i : Fin 2 => F.e (h i)) :=
    F.e.linearIndependent.comp h hh
  let T : Submodule K V := Submodule.span K (Set.range (fun i : Fin 2 => F.e (h i)))
  have hTle : T ≤ Uminus F := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    fin_cases i
    · change F.e 0 ∈ Module.End.eigenspace (tOp F) (-1)
      rw [Module.End.mem_eigenspace_iff]; simp [tOp, F.t_e]
    · change F.e 1 ∈ Module.End.eigenspace (tOp F) (-1)
      rw [Module.End.mem_eigenspace_iff]; simp [tOp, F.t_e]
  have hT2 : Module.finrank K T = 2 := by
    rw [finrank_span_eq_card hli2, Fintype.card_fin]
  have hU2 : 2 ≤ Module.finrank K (Uminus F) := by
    rw [← hT2]
    exact Submodule.finrank_mono hTle
  have hcompl := CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaces_isCompl
    (T := tOp F) 1 one_ne_zero F.two_ne_zero (tOp_mul_self F)
  have hsum : Module.finrank K (Wplus F) + Module.finrank K (Uminus F) = 5 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl,
      Module.finrank_eq_card_basis F.e]
    simp
  omega

theorem finrank_Uminus (F : FrameData Q) : Module.finrank K (Uminus F) = 2 := by
  have hcompl := CFSG.ComponentClassification.CatalogueBProjectiveInvolution.squareScalar_eigenspaces_isCompl
    (T := tOp F) 1 one_ne_zero F.two_ne_zero (tOp_mul_self F)
  have h := Submodule.finrank_add_eq_of_isCompl hcompl
  have hV : Module.finrank K V = 5 := by
    rw [Module.finrank_eq_card_basis F.e]
    simp
  change Module.finrank K (Wplus F) + Module.finrank K (Uminus F) =
    Module.finrank K V at h
  rw [finrank_Wplus, hV] at h
  omega

theorem Uminus_eq_orthPerp (F : FrameData Q) :
    Uminus F = orthPerp Q (Wplus F) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro u hu
    rw [mem_orthPerp]
    intro w hw
    have horth :=
      CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare.opposite_eigenspaces_orthogonal
        (Q.polarBilin) (tOp F) 1 one_ne_zero F.two_ne_zero (tOp_selfAdjoint F) w u hw hu
    simpa [QuadraticMap.polarBilin_apply_apply] using horth
  · rw [finrank_Uminus, show orthPerp Q (Wplus F) =
        LinearMap.BilinForm.orthogonal (Q.polarBilin) (Wplus F) from rfl,
      LinearMap.BilinForm.finrank_orthogonal F.nondeg, finrank_Wplus]
    have hV : Module.finrank K V = 5 := by
      rw [Module.finrank_eq_card_basis F.e]
      simp
    rw [hV]

abbrev tPositiveDerived (F : FrameData Q) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  (supportedOrthDerived Q (Wplus F)).comap
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype

@[expose] noncomputable def tPositiveEmbedding (F : FrameData Q) :
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype) →*
      TauCeti.QuadraticMap.orthogonalGroup Q :=
  (extendHom (isCompl_Wplus F)).codRestrict (TauCeti.QuadraticMap.orthogonalGroup Q)
    (fun g => extendHom_mem (isCompl_Wplus F) g)

theorem tPositiveEmbedding_injective (F : FrameData Q) :
    Function.Injective (tPositiveEmbedding F) := by
  intro g h hgh
  apply extendHom_injective (isCompl_Wplus F)
  have := congrArg (fun x : TauCeti.QuadraticMap.orthogonalGroup Q =>
    (x : V ≃ₗ[K] V)) hgh
  simpa [tPositiveEmbedding] using this

theorem tPositiveDerived_eq_map_commutator (F : FrameData Q) :
    tPositiveDerived F =
      (commutator (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (Wplus F).subtype))).map (tPositiveEmbedding F) := by
  rw [tPositiveDerived, supportedOrthDerived_eq_map (isCompl_Wplus F),
    orthDerived_eq_map_commutator]
  rw [Subgroup.map_map]
  change ((commutator (TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (Wplus F).subtype))).map (extendHom (isCompl_Wplus F))).comap
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype =
    (commutator (TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (Wplus F).subtype))).map (tPositiveEmbedding F)
  rw [show tPositiveEmbedding F =
      (extendHom (isCompl_Wplus F)).codRestrict
        (TauCeti.QuadraticMap.orthogonalGroup Q)
        (fun g => extendHom_mem (isCompl_Wplus F) g) from rfl]
  rw [CFSG.map_codRestrict_eq_subgroupOf]
  rw [Subgroup.comap_subtype]

theorem tPositiveDerived_le_commutator (F : FrameData Q) :
    tPositiveDerived F ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  rw [tPositiveDerived_eq_map_commutator, map_commutator_eq, commutator_def]
  exact Subgroup.commutator_mono le_top le_top

abbrev C0 (F : FrameData Q) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Subgroup.centralizer ({F.tO} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))

abbrev CSO (F : FrameData Q) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Q.specialOrthogonalWithin ⊓ C0 F

@[expose] def C0toOperator (F : FrameData Q) :
    C0 F →* orthogonalOperatorCentralizer Q (tOp F) where
  toFun g :=
    ⟨g.val, by
      intro x
      have h := congrArg (fun s : TauCeti.QuadraticMap.orthogonalGroup Q =>
        (s : V ≃ₗ[K] V)) (Subgroup.mem_centralizer_singleton_iff.mp g.property)
      have hx := LinearEquiv.congr_fun h x
      simpa [LinearEquiv.mul_apply, FrameData.tO, tOp, Subgroup.coe_mk] using hx⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def operatorToC0 (F : FrameData Q) :
    orthogonalOperatorCentralizer Q (tOp F) →* C0 F where
  toFun g :=
    ⟨g.val, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      have h := g.property x
      simpa [LinearEquiv.mul_apply, FrameData.tO, tOp, Subgroup.coe_mk] using h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def C0toOperatorEquiv (F : FrameData Q) :
    C0 F ≃* orthogonalOperatorCentralizer Q (tOp F) where
  toFun := C0toOperator F
  invFun := operatorToC0 F
  left_inv := by intro g; apply Subtype.ext; rfl
  right_inv := by intro g; apply Subtype.ext; rfl
  map_mul' := (C0toOperator F).map_mul

@[expose] def resPlus (F : FrameData Q) :
    C0 F →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype) :=
  (orthogonalCentralizerRestriction Q (tOp F) 1).comp (C0toOperatorEquiv F).toMonoidHom

theorem resPlus_apply (F : FrameData Q) (g : C0 F) (w : Wplus F) :
    ((resPlus F g).val w).val = (g.val : V ≃ₗ[K] V) w.val := rfl

theorem C0_preserves_Wplus (F : FrameData Q) (g : C0 F) {w : V} (hw : w ∈ Wplus F) :
    (g.val : V ≃ₗ[K] V) w ∈ Wplus F := by
  exact CFSG.ComponentClassification.CatalogueBProjectiveInvolution.operatorCentralizer_preserves_eigenspace (tOp F) 1
    ⟨(g.val : V ≃ₗ[K] V), (C0toOperator F g).property⟩ hw

theorem C0_preserves_Uminus (F : FrameData Q) (g : C0 F) {w : V} (hw : w ∈ Uminus F) :
    (g.val : V ≃ₗ[K] V) w ∈ Uminus F := by
  exact CFSG.ComponentClassification.CatalogueBProjectiveInvolution.operatorCentralizer_preserves_eigenspace (tOp F) (-1)
    ⟨(g.val : V ≃ₗ[K] V), (C0toOperator F g).property⟩ hw

theorem C0_preserves_orthPerp (F : FrameData Q) (g : C0 F) {w : V}
    (hw : w ∈ orthPerp Q (Wplus F)) : (g.val : V ≃ₗ[K] V) w ∈ orthPerp Q (Wplus F) := by
  rw [← Uminus_eq_orthPerp] at hw ⊢
  exact C0_preserves_Uminus F g hw

theorem tPositiveEmbedding_mem_C0 (F : FrameData Q) :
    ∀ g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype),
      tPositiveEmbedding F g ∈ C0 F := by
  intro g
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (extendHom (isCompl_Wplus F) g) (F.t v) =
    F.t ((extendHom (isCompl_Wplus F) g) v)
  have hP : ∀ w ∈ orthPerp Q (Wplus F), F.t w ∈ orthPerp Q (Wplus F) := by
    intro w hw
    rw [mem_orthPerp] at hw ⊢
    intro u hu
    have htu : F.t u = u := by
      have hu_mem : u ∈ Wplus F := hu
      rw [Module.End.mem_eigenspace_iff] at hu_mem
      simpa [FrameData.t_e] using hu_mem
    calc polar Q u (F.t w) = polar Q (F.t u) (F.t w) := by rw [htu]
      _ = polar Q u w :=
        CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem F.t_mem u w
      _ = 0 := hw u hu
  obtain ⟨⟨u, w⟩, huw, _⟩ :=
    Submodule.existsUnique_add_of_isCompl_prod (isCompl_Wplus F) v
  rw [← huw]
  have hu : F.t (u : V) = u := by
    have hu_mem : (u : V) ∈ Wplus F := u.2
    rw [Module.End.mem_eigenspace_iff] at hu_mem
    simpa [FrameData.t_e] using hu_mem
  have hgu : F.t (((g : Wplus F ≃ₗ[K] Wplus F) u : Wplus F) : V) =
      (((g : Wplus F ≃ₗ[K] Wplus F) u : Wplus F) : V) := by
    have hmem : (((g : Wplus F ≃ₗ[K] Wplus F) u : Wplus F) : V) ∈ Wplus F :=
      ((g : Wplus F ≃ₗ[K] Wplus F) u).2
    rw [Module.End.mem_eigenspace_iff] at hmem
    simpa [FrameData.t_e] using hmem
  have htw : F.t (w : V) ∈ orthPerp Q (Wplus F) := hP w w.2
  have hL : extendHom (isCompl_Wplus F) g (F.t ((u : V) + w)) =
      (((g : Wplus F ≃ₗ[K] Wplus F) u : Wplus F) : V) + F.t w := by
    rw [map_add, hu]
    have h := extendHom_apply (isCompl_Wplus F) g u ⟨F.t w, htw⟩
    simpa using h
  have hR : F.t (extendHom (isCompl_Wplus F) g ((u : V) + w)) =
      (((g : Wplus F ≃ₗ[K] Wplus F) u : Wplus F) : V) + F.t w := by
    have h := extendHom_apply (isCompl_Wplus F) g u w
    rw [h, map_add, hgu]
  rw [hL, hR]

theorem resPlus_tPositiveEmbedding (F : FrameData Q) :
    ∀ g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype),
      resPlus F ⟨tPositiveEmbedding F g, tPositiveEmbedding_mem_C0 F g⟩ = g := by
  intro g
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  rw [resPlus_apply]
  change (extendHom (isCompl_Wplus F) g) (w : V) = ((g : Wplus F ≃ₗ[K] Wplus F) w : V)
  exact extendHom_apply_mem (isCompl_Wplus F) g w


theorem resPlus_surjective (F : FrameData Q) :
    Function.Surjective (resPlus F) := by
  intro h
  let e := positiveOrthogonalCentralizerEquiv Q (tOp F) 1 one_ne_zero F.two_ne_zero
    (tOp_mul_self F) (tOp_selfAdjoint F)
  refine ⟨(C0toOperatorEquiv F).symm (e.symm (h, 1)), ?_⟩
  change (orthogonalCentralizerRestriction Q (tOp F) 1)
    ((C0toOperatorEquiv F) ((C0toOperatorEquiv F).symm (e.symm (h, 1)))) = h
  rw [MulEquiv.apply_symm_apply]
  have h2 := congrArg Prod.fst (MulEquiv.apply_symm_apply e (h, 1))
  change (orthogonalCentralizerRestriction Q (tOp F) 1) (e.symm (h, 1)) = h
  simpa [e, positiveOrthogonalCentralizerEquiv, splitOrthogonalRestriction,
    orthogonalCentralizerRestriction] using h2

@[expose] def detC0 (F : FrameData Q) : C0 F →* Kˣ :=
  LinearEquiv.det.comp ((TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp (C0 F).subtype)

theorem detC0_apply (F : FrameData Q) (g : C0 F) :
    detC0 F g = LinearEquiv.det (g.val : V ≃ₗ[K] V) := rfl

theorem detC0_eq (F : FrameData Q) (g : C0 F) :
    detC0 F g =
      LinearEquiv.det ((positiveOrthogonalCentralizerEquiv Q (tOp F) 1 one_ne_zero
        F.two_ne_zero (tOp_mul_self F) (tOp_selfAdjoint F)
        (C0toOperatorEquiv F g)).1.val) *
      LinearEquiv.det ((positiveOrthogonalCentralizerEquiv Q (tOp F) 1 one_ne_zero
        F.two_ne_zero (tOp_mul_self F) (tOp_selfAdjoint F)
        (C0toOperatorEquiv F g)).2.val) := by
  let e := positiveOrthogonalCentralizerEquiv Q (tOp F) 1 one_ne_zero F.two_ne_zero
    (tOp_mul_self F) (tOp_selfAdjoint F)
  have h := det_positiveOrthogonalExtension (Q := Q) (T := tOp F) (b := 1)
    one_ne_zero F.two_ne_zero (tOp_mul_self F) (tOp_selfAdjoint F)
    (e (C0toOperatorEquiv F g))
  have he : positiveOrthogonalExtension Q (tOp F) 1 one_ne_zero F.two_ne_zero
      (tOp_mul_self F) (tOp_selfAdjoint F) (e (C0toOperatorEquiv F g)) =
      C0toOperatorEquiv F g := by
    change e.symm (e (C0toOperatorEquiv F g)) = C0toOperatorEquiv F g
    exact MulEquiv.symm_apply_apply e (C0toOperatorEquiv F g)
  rw [he] at h
  change LinearEquiv.det (((C0toOperator F) g).val.val) =
    LinearEquiv.det ((e ((C0toOperator F) g)).1.val) *
      LinearEquiv.det ((e ((C0toOperator F) g)).2.val)
  exact h

theorem detC0_sq (F : FrameData Q) (g : C0 F) : detC0 F g ^ 2 = 1 := by
  let e := positiveOrthogonalCentralizerEquiv Q (tOp F) 1 one_ne_zero F.two_ne_zero
    (tOp_mul_self F) (tOp_selfAdjoint F)
  let g1 := (e (C0toOperatorEquiv F g)).1
  let g2 := (e (C0toOperatorEquiv F g)).2
  have h1 : LinearEquiv.det (g1 : Wplus F ≃ₗ[K] Wplus F) ^ 2 = 1 := by
    rw [← QuadraticMap.orthogonalDet_apply g1]
    exact TauCeti.QuadraticMap.orthogonalDet_sq (Wplus_polar_nondegenerate F).1 g1
  have h2 : LinearEquiv.det (g2 : Uminus F ≃ₗ[K] Uminus F) ^ 2 = 1 := by
    rw [← QuadraticMap.orthogonalDet_apply g2]
    exact TauCeti.QuadraticMap.orthogonalDet_sq (Uminus_polar_nondegenerate F).1 g2
  rw [detC0_eq]
  change (LinearEquiv.det g1.val * LinearEquiv.det g2.val) ^ 2 = 1
  rw [mul_pow, h1, h2, one_mul]

theorem CSO_eq_map_ker (F : FrameData Q) :
    CSO F = (detC0 F).ker.map (C0 F).subtype := by
  ext g
  constructor
  · rintro ⟨hSO, hC0⟩
    refine ⟨⟨g, hC0⟩, ?_, rfl⟩
    change detC0 F ⟨g, hC0⟩ = 1
    exact QuadraticMap.mem_specialOrthogonalWithin_iff.mp hSO
  · rintro ⟨c, hc, rfl⟩
    change detC0 F c = 1 at hc
    exact ⟨QuadraticMap.mem_specialOrthogonalWithin_iff.mpr hc, c.property⟩


theorem tPositiveDerived_le_C0 (F : FrameData Q) :
    tPositiveDerived F ≤ C0 F := by
  rw [tPositiveDerived_eq_map_commutator]
  rintro x ⟨g, _hg, rfl⟩
  exact tPositiveEmbedding_mem_C0 F g

section TraceZeroAction

variable [Finite K] (hodd : Odd (Nat.card K))

structure TraceZeroModel (F : FrameData Q) (hodd : Odd (Nat.card K)) where
  d : Kˣ
  psi : Wplus F ≃ₗ[K] traceZeroSubmodule K
  equiv : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype) ≃*
    TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)
  hpsi : ∀ v : Wplus F,
    (Q.comp (Wplus F).subtype) v = (d : K) * traceZeroForm K (psi v)
  equiv_apply : ∀ g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype),
    (equiv g).val = (psi.symm.trans g.val).trans psi
  equiv_symm_apply : ∀ g : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K),
    (equiv.symm g).val = (psi.trans g.val).trans psi.symm

noncomputable def traceZeroModel (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    TraceZeroModel F hodd := by
  classical
  have h : Nonempty (TraceZeroModel F hodd) := by
    obtain ⟨d, psi, e, hpsi, he, hesymm⟩ :=
      CFSG.ComponentClassification.CatalogueBOrthogonalThreeSimilarity.exists_trace_zero_similarity_and_orthogonal_equiv
        (K := K) (V := Wplus F) hodd (Q := Q.comp (Wplus F).subtype)
        (Wplus_polar_nondegenerate F) (finrank_Wplus F)
    exact ⟨⟨d, psi, e, hpsi, he, hesymm⟩⟩
  exact Classical.choice h

@[expose] noncomputable def rho (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype) →*
      CFSG.GorensteinWalter.PGL2 K :=
  (MonoidHom.fst (CFSG.GorensteinWalter.PGL2 K) (rootsOfUnity 2 K)).comp
    (((CFSG.ComponentClassification.CatalogueBOrthogonal.traceZeroProjectiveEquiv
        (K := K) F.two_ne_zero).symm).toMonoidHom.comp
      (traceZeroModel F hodd).equiv.toMonoidHom)

theorem rho_surjective (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    Function.Surjective (rho F hodd) := by
  intro A
  let h : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) :=
    CFSG.ComponentClassification.CatalogueBOrthogonal.traceZeroProjectiveEquiv
      (K := K) F.two_ne_zero (A, 1)
  refine ⟨(traceZeroModel F hodd).equiv.symm h, ?_⟩
  change ((CFSG.ComponentClassification.CatalogueBOrthogonal.traceZeroProjectiveEquiv
      (K := K) F.two_ne_zero).symm
      ((traceZeroModel F hodd).equiv ((traceZeroModel F hodd).equiv.symm h))).1 = A
  rw [MulEquiv.apply_symm_apply]
  have hh : (CFSG.ComponentClassification.CatalogueBOrthogonal.traceZeroProjectiveEquiv
      (K := K) F.two_ne_zero).symm h = (A, 1) := by
    dsimp only [h]
    exact MulEquiv.symm_apply_apply _ _
  rw [hh]


private theorem traceZeroProjectiveEquiv_one_apply (F : FrameData Q)
    (ε : rootsOfUnity 2 K) (X : traceZeroSubmodule K) :
    ((CFSG.ComponentClassification.CatalogueBOrthogonal.traceZeroProjectiveEquiv
      (K := K) F.two_ne_zero (1, ε)).val X).val = (ε.val : K) • X.val := by
  have h1 : (1 : CFSG.GorensteinWalter.PGL2 K) =
      Matrix.ProjGenLinGroup.mk (1 : GL (Fin 2) K) := by
    rw [← map_one (Matrix.ProjGenLinGroup.mk)]
  rw [h1]
  have hv := CFSG.ComponentClassification.CatalogueBOrthogonal.traceZeroProjectiveEquiv_val
    (K := K) F.two_ne_zero (1 : GL (Fin 2) K) ε X
  simpa using hv


theorem rho_eq_one_iff (F : FrameData Q) (hodd : Odd (Nat.card K))
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype)) :
    rho F hodd g = 1 ↔ ∃ ε : K, ε ^ 2 = 1 ∧ ∀ w : Wplus F, g.val w = ε • w := by
  let e := (traceZeroModel F hodd).equiv
  let psi := (traceZeroModel F hodd).psi
  let P := CFSG.ComponentClassification.CatalogueBOrthogonal.traceZeroProjectiveEquiv
    (K := K) F.two_ne_zero
  have hrho : rho F hodd g = (P.symm (e g)).1 := rfl
  rw [hrho]
  constructor
  · intro h1
    let εr : rootsOfUnity 2 K := (P.symm (e g)).2
    have hp : P.symm (e g) = (1, εr) := Prod.ext h1 rfl
    have hP : P (1, εr) = e g := by
      rw [← hp]
      exact MulEquiv.apply_symm_apply P (e g)
    refine ⟨(εr.val : K), ?_, ?_⟩
    · have := (mem_rootsOfUnity' 2 εr.val).mp εr.property
      simpa using this
    · intro w
      have hleft : (e g).val (psi w) = psi (g.val w) := by
        have he := (traceZeroModel F hodd).equiv_apply g
        rw [he]
        simp [psi, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      have hright : (e g).val (psi w) = (εr.val : K) • psi w := by
        rw [← hP]
        apply Subtype.ext
        simpa using traceZeroProjectiveEquiv_one_apply (F := F) εr (psi w)
      apply psi.injective
      rw [← hleft, hright, map_smul]
  · rintro ⟨ε, hε, hg⟩
    have hε0 : ε ≠ 0 := by
      intro h0
      rw [h0] at hε
      norm_num at hε
    let u : Kˣ := Units.mk0 ε hε0
    have huval : (u : K) = ε := Units.val_mk0 hε0
    have hu : u ∈ rootsOfUnity 2 K := (mem_rootsOfUnity' 2 u).mpr (by
      change (u : K) ^ 2 = 1
      rw [huval]
      exact hε)
    let εr : rootsOfUnity 2 K := ⟨u, hu⟩
    have hεr : (εr.val : K) = ε := by
      change (u : K) = ε
      exact huval
    have hP : P (1, εr) = e g := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro X
      apply Subtype.ext
      obtain ⟨w, rfl⟩ := psi.surjective X
      have he := (traceZeroModel F hodd).equiv_apply g
      rw [he]
      simp only [psi, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        hg, map_smul]
      simpa [hεr] using traceZeroProjectiveEquiv_one_apply (F := F) εr (psi w)
    have hp : P.symm (e g) = (1, εr) := by
      rw [← hP]
      exact MulEquiv.symm_apply_apply P (1, εr)
    rw [hp]

@[expose] noncomputable def eta (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    C0 F →* CFSG.GorensteinWalter.PGL2 K :=
  (rho F hodd).comp (resPlus F)

theorem eta_apply (F : FrameData Q) (hodd : Odd (Nat.card K)) (g : C0 F) :
    eta F hodd g = rho F hodd (resPlus F g) := rfl

theorem eta_surjective (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    Function.Surjective (eta F hodd) :=
  (rho_surjective F hodd).comp (resPlus_surjective F)

theorem eta_tPositiveEmbedding (F : FrameData Q) (hodd : Odd (Nat.card K))
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype)) :
    eta F hodd ⟨tPositiveEmbedding F g, tPositiveEmbedding_mem_C0 F g⟩ =
      rho F hodd g := by
  rw [eta_apply, resPlus_tPositiveEmbedding]

end TraceZeroAction

section PSL2Action

variable [Finite K]

@[expose] noncomputable def etaX (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    tPositiveDerived F →* CFSG.GorensteinWalter.PGL2 K :=
  (eta F hodd).comp (Subgroup.inclusion (tPositiveDerived_le_C0 F))

private theorem etaX_range_eq_map (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    (etaX F hodd).range =
      (commutator (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (Wplus F).subtype))).map (rho F hodd) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    have hxX : (x : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
        (commutator (TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (Wplus F).subtype))).map (tPositiveEmbedding F) := by
      rw [← tPositiveDerived_eq_map_commutator]
      exact x.property
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hxX
    let x' : tPositiveDerived F := ⟨tPositiveEmbedding F d, by
      rw [tPositiveDerived_eq_map_commutator]
      exact Subgroup.mem_map.mpr ⟨d, hd, rfl⟩⟩
    have hxsub : x = x' := by
      apply Subtype.ext
      exact hdx.symm
    have hone : (Subgroup.inclusion (tPositiveDerived_le_C0 F)) x' =
        ⟨tPositiveEmbedding F d, tPositiveEmbedding_mem_C0 F d⟩ := by
      apply Subtype.ext
      exact Subgroup.coe_inclusion _ _
    have hxeta : etaX F hodd x = rho F hodd d := by
      rw [hxsub]
      simp only [etaX, MonoidHom.comp_apply]
      rw [hone, eta_tPositiveEmbedding]
    rw [hxeta]
    exact Subgroup.mem_map.mpr ⟨d, hd, rfl⟩
  · rintro y ⟨d, hd, rfl⟩
    let xd : tPositiveDerived F := ⟨tPositiveEmbedding F d, by
      rw [tPositiveDerived_eq_map_commutator]
      exact Subgroup.mem_map.mpr ⟨d, hd, rfl⟩⟩
    refine ⟨xd, ?_⟩
    have hincl : (Subgroup.inclusion (tPositiveDerived_le_C0 F)) xd =
        ⟨tPositiveEmbedding F d, tPositiveEmbedding_mem_C0 F d⟩ := by
      apply Subtype.ext
      exact Subgroup.coe_inclusion _ _
    simp only [etaX, MonoidHom.comp_apply]
    rw [hincl, eta_tPositiveEmbedding]

theorem etaX_range (F : FrameData Q) (hodd : Odd (Nat.card K)) (h3 : 3 < Nat.card K) :
    (etaX F hodd).range =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  rw [etaX_range_eq_map]
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (rho_surjective F hodd),
    ← commutator_def]
  exact CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three
    K (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hodd) h3

private theorem etaX_ker_eq_bot (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    ∀ x : tPositiveDerived F, etaX F hodd x = 1 → x = 1 := by
  intro x hx
  have hxX : (x : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
      (commutator (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (Wplus F).subtype))).map (tPositiveEmbedding F) := by
    rw [← tPositiveDerived_eq_map_commutator]
    exact x.property
  obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hxX
  let x' : tPositiveDerived F := ⟨tPositiveEmbedding F d, by
    rw [tPositiveDerived_eq_map_commutator]
    exact Subgroup.mem_map.mpr ⟨d, hd, rfl⟩⟩
  have hxsub : x = x' := by
    apply Subtype.ext
    exact hdx.symm
  have hone : (Subgroup.inclusion (tPositiveDerived_le_C0 F)) x' =
      ⟨tPositiveEmbedding F d, tPositiveEmbedding_mem_C0 F d⟩ := by
    apply Subtype.ext
    exact Subgroup.coe_inclusion _ _
  rw [hxsub] at hx
  rw [etaX, MonoidHom.comp_apply, hone, eta_tPositiveEmbedding] at hx
  have hscalar := (rho_eq_one_iff F hodd d).mp hx
  obtain ⟨a, ha2, hact⟩ := hscalar
  let detA3 : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype) →* Kˣ :=
    LinearEquiv.det.comp (TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (Wplus F).subtype)).subtype
  have hdker : d ∈ detA3.ker :=
    Abelianization.commutator_subset_ker detA3 hd
  have hdet1 : LinearEquiv.det (d : Wplus F ≃ₗ[K] Wplus F) = 1 := hdker
  have hlin : (d : Wplus F ≃ₗ[K] Wplus F).toLinearMap = a • LinearMap.id := by
    apply LinearMap.ext
    intro w
    exact hact w
  have hdetpow : LinearEquiv.det (d : Wplus F ≃ₗ[K] Wplus F) = a ^ 3 := by
    rw [LinearEquiv.coe_det, hlin, LinearMap.det_smul, LinearMap.det_id,
      finrank_Wplus, mul_one]
  have ha3 : a ^ 3 = 1 := by
    simpa [hdet1] using hdetpow.symm
  have ha1 : a = 1 := by
    have h : a ^ 2 * a = 1 := by simpa [pow_succ] using ha3
    rw [ha2, one_mul] at h
    exact h
  have hd1 : d = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    rw [hact w, ha1, one_smul]
    rfl
  rw [hxsub]
  apply Subtype.ext
  dsimp only [x']
  rw [hd1, map_one]
  exact Subgroup.coe_one (H := tPositiveDerived F)

theorem etaX_injective (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    Function.Injective (etaX F hodd) := by
  intro x y hxy
  have h : x * y⁻¹ = 1 := by
    apply etaX_ker_eq_bot F hodd
    rw [map_mul, map_inv, hxy]
    exact mul_inv_cancel (etaX F hodd y)
  calc x = x * y⁻¹ * y := by group
    _ = y := by rw [h, one_mul]

@[expose] noncomputable def eX (F : FrameData Q) (hodd : Odd (Nat.card K)) (h3 : 3 < Nat.card K) :
    tPositiveDerived F ≃* CFSG.GorensteinWalter.PSL2 K :=
  ((MulEquiv.ofBijective (etaX F hodd).rangeRestrict
    ⟨fun a b hab => etaX_injective F hodd (congrArg Subtype.val hab),
      fun y => by
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.property
        exact ⟨x, Subtype.ext hx⟩⟩).trans
    (MulEquiv.subgroupCongr (etaX_range F hodd h3))).trans
    (CFSG.GorensteinWalter.psl2EquivToPGLRange K).symm

theorem toPGL_eX_apply (F : FrameData Q) (hodd : Odd (Nat.card K)) (h3 : 3 < Nat.card K)
    (x : tPositiveDerived F) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (eX F hodd h3 x) = etaX F hodd x := by
  let y : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
    (MulEquiv.subgroupCongr (etaX_range F hodd h3)) ((etaX F hodd).rangeRestrict x)
  have hy : y.val = etaX F hodd x := rfl
  have hp (p : CFSG.GorensteinWalter.PSL2 K) :
      (CFSG.GorensteinWalter.psl2EquivToPGLRange K p).val =
        Matrix.ProjectiveSpecialLinearGroup.toPGL p := rfl
  have hs : eX F hodd h3 x =
      (CFSG.GorensteinWalter.psl2EquivToPGLRange K).symm y := rfl
  rw [hs, ← hy, ← hp]
  exact congrArg Subtype.val
    (MulEquiv.apply_symm_apply (CFSG.GorensteinWalter.psl2EquivToPGLRange K) y)

end PSL2Action


section Normalization

variable [Finite K] (hodd : Odd (Nat.card K))

theorem tPositive_conj (F : FrameData Q) (g : C0 F)
    (h : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype)) :
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) * tPositiveEmbedding F h *
        ((g⁻¹ : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) =
      tPositiveEmbedding F (resPlus F g * h * (resPlus F g)⁻¹) := by
  have hW : (g.val : V ≃ₗ[K] V) ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub (Wplus F) := by
    rw [CFSG.ClassicalGroups.Orthogonal.Small.mem_stabSub]
    intro x
    constructor
    · exact C0_preserves_Wplus F g
    · intro hx
      have hgx : (g⁻¹ : C0 F).val.val ((g.val : V ≃ₗ[K] V) x) ∈ Wplus F :=
        C0_preserves_Wplus F (g⁻¹) hx
      simpa [LinearEquiv.apply_inv_apply'] using hgx
  have hW' : (g.val : V ≃ₗ[K] V) ∈ CFSG.ClassicalGroups.Orthogonal.Small.stabSub
      (orthPerp Q (Wplus F)) := by
    rw [CFSG.ClassicalGroups.Orthogonal.Small.mem_stabSub]
    intro x
    constructor
    · exact C0_preserves_orthPerp F g
    · intro hx
      have hgx : (g⁻¹ : C0 F).val.val ((g.val : V ≃ₗ[K] V) x) ∈ orthPerp Q (Wplus F) :=
        C0_preserves_orthPerp F (g⁻¹) hx
      simpa [LinearEquiv.apply_inv_apply'] using hgx
  have hres : (resPlus F g : Wplus F ≃ₗ[K] Wplus F) =
      CFSG.ClassicalGroups.Orthogonal.Small.resHom (Wplus F) ⟨(g.val : V ≃ₗ[K] V), hW⟩ := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [CFSG.ClassicalGroups.Orthogonal.Small.resHom_apply, resPlus_apply]
  have hconj := CFSG.ClassicalGroups.Orthogonal.Small.conj_orthExtend
    (W := Wplus F) (W' := orthPerp Q (Wplus F)) (isCompl_Wplus F) hW hW'
    (h : Wplus F ≃ₗ[K] Wplus F)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hiota : ∀ k, ((tPositiveEmbedding F k : TauCeti.QuadraticMap.orthogonalGroup Q) :
      V ≃ₗ[K] V) = CFSG.LocalAnalysis.ComponentInitial.orthExtend
        (isCompl_Wplus F) k := fun k => rfl
  have hk : ((resPlus F g * h * (resPlus F g)⁻¹ :
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype)) :
      Wplus F ≃ₗ[K] Wplus F) =
      CFSG.ClassicalGroups.Orthogonal.Small.resHom (Wplus F)
        ⟨(g.val : V ≃ₗ[K] V), hW⟩ * h *
      (CFSG.ClassicalGroups.Orthogonal.Small.resHom (Wplus F)
        ⟨(g.val : V ≃ₗ[K] V), hW⟩)⁻¹ := by
    apply LinearEquiv.ext
    intro w
    rfl
  have hv := congrArg (fun e : V ≃ₗ[K] V => e v) hconj
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, hiota, hres] using hv


theorem tPositiveDerived_normalized (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    C0 F ≤ Subgroup.normalizer (tPositiveDerived F : Set
      (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have hconj_mem : ∀ (c : C0 F) {y : TauCeti.QuadraticMap.orthogonalGroup Q},
      y ∈ tPositiveDerived F →
        (c : TauCeti.QuadraticMap.orthogonalGroup Q) * y *
          ((c⁻¹ : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
            tPositiveDerived F := by
    intro c y hy
    let A3 := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype)
    let D3 := commutator A3
    have hDnormal : D3.Normal := inferInstance
    have hy' : y ∈ D3.map (tPositiveEmbedding F) := by
      rw [← tPositiveDerived_eq_map_commutator]
      exact hy
    obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hy'
    rw [← hdy, tPositive_conj F c d]
    let k : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype) :=
      resPlus F c * d * (resPlus F c)⁻¹
    have hk : k ∈ D3 := hDnormal.conj_mem d hd (resPlus F c)
    rw [tPositiveDerived_eq_map_commutator]
    exact Subgroup.mem_map_of_mem (tPositiveEmbedding F) hk
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hconj_mem ⟨g, hg⟩ hx
  · intro hx
    have h := hconj_mem (⟨g, hg⟩ : C0 F)⁻¹ hx
    simpa [Subgroup.coe_inv, inv_inv, mul_assoc] using h

theorem eta_eq_one_iff_centralizes_X (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (g : C0 F) :
    eta F hodd g = 1 ↔ ∀ x : tPositiveDerived F,
      (g : TauCeti.QuadraticMap.orthogonalGroup Q) * x.val =
        x.val * (g : TauCeti.QuadraticMap.orthogonalGroup Q) := by
  constructor
  · intro hg x
    have hxconj :
        g.val * x.val * g.val⁻¹ ∈ tPositiveDerived F :=
      ((Subgroup.mem_normalizer_iff.mp
        ((tPositiveDerived_normalized F hodd) g.property)) x.val).mp x.property
    let y : tPositiveDerived F := ⟨g.val * x.val * g.val⁻¹, hxconj⟩
    have hi : Subgroup.inclusion (tPositiveDerived_le_C0 F) y =
        g * Subgroup.inclusion (tPositiveDerived_le_C0 F) x * g⁻¹ := by
      apply Subtype.ext
      rfl
    have heta : etaX F hodd y = etaX F hodd x := by
      change eta F hodd (Subgroup.inclusion (tPositiveDerived_le_C0 F) y) =
        eta F hodd (Subgroup.inclusion (tPositiveDerived_le_C0 F) x)
      rw [hi]
      simp only [map_mul, map_inv, hg, one_mul, inv_one, mul_one]
    have hval : g.val * x.val * g.val⁻¹ = x.val :=
      congrArg (fun z : tPositiveDerived F => z.val)
        (etaX_injective F hodd heta)
    have h := congrArg
      (fun z : TauCeti.QuadraticMap.orthogonalGroup Q => z * g.val) hval
    simpa [mul_assoc] using h
  · intro hcent
    have hmem : eta F hodd g ∈ Subgroup.centralizer
        ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :
          Set (CFSG.GorensteinWalter.PGL2 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hj' : j ∈ (etaX F hodd).range := by
        rw [etaX_range F hodd h3]
        exact hj
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hj'
      have hxcent : (g : TauCeti.QuadraticMap.orthogonalGroup Q) * x.val =
          x.val * (g : TauCeti.QuadraticMap.orthogonalGroup Q) := hcent x
      have hxC : g * (Subgroup.inclusion (tPositiveDerived_le_C0 F) x) * g⁻¹ =
          Subgroup.inclusion (tPositiveDerived_le_C0 F) x := by
        apply Subtype.ext
        have := congrArg (fun y : TauCeti.QuadraticMap.orthogonalGroup Q =>
          y * ((g⁻¹ : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q)) hxcent
        change (g : TauCeti.QuadraticMap.orthogonalGroup Q) * x.val *
          ((g⁻¹ : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) = x.val
        simpa [mul_assoc] using this
      have heta : eta F hodd g * etaX F hodd x * (eta F hodd g)⁻¹ =
          etaX F hodd x := by
        change eta F hodd g * eta F hodd
            (Subgroup.inclusion (tPositiveDerived_le_C0 F) x) * (eta F hodd g)⁻¹ =
          eta F hodd (Subgroup.inclusion (tPositiveDerived_le_C0 F) x)
        have h := congrArg (eta F hodd) hxC
        rw [map_mul, map_mul, map_inv] at h
        exact h
      rw [← hx]
      have h2 := congrArg (fun y => y * eta F hodd g) heta
      simpa [mul_assoc] using h2.symm
    have hzero := CFSG.GorensteinWalter.pgl2_psl2Range_centralizer_eq_bot K
      (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hodd)
    rw [hzero] at hmem
    simpa using hmem

end Normalization


section Simplicity

variable [Finite K] (hodd : Odd (Nat.card K)) (h3 : 3 < Nat.card K)

theorem tPositiveDerived_isSimpleGroup (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) :
    IsSimpleGroup (tPositiveDerived F) := by
  letI : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := K) (by omega)
  exact MulEquiv.isSimpleGroup (eX F hodd h3)

theorem tPositiveDerived_not_isMulCommutative (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) :
    ¬ IsMulCommutative (tPositiveDerived F) := by
  have hperfPSL : Group.IsPerfect (CFSG.GorensteinWalter.PSL2 K) :=
    CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three K h3
  have hperf : Group.IsPerfect (tPositiveDerived F) :=
    Group.IsPerfect.ofSurjective (f := (eX F hodd h3).symm.toMonoidHom)
      (eX F hodd h3).symm.surjective
  letI : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := K) (by omega)
  haveI : Nontrivial (tPositiveDerived F) := (eX F hodd h3).toEquiv.nontrivial
  intro hcomm
  letI : Group.IsPerfect (tPositiveDerived F) := hperf
  exact Group.IsPerfect.not_isMulCommutative (G := tPositiveDerived F) hcomm

end Simplicity





section CommonCentralizer

variable [Finite K] (hodd : Odd (Nat.card K)) (h3 : 3 < Nat.card K)

@[expose] noncomputable def tPositiveDerivedConj (F : FrameData Q) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  (tPositiveDerived F).map (MulAut.conj F.sO).toMonoidHom

private theorem e2_mem_Wplus (F : FrameData Q) : F.e 2 ∈ Wplus F := by
  change F.e 2 ∈ Module.End.eigenspace (tOp F) 1
  rw [Module.End.mem_eigenspace_iff]
  simp [tOp, F.t_e]

private theorem e3_mem_Wplus (F : FrameData Q) : F.e 3 ∈ Wplus F := by
  change F.e 3 ∈ Module.End.eigenspace (tOp F) 1
  rw [Module.End.mem_eigenspace_iff]
  simp [tOp, F.t_e]

private theorem e4_mem_Wplus (F : FrameData Q) : F.e 4 ∈ Wplus F := by
  change F.e 4 ∈ Module.End.eigenspace (tOp F) 1
  rw [Module.End.mem_eigenspace_iff]
  simp [tOp, F.t_e]

private theorem exists_scalar_on_Wplus (F : FrameData Q)
    (hodd : Odd (Nat.card K)) (h3 : 3 < Nat.card K)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) (hgC0 : g ∈ C0 F)
    (hgX : ∀ x ∈ tPositiveDerived F, Commute g x) :
    ∃ a : K, a ^ 2 = 1 ∧ ∀ w : Wplus F, g.val w.val = a • w.val := by
  let gc : C0 F := ⟨g, hgC0⟩
  have heta : eta F hodd gc = 1 :=
    (eta_eq_one_iff_centralizes_X F hodd h3 gc).mpr (by
      intro x
      exact hgX x.val x.property)
  have hrho : rho F hodd (resPlus F gc) = 1 := by
    rw [← eta_apply F hodd gc, heta]
  obtain ⟨a, ha2, hact⟩ := (rho_eq_one_iff F hodd (resPlus F gc)).mp hrho
  refine ⟨a, ha2, ?_⟩
  intro w
  have h := congrArg Subtype.val (hact w)
  simpa [resPlus_apply] using h

theorem tPositive_common_centralizer_eq_one (F : FrameData Q)
    (hodd : Odd (Nat.card K)) (h3 : 3 < Nat.card K)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgSO : g ∈ Q.specialOrthogonalWithin)
    (hgt : Commute g F.tO) (hgz : Commute g F.zO)
    (hgX : ∀ x ∈ tPositiveDerived F, Commute g x)
    (hgX' : ∀ x ∈ tPositiveDerivedConj F, Commute g x) : g = 1 := by
  have hs : F.sO⁻¹ = F.sO := inv_eq_of_mul_eq_one_right F.sO_mul_self
  have hgC0 : g ∈ C0 F := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hgt
  obtain ⟨a, ha2, hact⟩ := exists_scalar_on_Wplus F hodd h3 g hgC0 hgX
  let g' : TauCeti.QuadraticMap.orthogonalGroup Q := F.sO⁻¹ * g * F.sO
  have hzt : F.sO⁻¹ * (F.zO * F.tO) * F.sO = F.tO := by
    simpa [hs] using FiveDimensionalSylow.sO_conj_zt F
  have hg't : Commute g' F.tO := by
    have h := (hgz.mul_right hgt).conj F.sO⁻¹
    simpa only [g', inv_inv, hzt] using h
  have hg'C0 : g' ∈ C0 F := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hg't
  have hg'X : ∀ x ∈ tPositiveDerived F, Commute g' x := by
    intro x hx
    have hx' : F.sO * x * F.sO⁻¹ ∈ tPositiveDerivedConj F := by
      rw [tPositiveDerivedConj]
      exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have hcongr : Commute (F.sO⁻¹ * g * F.sO) x := by
      have h := (hgX' _ hx').conj F.sO⁻¹
      simpa [mul_assoc] using h
    simpa [g'] using hcongr
  obtain ⟨b, _hb2, hbact⟩ := exists_scalar_on_Wplus F hodd h3 g' hg'C0 hg'X
  have hg_s : ∀ w : V, g.val (F.s w) = F.s (g'.val w) := by
    intro w
    have hcomm : g * F.sO = F.sO * g' := by
      dsimp [g']
      calc g * F.sO = (F.sO * F.sO⁻¹) * (g * F.sO) := by
            rw [mul_inv_cancel, one_mul]
        _ = F.sO * (F.sO⁻¹ * g * F.sO) := by rw [mul_assoc, mul_assoc]
    have h := congrArg (fun e : V ≃ₗ[K] V => e w)
      (congrArg (fun z : TauCeti.QuadraticMap.orthogonalGroup Q =>
        (z : V ≃ₗ[K] V)) hcomm)
    simpa [LinearEquiv.mul_apply] using h
  have hs2 : (F.s : V ≃ₗ[K] V) (F.e 2) = F.e 0 := by simpa using F.s_e 2
  have hs3 : (F.s : V ≃ₗ[K] V) (F.e 3) = F.e 1 := by simpa using F.s_e 3
  have hs4 : (F.s : V ≃ₗ[K] V) (F.e 4) = F.e 4 := by simpa using F.s_e 4
  have hb0 : g.val (F.e 0) = b • F.e 0 := by
    have h := hg_s (F.e 2)
    rw [hbact ⟨F.e 2, e2_mem_Wplus F⟩] at h
    rw [hs2] at h
    simpa [map_smul, hs2] using h
  have hb1 : g.val (F.e 1) = b • F.e 1 := by
    have h := hg_s (F.e 3)
    rw [hbact ⟨F.e 3, e3_mem_Wplus F⟩] at h
    rw [hs3] at h
    simpa [map_smul, hs3] using h
  have hb4 : g.val (F.e 4) = b • F.e 4 := by
    have h := hg_s (F.e 4)
    rw [hbact ⟨F.e 4, e4_mem_Wplus F⟩] at h
    rw [hs4] at h
    simpa [map_smul, hs4] using h
  have ha2' : g.val (F.e 2) = a • F.e 2 := hact ⟨F.e 2, e2_mem_Wplus F⟩
  have ha3' : g.val (F.e 3) = a • F.e 3 := hact ⟨F.e 3, e3_mem_Wplus F⟩
  have ha4' : g.val (F.e 4) = a • F.e 4 := hact ⟨F.e 4, e4_mem_Wplus F⟩
  have hab : a = b := by
    have h : a • F.e 4 = b • F.e 4 := by rw [← ha4', hb4]
    exact F.e.linearIndependent.smul_left_injective 4 h
  have hgb : ∀ i : Fin 5, g.val (F.e i) = a • F.e i := by
    intro i
    fin_cases i
    · change g.val (F.e 0) = a • F.e 0
      rw [hab]; exact hb0
    · change g.val (F.e 1) = a • F.e 1
      rw [hab]; exact hb1
    · change g.val (F.e 2) = a • F.e 2
      exact ha2'
    · change g.val (F.e 3) = a • F.e 3
      exact ha3'
    · change g.val (F.e 4) = a • F.e 4
      exact ha4'
  have hg_lin : (g.val : V →ₗ[K] V) = a • LinearMap.id := by
    apply F.e.ext
    intro i
    simpa using hgb i
  have hdet : (LinearEquiv.det (g.val : V ≃ₗ[K] V) : K) = a ^ 5 := by
    rw [LinearEquiv.coe_det, hg_lin, LinearMap.det_smul, LinearMap.det_id,
      Module.finrank_eq_card_basis F.e]
    simp
  have hdet1 : (LinearEquiv.det (g.val : V ≃ₗ[K] V) : K) = 1 := by
    have h := QuadraticMap.mem_specialOrthogonalWithin_iff.mp hgSO
    simpa using congrArg (fun u : Kˣ => (u : K)) h
  have ha5 : a ^ 5 = 1 := by
    rw [← hdet]
    exact hdet1
  have ha1 : a = 1 := by
    have hpow : a ^ 5 = (a ^ 2) ^ 2 * a := by ring
    rw [ha2, one_pow, one_mul] at hpow
    rw [hpow] at ha5
    exact ha5
  have hgid : (g.val : V →ₗ[K] V) = LinearMap.id := by
    rw [hg_lin, ha1, one_smul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have h := LinearMap.congr_fun hgid v
  simpa using h

end CommonCentralizer



end CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive
