module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponentTransport
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitMatrix

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup Matrix CFSG.ComponentClassification CatalogueBProjectiveInvolution
  CatalogueBProjectiveCoordinates
open scoped MatrixGroups

namespace ProjectiveEigenspace

variable {K : Type*} [Field K] {n : ℕ}

theorem matrix_eq_of_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M₁ M₂ : Matrix ι ι K} (h : ∀ v, M₁ *ᵥ v = M₂ *ᵥ v) : M₁ = M₂ :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using h v)

section Split

variable {T : GL (Fin n) K} {c : Kˣ} (htwo : (2 : K) ≠ 0)
  (hsq : T ^ 2 = GeneralLinearGroup.scalar (Fin n) (c ^ 2))

include htwo hsq

theorem splitEquiv_fst_mulVec (x : centralizer {T}) (a : (splitMatrixOperator T).eigenspace c.val) :
    ((matrixCentralizerSplitEquiv T c htwo hsq x).1 : Matrix _ _ K) *ᵥ
        (positiveMatrixBasis T c.val).equivFun a =
      (positiveMatrixBasis T c.val).equivFun
        (operatorCentralizerRestriction (splitMatrixOperator T) c.val
          (matrixCentralizerEquiv T x) a) := by
  rw [matrixCentralizerSplitEquiv_apply]
  exact basisAutomorphismMatrixEquiv_mulVec _ _ a

theorem splitEquiv_snd_mulVec (x : centralizer {T})
    (w : (splitMatrixOperator T).eigenspace (-c.val)) :
    ((matrixCentralizerSplitEquiv T c htwo hsq x).2 : Matrix _ _ K) *ᵥ
        (negativeMatrixBasis T c.val).equivFun w =
      (negativeMatrixBasis T c.val).equivFun
        (operatorCentralizerRestriction (splitMatrixOperator T) (-c.val)
          (matrixCentralizerEquiv T x) w) := by
  rw [matrixCentralizerSplitEquiv_apply]
  exact basisAutomorphismMatrixEquiv_mulVec _ _ w

theorem fix_of_splitEquiv_fst_eq_one {x : centralizer {T}}
    (h : (matrixCentralizerSplitEquiv T c htwo hsq x).1 = 1) :
    ∀ a ∈ (splitMatrixOperator T).eigenspace c.val,
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a = a := by
  intro a ha
  have h1 := splitEquiv_fst_mulVec htwo hsq x ⟨a, ha⟩
  rw [h, Units.val_one, one_mulVec] at h1
  exact (congrArg Subtype.val ((positiveMatrixBasis T c.val).equivFun.injective h1)).symm

theorem fix_of_splitEquiv_snd_eq_one {x : centralizer {T}}
    (h : (matrixCentralizerSplitEquiv T c htwo hsq x).2 = 1) :
    ∀ w ∈ (splitMatrixOperator T).eigenspace (-c.val),
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
  intro w hw
  have h1 := splitEquiv_snd_mulVec htwo hsq x ⟨w, hw⟩
  rw [h, Units.val_one, one_mulVec] at h1
  exact (congrArg Subtype.val ((negativeMatrixBasis T c.val).equivFun.injective h1)).symm

theorem splitEquiv_snd_eq_one {x : centralizer {T}}
    (h : ∀ w ∈ (splitMatrixOperator T).eigenspace (-c.val),
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w) :
    (matrixCentralizerSplitEquiv T c htwo hsq x).2 = 1 := by
  change basisAutomorphismMatrixEquiv (negativeMatrixBasis T c.val)
    (operatorCentralizerRestriction (splitMatrixOperator T) (-c.val)
      (matrixCentralizerEquiv T x)) = 1
  have h1 : operatorCentralizerRestriction (splitMatrixOperator T) (-c.val)
      (matrixCentralizerEquiv T x) = 1 :=
    LinearEquiv.ext fun w => Subtype.ext (h w w.2)
  rw [h1, map_one]

theorem fix_or_fix_of_isComponent [Finite K] {L : Subgroup (centralizer {T})}
    (hL : CFSG.IsComponent L) :
    (∀ x ∈ L, ∀ w ∈ (splitMatrixOperator T).eigenspace (-c.val),
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∨
      ∀ x ∈ L, ∀ a ∈ (splitMatrixOperator T).eigenspace c.val,
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a = a := by
  set e := matrixCentralizerSplitEquiv T c htwo hsq
  have hL' := isComponent_map_of_isComponent e hL
  set L' := L.map e.toMonoidHom
  have hN₁ := Subgroup.prod_normal (⊤ : Subgroup (GL (Fin (positiveMatrixDimension T c.val)) K))
    (⊥ : Subgroup (GL (Fin (negativeMatrixDimension T c.val)) K))
  have hN₂ := Subgroup.prod_normal (⊥ : Subgroup (GL (Fin (positiveMatrixDimension T c.val)) K))
    (⊤ : Subgroup (GL (Fin (negativeMatrixDimension T c.val)) K))
  rcases component_normal_subgroup hL' hN₁ with h1 | h1
  · left
    intro x hx
    refine fix_of_splitEquiv_snd_eq_one htwo hsq ?_
    exact (mem_prod.1 (h1 (mem_map_of_mem e.toMonoidHom hx))).2
  rcases component_normal_subgroup hL' hN₂ with h2 | h2
  · right
    intro x hx
    refine fix_of_splitEquiv_fst_eq_one htwo hsq ?_
    exact (mem_prod.1 (h2 (mem_map_of_mem e.toMonoidHom hx))).1
  exfalso
  have hc₁ := commutator_eq_bot_iff_le_centralizer.1 h1
  have hc₂ := commutator_eq_bot_iff_le_centralizer.1 h2
  refine not_le_centralizer_self_of_isQuasisimple
    ((AssemblyBPredicates.isQuasisimple_iff_native L').2 hL'.1) fun p hp => ?_
  rw [mem_centralizer_iff]
  intro q _
  have hq : q = (q.1, 1) * (1, q.2) := by simp
  have hq₁ : (q.1, (1 : GL (Fin (negativeMatrixDimension T c.val)) K)) ∈
      (⊤ : Subgroup (GL (Fin (positiveMatrixDimension T c.val)) K)).prod ⊥ :=
    mem_prod.2 ⟨mem_top _, one_mem _⟩
  have hq₂ : ((1 : GL (Fin (positiveMatrixDimension T c.val)) K), q.2) ∈
      (⊥ : Subgroup (GL (Fin (positiveMatrixDimension T c.val)) K)).prod ⊤ :=
    mem_prod.2 ⟨one_mem _, mem_top _⟩
  have e₁ := mem_centralizer_iff.1 (hc₁ hp) _ hq₁
  have e₂ := mem_centralizer_iff.1 (hc₂ hp) _ hq₂
  rw [hq, mul_assoc, e₂, ← mul_assoc, e₁, mul_assoc]

@[expose] def splitFst : centralizer {T} →* GL (Fin (positiveMatrixDimension T c.val)) K :=
  (MonoidHom.fst _ _).comp (matrixCentralizerSplitEquiv T c htwo hsq).toMonoidHom

theorem splitFst_apply (x : centralizer {T}) :
    splitFst htwo hsq x = (matrixCentralizerSplitEquiv T c htwo hsq x).1 := rfl

theorem splitFst_surjective : Function.Surjective (splitFst htwo hsq) := fun M =>
  ⟨(matrixCentralizerSplitEquiv T c htwo hsq).symm (M, 1), by simp [splitFst_apply]⟩

theorem toMatrix_restrict_eq_splitFst (x : centralizer {T})
    (hA : ∀ a ∈ (splitMatrixOperator T).eigenspace c.val,
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a ∈
        (splitMatrixOperator T).eigenspace c.val) :
    LinearMap.toMatrix (positiveMatrixBasis T c.val) (positiveMatrixBasis T c.val)
        ((mulVecLin ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).restrict hA) =
      (splitFst htwo hsq x).val := by
  refine matrix_eq_of_mulVec_eq fun v => ?_
  obtain ⟨a, rfl⟩ := (positiveMatrixBasis T c.val).equivFun.surjective v
  have h1 := LinearMap.toMatrix_mulVec_repr (positiveMatrixBasis T c.val)
    (positiveMatrixBasis T c.val)
    ((mulVecLin ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).restrict hA) a
  have h2 := splitEquiv_fst_mulVec htwo hsq x a
  exact h1.trans h2.symm

theorem det_restrict_eq_det_splitFst (x : centralizer {T})
    (hA : ∀ a ∈ (splitMatrixOperator T).eigenspace c.val,
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a ∈
        (splitMatrixOperator T).eigenspace c.val) :
    LinearMap.det ((mulVecLin ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).restrict hA) =
      (splitFst htwo hsq x).val.det := by
  rw [← toMatrix_restrict_eq_splitFst htwo hsq x hA, LinearMap.det_toMatrix]

omit htwo hsq in
theorem mulVec_mem_eigenspace (x : centralizer {T}) {a : Fin n → K}
    (ha : a ∈ (splitMatrixOperator T).eigenspace c.val) :
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a ∈
      (splitMatrixOperator T).eigenspace c.val :=
  operatorCentralizer_preserves_eigenspace (splitMatrixOperator T) c.val
    (matrixCentralizerEquiv T x) ha

variable {L : Subgroup (centralizer {T})} (hL : CFSG.IsComponent L)
  (hfix : ∀ x ∈ L, ∀ w ∈ (splitMatrixOperator T).eigenspace (-c.val),
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = w)

include hfix in
theorem splitFst_injOn {x y : centralizer {T}} (hx : x ∈ L) (hy : y ∈ L)
    (h : splitFst htwo hsq x = splitFst htwo hsq y) : x = y := by
  apply (matrixCentralizerSplitEquiv T c htwo hsq).injective
  refine Prod.ext h ?_
  rw [splitEquiv_snd_eq_one htwo hsq (hfix x hx), splitEquiv_snd_eq_one htwo hsq (hfix y hy)]

include hL hfix in
theorem splitFst_map_eq [Finite K] (hA : (splitMatrixOperator T).eigenspace c.val ≠ ⊥) :
    L.map (splitFst htwo hsq) =
        CatalogueBGeneralLinear.specialLinearRange (positiveMatrixDimension T c.val) K ∧
      2 ≤ positiveMatrixDimension T c.val := by
  set r := positiveMatrixDimension T c.val with hr
  have hr1 : 1 ≤ r := by
    rw [Nat.one_le_iff_ne_zero, hr, positiveMatrixDimension]
    exact fun h => hA (Submodule.finrank_eq_zero.1 h)
  have hLL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hL.1.1
  set L₁ := L.map (splitFst htwo hsq)
  have hsub : L₁.IsSubnormal := hL.2.map (splitFst_surjective htwo hsq)
  have : Group.IsPerfect L₁ :=
    Subgroup.isPerfect_iff.2 (by rw [← map_commutator, hLL])
  have hne : L₁ ≠ ⊥ := by
    have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    obtain ⟨⟨x, hxL⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
      ((Subgroup.nontrivial_iff_ne_bot L).1 this)
    intro hbot
    apply hx1
    have h1 : splitFst htwo hsq x = splitFst htwo hsq 1 := by
      rw [map_one, ← mem_bot, ← hbot]
      exact mem_map_of_mem _ hxL
    exact Subtype.ext (splitFst_injOn htwo hsq hfix hxL (one_mem L) h1)
  have : Nontrivial L₁ := (Subgroup.nontrivial_iff_ne_bot L₁).2 hne
  by_cases hsmall : r = 1 ∨ r = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3)
  · exfalso
    have : Group.IsSolvable (GL (Fin r) K) :=
      CatalogueBGeneralLinear.generalLinear_small_solvable r K hsmall
    exact Group.IsPerfect.not_isSolvable L₁ inferInstance
  · obtain ⟨hr2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters r K hr1 hsmall
    exact ⟨CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange r K hr2 h22 h23 L₁
      hsub, hr2⟩

include hL hfix in
theorem map_subtype_eq_summandSpecialLinear [Finite K]
    (hA : (splitMatrixOperator T).eigenspace c.val ≠ ⊥) :
    ((L.map (centralizer {T}).subtype : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K)) =
      summandSpecialLinear ((splitMatrixOperator T).eigenspace c.val)
        ((splitMatrixOperator T).eigenspace (-c.val)) := by
  have hmap := (splitFst_map_eq htwo hsq hL hfix hA).1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hA' : ∀ a ∈ (splitMatrixOperator T).eigenspace c.val,
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ a ∈
          (splitMatrixOperator T).eigenspace c.val := fun a ha => mulVec_mem_eigenspace x ha
    refine ⟨hfix x hx, hA', (det_restrict_eq_det_splitFst htwo hsq x hA').trans ?_⟩
    have hx1 : splitFst htwo hsq x ∈
        CatalogueBGeneralLinear.specialLinearRange (positiveMatrixDimension T c.val) K :=
      hmap ▸ mem_map_of_mem _ hx
    rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel, MonoidHom.mem_ker] at hx1
    rw [← GeneralLinearGroup.val_det_apply, hx1, Units.val_one]
  · rintro ⟨hgW, hgA, hdet⟩
    have hcompl := squareScalar_eigenspaces_isCompl (splitMatrixOperator T) c.val c.ne_zero htwo
      (splitMatrixOperator_square T c hsq)
    have hgX : g ∈ centralizer {T} := by
      refine (matrix_mem_centralizer_iff T g).2 fun v => ?_
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1
        (hcompl.sup_eq_top ▸ Submodule.mem_top : v ∈ _ ⊔ _)
      have hTa := Module.End.mem_eigenspace_iff.1 ha
      have hTw := Module.End.mem_eigenspace_iff.1 hw
      have hTga := Module.End.mem_eigenspace_iff.1 (hgA a ha)
      change (g : Matrix (Fin n) (Fin n) K) *ᵥ ((T : Matrix (Fin n) (Fin n) K) *ᵥ (a + w)) =
        (T : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ (a + w))
      change (T : Matrix (Fin n) (Fin n) K) *ᵥ a = c.val • a at hTa
      change (T : Matrix (Fin n) (Fin n) K) *ᵥ w = (-c.val) • w at hTw
      change (T : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ a) =
        c.val • ((g : Matrix (Fin n) (Fin n) K) *ᵥ a) at hTga
      rw [mulVec_add, mulVec_add, hTa, hTw, mulVec_add, hgW w hw, mulVec_smul, mulVec_smul,
        hgW w hw, mulVec_add, hTga, hTw]
    set x : centralizer {T} := ⟨g, hgX⟩
    have hx1 : splitFst htwo hsq x ∈
        CatalogueBGeneralLinear.specialLinearRange (positiveMatrixDimension T c.val) K := by
      rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel, MonoidHom.mem_ker]
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply, Units.val_one, ← det_restrict_eq_det_splitFst htwo hsq x
        hgA]
      exact hdet
    rw [← hmap] at hx1
    obtain ⟨y, hy, hyx⟩ := hx1
    have hyx' : y = x := by
      apply (matrixCentralizerSplitEquiv T c htwo hsq).injective
      refine Prod.ext hyx ?_
      rw [splitEquiv_snd_eq_one htwo hsq (hfix y hy), splitEquiv_snd_eq_one htwo hsq hgW]
    exact ⟨y, hy, by rw [hyx']; rfl⟩

include hL hfix in
theorem apply_eq_of_isPerfect_of_le_centralizer_split [Finite K]
    (hA : (splitMatrixOperator T).eigenspace c.val ≠ ⊥) {R : Subgroup (GL (Fin n) K)}
    (hR : R ≤ centralizer ((L.map (centralizer {T}).subtype : Subgroup (GL (Fin n) K)) :
      Set (GL (Fin n) K)))
    (hRp : ⁅R, R⁆ = R) {g : GL (Fin n) K} (hg : g ∈ R) :
    ∀ a ∈ (splitMatrixOperator T).eigenspace c.val, (g : Matrix (Fin n) (Fin n) K) *ᵥ a = a := by
  obtain ⟨hmap, hr2⟩ := splitFst_map_eq htwo hsq hL hfix hA
  have hcompl := squareScalar_eigenspaces_isCompl (splitMatrixOperator T) c.val c.ne_zero htwo
    (splitMatrixOperator_square T c hsq)
  set bA := positiveMatrixBasis T c.val
  let Ψ : ((Fin (positiveMatrixDimension T c.val) → K) ×
      (splitMatrixOperator T).eigenspace (-c.val)) ≃ₗ[K] (Fin n → K) :=
    (bA.equivFun.symm.prodCongr (LinearEquiv.refl K _)).trans
      (Submodule.prodEquivOfIsCompl _ _ hcompl)
  have hΨ : ∀ v w, Ψ (v, w) = (bA.equivFun.symm v : Fin n → K) + w := fun v w => rfl
  have hS : ∀ s : SpecialLinearGroup (Fin (positiveMatrixDimension T c.val)) K,
      ∃ g ∈ L.map (centralizer {T}).subtype, ∀ x,
        (g : Matrix (Fin n) (Fin n) K) *ᵥ Ψ x =
          Ψ ((summandSL K K ((splitMatrixOperator T).eigenspace (-c.val))
            (positiveMatrixDimension T c.val) s : _ →ₗ[K] _) x) := by
    intro s
    have hs : SpecialLinearGroup.toGL s ∈ L.map (splitFst htwo hsq) := by
      rw [hmap]
      exact ⟨s, rfl⟩
    obtain ⟨y, hy, hys⟩ := hs
    refine ⟨y, mem_map_of_mem _ hy, fun ⟨v, w⟩ => ?_⟩
    rw [summandSL_apply, hΨ, hΨ, mulVec_add, hfix y hy w w.2]
    congr 1
    have h1 := splitEquiv_fst_mulVec htwo hsq y (bA.equivFun.symm v)
    rw [← splitFst_apply, hys, SpecialLinearGroup.coe_GL_coe_matrix,
      LinearEquiv.apply_symm_apply] at h1
    rw [h1, LinearEquiv.symm_apply_apply]
    rfl
  intro a ha
  have h := apply_eq_of_isPerfect_of_le_centralizer_transport hr2 Ψ hS hR hRp hg
    (bA.equivFun ⟨a, ha⟩)
  rwa [hΨ, LinearEquiv.symm_apply_apply, Submodule.coe_zero, add_zero] at h

end Split

theorem eq_one_of_mk_eq_one_of_fix {W : Submodule K (Fin n → K)} (hW : W ≠ ⊥)
    {g : GL (Fin n) K} (hg : ProjGenLinGroup.mk g = 1)
    (hgW : ∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w) : g = 1 := by
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨t, rfl⟩ := hg
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have h1 := hgW w hw
  have h2 : (GeneralLinearGroup.scalar (Fin n) t : Matrix (Fin n) (Fin n) K) *ᵥ w = t.val • w :=
    congrArg (fun f : (Fin n → K) ≃ₗ[K] (Fin n → K) => f w) (matrixActionEquiv_scalar t)
  rw [h2] at h1
  have ht : t = 1 := by
    apply Units.ext
    have h3 : (t.val - 1) • w = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rw [Units.val_one, ← sub_eq_zero]
    exact (smul_eq_zero.1 h3).resolve_right hw0
  rw [ht, map_one]

end ProjectiveEigenspace

end CFSG.LocalAnalysis.ComponentInitial
