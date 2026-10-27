module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataFamily
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitBasic

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)
open CFSG.ComponentClassification.CatalogueBStabilizerFamily
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (familyTransport
  familyTransport_apply)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open scoped Pointwise

section Equivariant

variable {G G' X X' : Type*} [Group G] [Group G']

theorem pointStabilizer_map_equiv (ρ : G →* Equiv.Perm X) (ρ' : G' →* Equiv.Perm X') (e : G ≃* G')
    (φ : X ≃ X') (hcov : ∀ g x, ρ' (e g) (φ x) = φ (ρ g x)) (x : X) :
    (pointStabilizer ρ x).map e.toMonoidHom = pointStabilizer ρ' (φ x) := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_pointStabilizer_iff, mem_pointStabilizer_iff]
  have hh := hcov (e.symm h) x
  rw [MulEquiv.apply_symm_apply] at hh
  rw [hh, φ.injective.eq_iff]

end Equivariant

variable {K : Type} [Field K] {d : ℕ}

abbrev subPerm (A : GL (Fin d) K) : Equiv.Perm (Submodule K (Fin d → K)) :=
  MulAction.toPermHom ((Fin d → K) ≃ₗ[K] (Fin d → K)) (Submodule K (Fin d → K))
    (matrixLinearIso A)

theorem subPerm_apply (A : GL (Fin d) K) (W : Submodule K (Fin d → K)) :
    subPerm A W = W.map (matrixLinearEquiv A).toLinearMap := rfl

theorem subPerm_mul (A A' : GL (Fin d) K) : subPerm (A * A') = subPerm A * subPerm A' := by
  rw [subPerm, subPerm, subPerm, map_mul, map_mul]

theorem map_scalar_eq (c : Kˣ) (W : Submodule K (Fin d → K)) :
    W.map (matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) c)).toLinearMap = W := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rw [LinearEquiv.coe_coe, scalarMatrixLinearEquiv]
    exact W.smul_mem _ hv
  · intro v hv
    refine ⟨((c⁻¹ : Kˣ) : K) • v, W.smul_mem _ hv, ?_⟩
    rw [LinearEquiv.coe_coe, scalarMatrixLinearEquiv, smul_smul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_smul]

variable (Q : QuadraticForm K (Fin d → K))

@[expose] def derivedSubAction : matrixDerived Q →* Equiv.Perm (Submodule K (Fin d → K)) :=
  (MulAction.toPermHom ((Fin d → K) ≃ₗ[K] (Fin d → K)) (Submodule K (Fin d → K))).comp
    (matrixLinearIso.toMonoidHom.comp (matrixDerived Q).subtype)

theorem scalars_le_ker_derivedSubAction :
    (StatedScalars (Fin d) K).subgroupOf (matrixDerived Q) ≤ (derivedSubAction Q).ker := by
  rintro X ⟨c, hc⟩
  rw [MonoidHom.mem_ker]
  refine Equiv.ext fun W => ?_
  change W.map (matrixLinearEquiv X.val).toLinearMap = W
  have hX : X.val = GeneralLinearGroup.scalar (Fin d) c := hc.symm
  rw [hX]
  exact map_scalar_eq c W

@[expose] def subAction : StatedProj (matrixDerived Q) →* Equiv.Perm (Submodule K (Fin d → K)) :=
  QuotientGroup.lift _ (derivedSubAction Q) (scalars_le_ker_derivedSubAction Q)

theorem subAction_proj (X : matrixDerived Q) : subAction Q (projH _ X) = subPerm X.val := rfl

theorem subAction_proj_apply (X : matrixDerived Q) (W : Submodule K (Fin d → K)) :
    subAction Q (projH _ X) W = W.map (matrixLinearEquiv X.val).toLinearMap := rfl

@[expose] def subStab (W : Submodule K (Fin d → K)) : Subgroup (StatedProj (matrixDerived Q)) :=
  pointStabilizer (subAction Q) W

theorem proj_mem_subStab_iff {W : Submodule K (Fin d → K)} (X : matrixDerived Q) :
    projH _ X ∈ subStab Q W ↔ W.map (matrixLinearEquiv X.val).toLinearMap = W := Iff.rfl

theorem subStab_map_conj (x : StatedProj (matrixDerived Q)) (W : Submodule K (Fin d → K)) :
    (subStab Q W).map (MulAut.conj x).toMonoidHom = subStab Q (subAction Q x W) :=
  pointStabilizer_conj _ x W

theorem projectivePointAction_val (x : StatedProj (matrixDerived Q)) (L : Points Q) :
    (projectivePointAction Q x L).val = subAction Q x L.val := by
  obtain ⟨X, rfl⟩ := projH_surjective x
  exact projectivePointAction_mk_submodule Q X L

@[expose] def ptFam : Set (Subgroup (StatedProj (matrixDerived Q))) :=
  {M | ∃ L : Points Q, subStab Q L.val = M}

theorem subStab_mem_ptFam (L : Points Q) : subStab Q L.val ∈ ptFam Q := ⟨L, rfl⟩

theorem projectivePointStabilizer_eq_subStab (L : Points Q) :
    projectivePointStabilizer Q L = subStab Q L.val := by
  ext x
  exact ⟨fun h => (projectivePointAction_val Q x L).symm.trans (congrArg Subtype.val h),
    fun h => Subtype.ext ((projectivePointAction_val Q x L).trans h)⟩

theorem projectivePointFamily_eq_ptFam : projectivePointFamily Q = ptFam Q := by
  ext M
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L, (projectivePointStabilizer_eq_subStab Q L).symm⟩
  · rintro ⟨L, rfl⟩
    exact ⟨L, projectivePointStabilizer_eq_subStab Q L⟩

@[expose] def IsTS (m : ℕ) (W : Submodule K (Fin d → K)) : Prop :=
  Module.finrank K W = m ∧ ∀ v ∈ W, Q v = 0

@[expose] def tsFam : Set (Subgroup (StatedProj (matrixDerived Q))) :=
  {M | ∃ W, IsTS Q 4 W ∧ subStab Q W = M}

theorem subStab_mem_tsFam {W : Submodule K (Fin d → K)} (hW : IsTS Q 4 W) :
    subStab Q W ∈ tsFam Q := ⟨W, hW, rfl⟩

variable {Q}

theorem IsTS.map_similitude {Q' : QuadraticForm K (Fin d → K)} {m : ℕ}
    {W : Submodule K (Fin d → K)} (hW : IsTS Q m W) {S : GL (Fin d) K} {ν : K}
    (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v) :
    IsTS Q' m (W.map (matrixLinearEquiv S).toLinearMap) := by
  refine ⟨by rw [LinearEquiv.finrank_map_eq]; exact hW.1, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  change Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = 0
  rw [hS, hW.2 v hv, mul_zero]

theorem IsTS.map_isometry {m : ℕ} {W : Submodule K (Fin d → K)} (hW : IsTS Q m W)
    {X : GL (Fin d) K} (hX : X ∈ matrixIsometries Q) :
    IsTS Q m (W.map (matrixLinearEquiv X).toLinearMap) :=
  hW.map_similitude (ν := 1) fun v => by
    rw [one_mul]
    exact (mem_matrixIsometries_iff Q X).1 hX v

theorem IsTS.subAction {m : ℕ} {W : Submodule K (Fin d → K)} (hW : IsTS Q m W)
    (x : StatedProj (matrixDerived Q)) : IsTS Q m (subAction Q x W) := by
  obtain ⟨X, rfl⟩ := projH_surjective x
  rw [subAction_proj_apply]
  exact hW.map_isometry (matrixDerived_le_isometries Q X.2)

theorem subStab_map_oκ {g : similarityPairs Q} (hg : g.val.right = 1)
    (W : Submodule K (Fin d → K)) :
    (subStab Q W).map (oκ Q g).toMonoidHom = subStab Q (subPerm g.val.left W) := by
  refine pointStabilizer_map_equiv _ _ (oκ Q g) (subPerm g.val.left) (fun x U => ?_) W
  obtain ⟨X, rfl⟩ := projH_surjective x
  have hX : ((matrixDerivedConjugation Q g X : matrixDerived Q) : GL (Fin d) K) =
      g.val.left * X * g.val.left⁻¹ := by
    rw [matrixDerivedConjugation_val, hg, map_one, MulAut.one_apply]
  rw [kappa_proj, subAction_proj, subAction_proj, hX, ← Equiv.Perm.mul_apply, ← subPerm_mul,
    ← Equiv.Perm.mul_apply, ← subPerm_mul, inv_mul_cancel_right]

section Transport

variable {Q' : QuadraticForm K (Fin d → K)} (S : GL (Fin d) K) (ν : Kˣ)
  (hS : ∀ v, Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * Q v)

theorem subStab_map_oTransport (W : Submodule K (Fin d → K)) :
    (subStab Q W).map (oTransport S ν hS).toMonoidHom = subStab Q' (subPerm S W) := by
  refine pointStabilizer_map_equiv _ _ (oTransport S ν hS) (subPerm S) (fun x U => ?_) W
  obtain ⟨X, rfl⟩ := projH_surjective x
  rw [oTransport_proj, subAction_proj, subAction_proj, coe_derivedTransport,
    ← Equiv.Perm.mul_apply, ← subPerm_mul, ← Equiv.Perm.mul_apply, ← subPerm_mul,
    inv_mul_cancel_right]

@[expose] def pointTransport (L : Points Q) : Points Q' :=
  ⟨subPerm S L.val, by
    rw [subPerm_apply, LinearEquiv.finrank_map_eq]
    exact L.2.1, by
    rintro _ ⟨v, hv, rfl⟩
    change Q' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = 0
    rw [hS, L.2.2 v hv, mul_zero]⟩

theorem pointTransport_val (L : Points Q) : (pointTransport S ν hS L).val = subPerm S L.val := rfl

theorem subPerm_mul_inv (W : Submodule K (Fin d → K)) : subPerm S (subPerm S⁻¹ W) = W := by
  rw [← Equiv.Perm.mul_apply, ← subPerm_mul, mul_inv_cancel, subPerm, map_one, map_one,
    Equiv.Perm.one_apply]

theorem familyTransport_ptFam : familyTransport (oTransport S ν hS) (ptFam Q) = ptFam Q' := by
  ext M
  constructor
  · rintro ⟨_, ⟨L, rfl⟩, rfl⟩
    change (subStab Q L.val).map (oTransport S ν hS).toMonoidHom ∈ ptFam Q'
    rw [subStab_map_oTransport]
    exact subStab_mem_ptFam Q' (pointTransport S ν hS L)
  · rintro ⟨L, rfl⟩
    refine ⟨_, subStab_mem_ptFam Q (pointTransport S⁻¹ ν⁻¹ (inv_similarity S ν hS) L), ?_⟩
    change (subStab Q (subPerm S⁻¹ L.val)).map (oTransport S ν hS).toMonoidHom = _
    rw [subStab_map_oTransport, subPerm_mul_inv]

theorem familyTransport_tsFam : familyTransport (oTransport S ν hS) (tsFam Q) = tsFam Q' := by
  ext M
  constructor
  · rintro ⟨_, ⟨W, hW, rfl⟩, rfl⟩
    change (subStab Q W).map (oTransport S ν hS).toMonoidHom ∈ tsFam Q'
    rw [subStab_map_oTransport]
    exact subStab_mem_tsFam Q' (hW.map_similitude hS)
  · rintro ⟨W, hW, rfl⟩
    refine ⟨_, subStab_mem_tsFam Q (hW.map_similitude (inv_similarity S ν hS)), ?_⟩
    change (subStab Q (subPerm S⁻¹ W)).map (oTransport S ν hS).toMonoidHom = _
    rw [subStab_map_oTransport, subPerm_mul_inv]

end Transport

end CFSG.ComponentClassification.Burgoyne.D4
