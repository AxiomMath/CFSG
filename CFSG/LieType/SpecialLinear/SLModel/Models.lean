module

public import CFSG.LieType.SpecialLinear.SLModel.Basic
public import CFSG.LieType.SpecialLinear.ExteriorModel.Fundamental
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.QuadraticDescent

public section

namespace CFSG.LieType.SpecialLinear.SLModel

open Matrix CFSG.LieType.SpecialLinear.ExteriorModel
  CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open scoped Kronecker

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {m f : ℕ}

omit [CharP k 2] in
theorem frobTwist_eq_comp (r : Fin f) :
    frobTwist F k f r = (algebraMap F k).comp (iterateFrobeniusEquiv F 2 r : F →+* F) := by
  rfl

theorem exists_equiv_single (ε : Fin f → Finset (Fin (m + 1))) {r₀ : Fin f} {j : Fin (m + 1)}
    (h₀ : ε r₀ = {j}) (hrest : ∀ r, r ≠ r₀ → ε r = ∅) :
    ∃ β : BModel k ε ≃ₗ[k] (Set.powersetCard (Fin (m + 1)) j → k), ∀ g v,
      β (slModelRep (F := F) (k := k) ε g v) =
        ((minorMatrix (j : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map
          (iterateFrobeniusEquiv F 2 r₀)).map (algebraMap F k) *ᵥ β v := by
  classical
  have hε : ∀ r, (ε r).card ≤ 1 := by
    intro r
    by_cases hr : r = r₀
    · subst hr
      rw [h₀]
      simp
    · rw [hrest r hr]
      simp
  let e := bIdxEquivSingle ε r₀ j h₀ hrest
  let β : BModel k ε ≃ₗ[k] (Set.powersetCard (Fin (m + 1)) j → k) :=
    (bModelEquivOfCardLeOne (k := k) ε hε).trans (LinearEquiv.funCongrLeft k k e.symm)
  refine ⟨β, ?_⟩
  intro g v
  let H : Fin f → SpecialLinearGroup (Fin (m + 1)) k :=
    fun r => SpecialLinearGroup.map (frobTwist F k f r) g
  let T : Matrix (Set.powersetCard (Fin (m + 1)) j) (Set.powersetCard (Fin (m + 1)) j) k :=
    ((minorMatrix (j : ℕ) (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map
      (iterateFrobeniusEquiv F 2 r₀)).map (algebraMap F k)
  have hH : (fun r => (H r : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) =
      fun r => (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (frobTwist F k f r) := by
    funext r
    rfl
  have hmat : bMat ε (fun r => (H r : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) =
      Matrix.reindex e.symm e.symm T := by
    ext s t
    rw [bMat_apply_of_single ε r₀ j h₀ hrest, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [congrFun hH r₀]
    dsimp only [T]
    change minor ((g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
        (frobTwist F k f r₀)) (e s) (e t) =
      ((minorMatrix (j : ℕ) (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map
        (iterateFrobeniusEquiv F 2 r₀)).map (algebraMap F k) (e s) (e t)
    rw [minor_map]
    simp only [frobTwist_eq_comp, RingHom.comp_apply, Matrix.map_apply, minorMatrix,
      Matrix.of_apply]
    rfl
  change (LinearEquiv.funCongrLeft k k e.symm)
      ((bModelEquivOfCardLeOne (k := k) ε hε) (slModelRep (F := F) (k := k) ε g v)) = _
  rw [slModelRep]
  change (LinearEquiv.funCongrLeft k k e.symm)
      ((bModelEquivOfCardLeOne (k := k) ε hε)
        (bRep ε ((twistHom (frobTwist F k f)) g) v)) = _
  rw [bModelEquivOfCardLeOne_bRep ε hε ((twistHom (frobTwist F k f)) g) v]
  change (LinearEquiv.funCongrLeft k k e.symm)
      ((bMat ε (fun r => (H r : Matrix (Fin (m + 1)) (Fin (m + 1)) k))) *ᵥ
        (bModelEquivOfCardLeOne (k := k) ε hε v)) =
    T *ᵥ (LinearEquiv.funCongrLeft k k e.symm (bModelEquivOfCardLeOne (k := k) ε hε v))
  rw [hmat]
  rw [← Matrix.mulVecLin_apply, ← Matrix.mulVecLin_apply]
  rw [Matrix.mulVecLin_reindex]
  rw [Equiv.symm_symm, ← LinearEquiv.funCongrLeft_symm]
  simp only [LinearMap.comp_apply]
  exact LinearEquiv.symm_apply_apply (LinearEquiv.funCongrLeft k k e) _

theorem exists_equiv_pair (ε : Fin f → Finset (Fin (m + 1))) {r₀ r₁ : Fin f} (hr : r₀ ≠ r₁)
    {j : Fin (m + 1)} (h₀ : ε r₀ = {j}) (h₁ : ε r₁ = {j})
    (hrest : ∀ r, r ≠ r₀ → r ≠ r₁ → ε r = ∅) :
    ∃ β : BModel k ε ≃ₗ[k]
        (Set.powersetCard (Fin (m + 1)) j × Set.powersetCard (Fin (m + 1)) j → k), ∀ g v,
      β (slModelRep (F := F) (k := k) ε g v) =
        ((minorMatrix (j : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map
            (iterateFrobeniusEquiv F 2 r₀) ⊗ₖ
          (minorMatrix (j : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map
            (iterateFrobeniusEquiv F 2 r₁)).map (algebraMap F k) *ᵥ β v := by
  classical
  have hε : ∀ r, (ε r).card ≤ 1 := by
    intro r
    by_cases hr₀ : r = r₀
    · subst hr₀
      rw [h₀]
      simp
    · by_cases hr₁ : r = r₁
      · subst hr₁
        rw [h₁]
        simp
      · rw [hrest r hr₀ hr₁]
        simp
  let e := bIdxEquivPair ε hr j j h₀ h₁ hrest
  let β : BModel k ε ≃ₗ[k]
      (Set.powersetCard (Fin (m + 1)) j × Set.powersetCard (Fin (m + 1)) j → k) :=
    (bModelEquivOfCardLeOne (k := k) ε hε).trans (LinearEquiv.funCongrLeft k k e.symm)
  refine ⟨β, ?_⟩
  intro g v
  let H : Fin f → SpecialLinearGroup (Fin (m + 1)) k :=
    fun r => SpecialLinearGroup.map (frobTwist F k f r) g
  let T : Matrix
      (Set.powersetCard (Fin (m + 1)) j × Set.powersetCard (Fin (m + 1)) j)
      (Set.powersetCard (Fin (m + 1)) j × Set.powersetCard (Fin (m + 1)) j) k :=
    ((minorMatrix (j : ℕ) (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map
        (iterateFrobeniusEquiv F 2 r₀) ⊗ₖ
      (minorMatrix (j : ℕ) (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).map
        (iterateFrobeniusEquiv F 2 r₁)).map (algebraMap F k)
  have hH : (fun r => (H r : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) =
      fun r => (g.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (frobTwist F k f r) := by
    funext r
    rfl
  have hmat : bMat ε (fun r => (H r : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) =
      Matrix.reindex e.symm e.symm T := by
    ext s t
    rw [bMat_apply_of_pair ε hr j j h₀ h₁ hrest,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [congrFun hH r₀, congrFun hH r₁]
    dsimp only [T]
    rw [minor_map, minor_map]
    simp only [Matrix.kroneckerMap_apply, Matrix.map_apply, minorMatrix, Matrix.of_apply,
      map_mul, frobTwist_eq_comp, RingHom.comp_apply]
    rfl
  change (LinearEquiv.funCongrLeft k k e.symm)
      ((bModelEquivOfCardLeOne (k := k) ε hε) (slModelRep (F := F) (k := k) ε g v)) = _
  rw [slModelRep]
  change (LinearEquiv.funCongrLeft k k e.symm)
      ((bModelEquivOfCardLeOne (k := k) ε hε)
        (bRep ε ((twistHom (frobTwist F k f)) g) v)) = _
  rw [bModelEquivOfCardLeOne_bRep ε hε ((twistHom (frobTwist F k f)) g) v]
  change (LinearEquiv.funCongrLeft k k e.symm)
      ((bMat ε (fun r => (H r : Matrix (Fin (m + 1)) (Fin (m + 1)) k))) *ᵥ
        (bModelEquivOfCardLeOne (k := k) ε hε v)) =
    T *ᵥ (LinearEquiv.funCongrLeft k k e.symm (bModelEquivOfCardLeOne (k := k) ε hε v))
  rw [hmat]
  rw [← Matrix.mulVecLin_apply, ← Matrix.mulVecLin_apply]
  rw [Matrix.mulVecLin_reindex]
  rw [Equiv.symm_symm, ← LinearEquiv.funCongrLeft_symm]
  simp only [LinearMap.comp_apply]
  exact LinearEquiv.symm_apply_apply (LinearEquiv.funCongrLeft k k e) _

end CFSG.LieType.SpecialLinear.SLModel
