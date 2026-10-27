module

public import CFSG.LieType.AlgebraicGroups.TorusCoordinates
public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding
public import CFSG.LinearAlgebra.TorusPrimeTorsion
public import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

public noncomputable section

open CategoryTheory WithConv TauCeti
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

def diagonalCharacterHom
    (T : FiniteTypeCommHopfAlgCat.{u,u} k) {n : ℕ}
    (c : Fin n → _root_.GroupLike k T) :
    WithConv (T →ₐ[k] k) →* (Fin n → kˣ) := by
  let E := DiagonalizableGroup.pointsMulEquiv
    (R := k) (G := _root_.GroupLike k T) (A := k)
  let a := TauCeti.GroupLike.evaluationBialgHom k T
  exact
    { toFun := fun t i => E (AlgHom.mapDomain a t) (c i)
      map_one' := by
        have h : E (AlgHom.mapDomain a (1 : WithConv (T →ₐ[k] k))) = 1 := by
          rw [map_one, map_one]
        exact congrArg (fun χ => fun i => χ (c i)) h
      map_mul' := by
        intro t s
        have h : E (AlgHom.mapDomain a (t * s)) =
            E (AlgHom.mapDomain a t) * E (AlgHom.mapDomain a s) := by
          rw [map_mul, map_mul]
        exact congrArg (fun χ => fun i => χ (c i)) h }

omit [IsAlgClosed k] in
@[simp] theorem diagonalCharacterHom_apply_val
    (T : FiniteTypeCommHopfAlgCat.{u,u} k) {n : ℕ}
    (c : Fin n → _root_.GroupLike k T)
    (t : WithConv (T →ₐ[k] k)) (i : Fin n) :
    (diagonalCharacterHom T c t i : k) = t.ofConv (c i) := by
  let a := TauCeti.GroupLike.evaluationBialgHom k T
  change ((DiagonalizableGroup.pointsMulEquiv (AlgHom.mapDomain a t)) (c i) : k) = _
  rw [DiagonalizableGroup.pointsMulEquiv_apply, DiagonalizableGroup.charOfPoint_apply_coe]
  rw [AlgHom.mapDomain_apply]
  change t.ofConv (a (MonoidAlgebra.single (c i) 1)) = t.ofConv (c i)
  rw [TauCeti.GroupLike.evaluationBialgHom_single, one_smul]

theorem exists_finite_diagonal_character_detector
    (T : FiniteTypeCommHopfAlgCat.{u,u} k) (hT : torusCommHopfAlgProperty k T)
    {n : ℕ} (c : Fin n → _root_.GroupLike k T) {p : ℕ}
    (hp : p.Prime) (hpk : (p : k) ≠ 0) :
    ∃ (e : ℕ) (F : Subgroup (WithConv (T →ₐ[k] k))),
      0 < e ∧ Finite F ∧ (Nat.card F : k) ≠ 0 ∧
      (∀ t, t ∈ F ↔ t ^ (p ^ e) = 1) ∧
      ∀ M : Matrix (Fin n) (Fin n) k,
        (∀ t ∈ F, Matrix.diagonal (fun i => t.ofConv (c i)) * M =
          M * Matrix.diagonal (fun i => t.ofConv (c i))) ↔
        (∀ t : WithConv (T →ₐ[k] k), Matrix.diagonal (fun i => t.ofConv (c i)) * M =
          M * Matrix.diagonal (fun i => t.ofConv (c i))) := by
  classical
  obtain ⟨r, ⟨a⟩⟩ := exists_coordinateEquiv_of_torus T hT
  let E := AlgHom.mapDomainMulEquiv (A := k) a
  let c' : Fin n → _root_.GroupLike k (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) :=
    fun i => TauCeti.GroupLike.map a.symm.toBialgHom (c i)
  let : Comodule k (MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) (Fin n → k) :=
    Comodule.ofGroupLike (Pi.basisFun k (Fin n)) (fun i => (c' i).val)
      (fun i => (c' i).isGroupLikeElem_val)
  obtain ⟨e, F0, he, hfin, hcard, hmem, hfix, hcomm⟩ :=
    CFSG.LinearAlgebra.exists_primePower_basePointsRepresentation_detector
      (K := k) (r := r) (V := Fin n → k) hp hpk
  let S := SplitTorus.pointsMulEquiv (R := k) (A := k) (σ := Fin r)
  let E' : WithConv (T →ₐ[k] k) ≃* (Fin r → kˣ) := E.trans S
  let F := F0.comap E'.toMonoidHom
  have hF : F = F0.comap E'.toMonoidHom := rfl
  let : Finite F0 := hfin
  let eF : F ≃* F0 :=
    { toFun := fun t => ⟨E' t.val, t.property⟩
      invFun := fun s => ⟨E'.symm s.val, by
        change E' (E'.symm s.val) ∈ F0
        simp⟩
      left_inv := fun t => Subtype.ext (E'.symm_apply_apply t.val)
      right_inv := fun s => Subtype.ext (E'.apply_symm_apply s.val)
      map_mul' := fun t s => Subtype.ext (E'.map_mul t.val s.val) }
  have hfinite : Finite F := Finite.of_equiv F0 eF.toEquiv.symm
  have hcardF : Nat.card F = (p ^ e) ^ r := by
    rw [Nat.card_congr eF.toEquiv, hcard]
  have hmK : (Nat.card F : k) ≠ 0 := by
    rw [hcardF, Nat.cast_pow, Nat.cast_pow]
    exact pow_ne_zero r (pow_ne_zero e hpk)
  have hFm (t) : t ∈ F ↔ t ^ (p ^ e) = 1 := by
    change E' t ∈ F0 ↔ _
    rw [hmem, ← map_pow, ← map_one E']
    exact E'.injective.eq_iff
  have haction (t : WithConv (T →ₐ[k] k)) :
      LinearMap.toMatrixAlgEquiv (Pi.basisFun k (Fin n))
        (Comodule.basePointsRepresentation
          (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) (Fin n → k) (E t)) =
        Matrix.diagonal (fun i => t.ofConv (c i)) := by
    have hcodiag := Comodule.coefficientMatrix_ofGroupLike
      (Pi.basisFun k (Fin n)) (fun i => (c' i).val)
      (fun i => (c' i).isGroupLikeElem_val)
    have heval : LinearMap.toMatrixAlgEquiv (Pi.basisFun k (Fin n))
        (Comodule.basePointsRepresentation
          (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) (Fin n → k) (E t)) =
        (Comodule.coefficientMatrix (C := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)))
          (Pi.basisFun k (Fin n))).map (E t).ofConv := by
      have h := pointsMulEquiv_coordinateBialgHom_eq_toMatrix (Pi.basisFun k (Fin n)) (E t)
      rw [TauCeti.AlgHom.mapDomain_apply, AlgHom.pointsMulEquiv_comp_coordinateBialgHom] at h
      exact h.symm
    rw [heval, hcodiag]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.map_apply, Matrix.diagonal_apply_eq]
      have hE : (E t).ofConv (c' i) = t.ofConv (a (a.symm (c i))) := by
        simp only [E, c', AlgHom.mapDomainMulEquiv_apply,
          TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
          TauCeti.GroupLike.val_map]
        change t.ofConv (a (a.symm (c i))) = t.ofConv (a (a.symm (c i)))
        rfl
      rw [hE, a.apply_symm_apply]
    · simp only [Matrix.map_apply, Matrix.diagonal_apply_ne _ hij, map_zero]
  refine ⟨e, F, he, hfinite, hmK, hFm, ?_⟩
  intro M
  let L := (LinearMap.toMatrixAlgEquiv (Pi.basisFun k (Fin n))).symm M
  have hL (t : WithConv (T →ₐ[k] k)) :
      Matrix.diagonal (fun i => t.ofConv (c i)) * M =
        M * Matrix.diagonal (fun i => t.ofConv (c i)) ↔
      L.comp (Comodule.basePointsRepresentation
          (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) (Fin n → k) (E t)) =
        (Comodule.basePointsRepresentation
          (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) (Fin n → k) (E t)).comp L := by
    rw [← haction t]
    let D := LinearMap.toMatrixAlgEquiv (Pi.basisFun k (Fin n))
    have hDL : D L = M := D.apply_symm_apply M
    rw [← hDL, ← map_mul, ← map_mul, D.injective.eq_iff]
    exact eq_comm
  constructor
  · intro h t
    apply (hL t).mpr
    have hcommL := hcomm L
    change ((∀ s ∈ F0, L.comp (Comodule.basePointsRepresentation
      (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) (Fin n → k) (S.symm s)) =
      (Comodule.basePointsRepresentation (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)))
        (Fin n → k) (S.symm s)).comp L) ↔
      ∀ s : Fin r → kˣ, L.comp (Comodule.basePointsRepresentation
        (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ))) (Fin n → k) (S.symm s)) =
        (Comodule.basePointsRepresentation (H := MonoidAlgebra k (Multiplicative (Fin r →₀ ℤ)))
          (Fin n → k) (S.symm s)).comp L) at hcommL
    have hall := hcommL.mp ?_
    · have hEt : S.symm (E' t) = E t := S.symm_apply_apply (E t)
      simpa only [hEt] using hall (E' t)
    · intro s hs
      let t := E'.symm s
      have ht : t ∈ F := by
        change E' (E'.symm s) ∈ F0
        simpa using hs
      have hEt : S.symm s = E t := by
        apply S.injective
        rw [S.apply_symm_apply]
        change s = E' (E'.symm s)
        exact (E'.apply_symm_apply s).symm
      simpa only [hEt] using (hL t).mp (h t ht)
  · intro h t ht
    exact h t

end CFSG.LieType.AlgebraicGroups
