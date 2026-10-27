module

public import CFSG.CharacterTheory.FrobeniusDeterminant.Core
public import CFSG.CharacterTheory.FrobeniusDeterminant.Center
public import CFSG.CharacterTheory.FrobeniusDeterminant.GenericDet
public import CFSG.CharacterTheory.FrobeniusDeterminant.LinearChange
public import CFSG.CharacterTheory.FrobeniusDeterminant.Norm
public import Mathlib.Algebra.Algebra.Subalgebra.Pi
public import Mathlib.Algebra.Azumaya.Basic
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG

open MvPolynomial Matrix

namespace FrobeniusDeterminant.AW

open scoped BigOperators

abbrev BlockIndex {r : ℕ} (d : Fin r → ℕ) :=
  (i : Fin r) × (Fin (d i) × Fin (d i))

@[expose] noncomputable def flattenMatrixPi {r : ℕ} (d : Fin r → ℕ) :
    ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₗ[ℂ]
      (BlockIndex d → ℂ) where
  toFun A j := A j.1 j.2.1 j.2.2
  invFun f i a b := f ⟨i, (a, b)⟩
  left_inv A := by
    funext i a b
    rfl
  right_inv f := by
    funext j
    rcases j with ⟨i, a, b⟩
    rfl
  map_add' A B := rfl
  map_smul' c A := rfl

@[expose] noncomputable def groupCoeffEquiv (G : Type*) [Fintype G] :
    (G → ℂ) ≃ₗ[ℂ] MonoidAlgebra ℂ G :=
  (Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm.trans
    (MonoidAlgebra.coeffLinearEquiv ℂ).symm

@[expose] noncomputable def awCoord {G : Type*} [Group G] [Fintype G] {r : ℕ}
    {d : Fin r → ℕ}
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) :
    (G → ℂ) ≃ₗ[ℂ] (BlockIndex d → ℂ) :=
  ((groupCoeffEquiv G).trans φ.toLinearEquiv).trans (flattenMatrixPi d)

@[simp] theorem awCoord_apply {G : Type*} [Group G] [Fintype G] {r : ℕ}
    {d : Fin r → ℕ}
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (x : G → ℂ) (j : BlockIndex d) :
    awCoord φ x j = φ (FrobeniusDeterminant.Core.ofFun G x) j.1 j.2.1 j.2.2 := by
  rfl

@[expose] noncomputable def genericBlock {r : ℕ} (d : Fin r → ℕ) (i : Fin r) :
    MvPolynomial (BlockIndex d) ℂ :=
  MvPolynomial.rename (fun ab : Fin (d i) × Fin (d i) => ⟨i, ab⟩)
    (Matrix.mvPolynomialX (Fin (d i)) (Fin (d i)) ℂ).det

@[expose] noncomputable def factor {G : Type*} [Group G] [Fintype G] [DecidableEq G] {r : ℕ}
    {d : Fin r → ℕ}
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (i : Fin r) : MvPolynomial G ℂ :=
  FrobeniusDeterminant.LinearChange.linearAlgEquiv (awCoord φ) (genericBlock d i)

theorem eval_factor {G : Type*} [Group G] [Fintype G] [DecidableEq G] {r : ℕ}
    {d : Fin r → ℕ}
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (i : Fin r) (x : G → ℂ) :
    MvPolynomial.eval x (factor φ i) =
      (φ (FrobeniusDeterminant.Core.ofFun G x) i).det := by
  change MvPolynomial.aeval x
      (FrobeniusDeterminant.LinearChange.linearAlgEquiv (awCoord φ) (genericBlock d i)) = _
  rw [FrobeniusDeterminant.LinearChange.aeval_linearAlgEquiv]
  rw [genericBlock, MvPolynomial.aeval_rename]
  rw [AlgHom.map_det]
  congr 1
  ext a b
  simp [Matrix.mvPolynomialX_apply]

theorem groupDeterminant_factorization {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {r : ℕ} {d : Fin r → ℕ}
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) :
    CFSG.FrobeniusDeterminant.groupDeterminant G =
      MvPolynomial.C (Equiv.Perm.sign (FrobeniusDeterminant.Core.invPerm G) : ℂ) *
        ∏ i, factor φ i ^ d i := by
  apply MvPolynomial.funext
  intro x
  rw [FrobeniusDeterminant.Core.eval_groupDeterminant]
  rw [← Algebra.norm_eq_of_algEquiv φ (FrobeniusDeterminant.Core.ofFun G x)]
  rw [FrobeniusDeterminant.Norm.norm_pi_fin]
  simp_rw [FrobeniusDeterminant.Norm.norm_matrix_complex]
  simp [eval_factor]

@[expose] noncomputable def centerLinearEquiv {A B : Type*} [Ring A] [Ring B]
    [Algebra ℂ A] [Algebra ℂ B] (e : A ≃ₐ[ℂ] B) :
    Subalgebra.center ℂ A ≃ₗ[ℂ] Subalgebra.center ℂ B where
  toFun z := ⟨e z.1, by
    rw [Subalgebra.mem_center_iff]
    intro b
    have hz := (Subalgebra.mem_center_iff.mp z.2) (e.symm b)
    simpa using congrArg e hz⟩
  invFun z := ⟨e.symm z.1, by
    rw [Subalgebra.mem_center_iff]
    intro a
    have hz := (Subalgebra.mem_center_iff.mp z.2) (e a)
    simpa using congrArg e.symm hz⟩
  left_inv z := by
    apply Subtype.ext
    exact e.symm_apply_apply z.1
  right_inv z := by
    apply Subtype.ext
    exact e.apply_symm_apply z.1
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact e.toLinearEquiv.map_smul c x.1

@[expose] noncomputable def matrixPiCenterEquiv {r : ℕ} (d : Fin r → ℕ)
    [∀ i, NeZero (d i)] :
    Subalgebra.center ℂ
        ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₗ[ℂ]
      (Fin r → ℂ) where
  toFun z i := z.1 i 0 0
  invFun f := ⟨fun i => Matrix.scalar (Fin (d i)) (f i), by
    rw [Subalgebra.mem_center_iff]
    intro y
    funext i
    exact (Matrix.scalar_commute (f i)
      (fun r' : ℂ => show Commute (f i) r' from mul_comm (f i) r')
      (y i)).eq.symm⟩
  left_inv z := by
    apply Subtype.ext
    funext i a b
    change Matrix.scalar (Fin (d i)) (z.1 i 0 0) a b = z.1 i a b
    have hz : z.1 ∈ Subalgebra.pi Set.univ
        (fun i : Fin r => Subalgebra.center ℂ
          (Matrix (Fin (d i)) (Fin (d i)) ℂ)) := by
      rw [← Subalgebra.center_pi]
      exact z.2
    have hi : z.1 i ∈ Subalgebra.center ℂ
        (Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
      exact hz i (Set.mem_univ i)
    obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff ℂ).mp hi
    have hc' : z.1 i = Matrix.scalar (Fin (d i)) c := by
      calc
        z.1 i = (algebraMap ℂ
          (Matrix (Fin (d i)) (Fin (d i)) ℂ)) c := hc
        _ = Matrix.scalar (Fin (d i)) c := by
          ext u v
          by_cases huv : u = v <;>
            simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, huv]
    have h00 : z.1 i 0 0 = c := by
      rw [hc']
      simp
    rw [h00]
    exact (congrFun (congrFun hc' a) b).symm
  right_inv f := by
    funext i
    simp
  map_add' x y := by
    funext i
    rfl
  map_smul' c x := by
    funext i
    rfl

theorem wedderburn_count {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {r : ℕ} {d : Fin r → ℕ} [∀ i, NeZero (d i)]
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) :
    r = Nat.card (ConjClasses G) := by
  rw [← FrobeniusDeterminant.Center.finrank_center_eq_card_conjClasses G]
  rw [LinearEquiv.finrank_eq (centerLinearEquiv φ)]
  rw [LinearEquiv.finrank_eq (matrixPiCenterEquiv d)]
  simp

theorem genericBlock_irreducible {r : ℕ} {d : Fin r → ℕ}
    [∀ i, NeZero (d i)] (i : Fin r) :
    Irreducible (genericBlock d i) := by
  apply FrobeniusDeterminant.irreducible_rename_of_injective
  · intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · exact FrobeniusDeterminant.genericDet_irreducible (d i) (NeZero.pos _)

theorem genericBlock_isHomogeneous {r : ℕ} {d : Fin r → ℕ}
    (i : Fin r) : (genericBlock d i).IsHomogeneous (d i) := by
  rw [genericBlock]
  apply (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff ?_).2
  · simpa using FrobeniusDeterminant.genericDet_isHomogeneous (Fin (d i)) ℂ
  · intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

theorem factor_irreducible {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {r : ℕ} {d : Fin r → ℕ} [∀ i, NeZero (d i)]
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) (i : Fin r) :
    Irreducible (factor φ i) := by
  exact (FrobeniusDeterminant.LinearChange.irreducible_linearAlgEquiv_iff
    (awCoord φ) (genericBlock d i)).2 (genericBlock_irreducible i)

theorem factor_isHomogeneous {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {r : ℕ} {d : Fin r → ℕ}
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) (i : Fin r) :
    (factor φ i).IsHomogeneous (d i) := by
  change (MvPolynomial.aeval
    (FrobeniusDeterminant.LinearChange.linearVar (awCoord φ)) (genericBlock d i)).IsHomogeneous (d i)
  simpa using (genericBlock_isHomogeneous i).aeval
    (FrobeniusDeterminant.LinearChange.linearVar (awCoord φ))
    (fun k => FrobeniusDeterminant.LinearChange.linearVar_isHomogeneous (awCoord φ) k)

theorem factor_totalDegree {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {r : ℕ} {d : Fin r → ℕ} [∀ i, NeZero (d i)]
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) (i : Fin r) :
    (factor φ i).totalDegree = d i :=
  (factor_isHomogeneous φ i).totalDegree (factor_irreducible φ i).ne_zero

private noncomputable def blockSpecialize {r : ℕ} (d : Fin r → ℕ)
    (j : Fin r) : BlockIndex d → ℂ :=
  fun k => if h : k.1 = j then
    if k.2.1 = cast (by rw [h]) k.2.2 then 1 else 0
  else 0

private lemma eval_genericBlock_blockSpecialize_same {r : ℕ}
    {d : Fin r → ℕ} [∀ i, NeZero (d i)] (j : Fin r) :
    MvPolynomial.eval (blockSpecialize d j) (genericBlock d j) = 1 := by
  rw [genericBlock, MvPolynomial.eval_rename,
    Matrix.eval_det_mvPolynomialX]
  have hmatrix : Matrix.of (fun a b =>
      blockSpecialize d j ⟨j, (a, b)⟩) = (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) := by
    ext a b
    simp [blockSpecialize, Matrix.one_apply]
  change (Matrix.of (fun a b =>
    blockSpecialize d j ⟨j, (a, b)⟩)).det = 1
  rw [hmatrix, Matrix.det_one]

private lemma eval_genericBlock_blockSpecialize_ne {r : ℕ}
    {d : Fin r → ℕ} [∀ i, NeZero (d i)] {i j : Fin r} (hij : i ≠ j) :
    MvPolynomial.eval (blockSpecialize d j) (genericBlock d i) = 0 := by
  rw [genericBlock, MvPolynomial.eval_rename,
    Matrix.eval_det_mvPolynomialX]
  have hmatrix : Matrix.of (fun a b =>
      blockSpecialize d j ⟨i, (a, b)⟩) = (0 : Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
    ext a b
    simp [blockSpecialize, hij]
  change (Matrix.of (fun a b =>
    blockSpecialize d j ⟨i, (a, b)⟩)).det = 0
  rw [hmatrix, Matrix.det_zero]

theorem genericBlock_not_associated {r : ℕ} {d : Fin r → ℕ}
    [∀ i, NeZero (d i)] {i j : Fin r} (hij : i ≠ j) :
    ¬Associated (genericBlock d i) (genericBlock d j) := by
  intro h
  have hm := h.map (MvPolynomial.eval (blockSpecialize d j))
  have hn := hm.ne_zero_iff
  rw [eval_genericBlock_blockSpecialize_ne hij,
    eval_genericBlock_blockSpecialize_same] at hn
  exact (hn.mpr one_ne_zero) rfl

theorem factor_not_associated {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] {r : ℕ} {d : Fin r → ℕ} [∀ i, NeZero (d i)]
    (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ]
      ((i : Fin r) → Matrix (Fin (d i)) (Fin (d i)) ℂ))
    {i j : Fin r} (hij : i ≠ j) :
    ¬Associated (factor φ i) (factor φ j) := by
  intro h
  have hm := h.map (FrobeniusDeterminant.LinearChange.linearAlgEquiv (awCoord φ)).symm
  apply genericBlock_not_associated (d := d) hij
  simpa [factor] using hm

end FrobeniusDeterminant.AW

end CFSG
