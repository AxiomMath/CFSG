module

public import CFSG.HardMathSupport.U4FF.ClassDatumDefs
public import CFSG.HardMathSupport.U4FF.ClassWeyl

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)

namespace Datum

section Pmat

variable {K : Type} [Field K]

@[expose] def pmat (π : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if i = π j then 1 else 0

theorem pmat_apply (π : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    (pmat π : Matrix (Fin 4) (Fin 4) K) i j = if i = π j then 1 else 0 := rfl

theorem pmat_mul (π τ : Equiv.Perm (Fin 4)) :
    (pmat π : Matrix (Fin 4) (Fin 4) K) * pmat τ = pmat (π * τ) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ j)]
  · by_cases h : i = π (τ j) <;> simp [pmat_apply, h]
  · intro k _ hk
    rw [pmat_apply τ k j, if_neg hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pmat_one : (pmat 1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [pmat_apply, Matrix.one_apply, h]

theorem pmat_mul_mul_apply (π τ : Equiv.Perm (Fin 4)) (M : Matrix (Fin 4) (Fin 4) K)
    (i j : Fin 4) :
    ((pmat π : Matrix (Fin 4) (Fin 4) K) * M * (pmat τ : Matrix (Fin 4) (Fin 4) K)) i j =
      M (π⁻¹ i) (τ j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ j)]
  · rw [pmat_apply τ (τ j) j, if_pos rfl, mul_one, Matrix.mul_apply,
      Finset.sum_eq_single (π⁻¹ i)]
    · rw [pmat_apply π i (π⁻¹ i), if_pos (by simp), one_mul]
    · intro k _ hk
      rw [pmat_apply π i k, if_neg, zero_mul]
      intro h
      apply hk
      rw [h]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro l _ hl
    rw [pmat_apply τ l j, if_neg hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pmat_transpose (π : Equiv.Perm (Fin 4)) :
    (pmat π : Matrix (Fin 4) (Fin 4) K)ᵀ = pmat π⁻¹ := by
  ext i j
  rw [Matrix.transpose_apply, pmat_apply, pmat_apply]
  have : (j = π i) ↔ (i = π⁻¹ j) := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  simp only [this]

theorem antidiag_eq_pmat : (antidiag 4 : Matrix (Fin 4) (Fin 4) K) = pmat Fin.revPerm := by
  ext i j
  rw [pmat_apply]
  simp only [antidiag, of_apply, Fin.revPerm_apply]
  have : (j = Fin.rev i) ↔ (i = Fin.rev j) := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  simp only [this]

@[expose] def permGL (π : Equiv.Perm (Fin 4)) : GL (Fin 4) K :=
  ⟨pmat π, pmat π⁻¹, by rw [pmat_mul, mul_inv_cancel, pmat_one],
    by rw [pmat_mul, inv_mul_cancel, pmat_one]⟩

theorem pmat_eq_permMatrix (π : Equiv.Perm (Fin 4)) :
    (pmat π : Matrix (Fin 4) (Fin 4) K) = (π⁻¹).permMatrix K := by
  ext i j
  simp only [pmat_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  have : (i = π j) ↔ (π⁻¹ i = j) := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [← h]
      simp
  simp only [this]

end Pmat

section PermSU

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem det_pmat (π : Equiv.Perm (Fin 4)) : (pmat π : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [pmat_eq_permMatrix, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π⁻¹) with h | h
  · rw [h]
    simp
  · rw [h]
    simp [CharTwo.neg_eq]

theorem conjTr_pmat (π : Equiv.Perm (Fin 4)) :
    conjTr (unitaryInvolution K 2 n) (pmat π : Matrix (Fin 4) (Fin 4) K) = pmat π⁻¹ := by
  have h : (pmat π : Matrix (Fin 4) (Fin 4) K).map (unitaryInvolution K 2 n) = pmat π := by
    ext i j
    simp only [Matrix.map_apply, pmat_apply]
    split_ifs <;> simp
  rw [conjTr, h, pmat_transpose]

theorem permGL_mem_SU {π : Equiv.Perm (Fin 4)} (hπ : ∀ i, π (Fin.rev i) = Fin.rev (π i)) :
    (permGL π : GL (Fin 4) K) ∈ SU (unitaryInvolution K 2 n) 4 := by
  refine mem_SU.mpr ⟨det_pmat π, ?_⟩
  show conjTr (unitaryInvolution K 2 n) (pmat π : Matrix (Fin 4) (Fin 4) K) * antidiag 4 *
    pmat π = antidiag 4
  rw [conjTr_pmat, antidiag_eq_pmat, pmat_mul, pmat_mul]
  congr 1
  ext i
  simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply]
  rw [← hπ i]
  simp

@[expose] def permG (π : Equiv.Perm (Fin 4)) (hπ : ∀ i, π (Fin.rev i) = Fin.rev (π i)) :
    G4 K n :=
  ⟨permGL π, permGL_mem_SU hπ⟩

end PermSU

end Datum

section WeylReps

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem permOf_comm_rev (w : WB) (i : Fin 4) :
    permOf w (Fin.rev i) = Fin.rev (permOf w i) := by
  obtain ⟨j, rfl⟩ := exists_wTab w
  rw [permOf_wTab]
  revert j i
  decide

@[expose] noncomputable def nHom (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    WB →* G4 K n where
  toFun w := Datum.permG (permOf w) (permOf_comm_rev w)
  map_one' := by
    apply eq_of_gm_eq
    show Datum.pmat (permOf 1) = 1
    rw [map_one]
    exact Datum.pmat_one
  map_mul' w w' := by
    apply eq_of_gm_eq
    rw [gm_mul]
    show Datum.pmat (permOf (w * w')) = Datum.pmat (permOf w) * Datum.pmat (permOf w')
    rw [map_mul, Datum.pmat_mul]

variable {n : ℕ}

theorem gm_nHom (w : WB) : gm (nHom K n w) = Datum.pmat (permOf w) := rfl

theorem nHom_inv (w : WB) : (nHom K n w)⁻¹ = nHom K n w⁻¹ := (map_inv (nHom K n) w).symm

theorem gm_nHom_conj (v w : WB) (g : G4 K n) (i j : Fin 4) :
    gm (nHom K n v * g * nHom K n w) i j = gm g ((permOf v)⁻¹ i) (permOf w j) := by
  rw [gm_mul, gm_mul, gm_nHom, gm_nHom]
  exact Datum.pmat_mul_mul_apply _ _ _ i j

theorem gm_nHom_conj_inv (w : WB) (g : G4 K n) (i j : Fin 4) :
    gm ((nHom K n w)⁻¹ * g * nHom K n w) i j = gm g (permOf w i) (permOf w j) := by
  rw [nHom_inv, gm_nHom_conj, map_inv]
  simp

theorem nHom_w0 : nHom K n w0 = jSU K n := by
  apply eq_of_gm_eq
  rw [gm_nHom, gm_jSU, permOf_w0, Datum.antidiag_eq_pmat]

end WeylReps

end CFSG.HardMathSupport.U4FF
