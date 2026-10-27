module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Alt4
public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Equiv Matrix CFSG.Open

variable {K : Type} [Field K]

@[expose] noncomputable def permGL (n : ℕ) (K : Type) [Field K] : Perm (Fin n) →* GL (Fin n) K :=
  MonoidHom.toHomUnits (Matrix.permMatrixHom (n := Fin n) (R := K))

theorem coe_permGL {n : ℕ} (σ : Perm (Fin n)) :
    ((permGL n K σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = σ⁻¹.permMatrix K := rfl

theorem det_permGL {n : ℕ} (σ : Perm (Fin n)) :
    ((permGL n K σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = Perm.sign σ := by
  rw [coe_permGL, Matrix.det_permutation, map_inv, Int.units_inv_eq_self]

theorem eq_one_of_permGL_scalar {n : ℕ} {σ : Perm (Fin n)} {c : Kˣ}
    (h : permGL n K σ = Matrix.GeneralLinearGroup.scalar (Fin n) c) : σ = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  have h1 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (σ i) i) h
  simp only [coe_permGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hi] at h1
  simp [Perm.permMatrix, PEquiv.toMatrix_apply] at h1

theorem threeTwoWitness_statedProj_perm {n : ℕ} (hn : 4 ≤ n) {H : Subgroup (GL (Fin n) K)}
    (hH : ∀ σ : Perm (Fin n), Perm.sign σ = 1 → permGL n K σ ∈ H) :
    ThreeTwoWitness (CFSG.Open.StatedProj H) := by
  let ι : Fin 4 ↪ Fin n := Fin.castLEEmb hn
  let φ0 : alternatingGroup (Fin 4) →* Perm (Fin n) :=
    (Perm.viaEmbeddingHom ι).comp (alternatingGroup (Fin 4)).subtype
  have hsign : ∀ a : alternatingGroup (Fin 4), Perm.sign (φ0 a) = 1 := by
    intro a
    have h1 : Perm.sign (a : Perm (Fin 4)) = 1 := Perm.mem_alternatingGroup.1 a.2
    classical
    change Perm.sign (Perm.viaEmbedding (a : Perm (Fin 4)) ι) = 1
    rw [Perm.viaEmbedding, Perm.sign_extendDomain]
    exact h1
  have hmem : ∀ a, (permGL n K).comp φ0 a ∈ H := fun a => hH _ (hsign a)
  let φ1 : alternatingGroup (Fin 4) →* H := ((permGL n K).comp φ0).codRestrict H hmem
  let ψ : alternatingGroup (Fin 4) →* CFSG.Open.StatedProj H := (QuotientGroup.mk' _).comp φ1
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : QuotientGroup.mk (φ1 a) = (1 : CFSG.Open.StatedProj H) := ha
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 : φ0 a = 1 := eq_one_of_permGL_scalar (σ := φ0 a) (c := c) hc.symm
    have h3 : (a : Perm (Fin 4)) = 1 :=
      Perm.viaEmbeddingHom_injective ι (by rw [map_one]; exact h2)
    exact Subtype.ext h3
  exact ThreeTwoWitness.of_injective ψ hinj threeTwoWitness_alt_four

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
