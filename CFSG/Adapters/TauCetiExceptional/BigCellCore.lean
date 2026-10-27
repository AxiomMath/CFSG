module

public import CFSG.Adapters.TauCetiExceptional.BigCellLDU
public import Mathlib.RingTheory.Localization.Away.Basic

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open MvPolynomial

variable {n : ℕ}

@[expose] def coordMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
  Matrix.of fun i j => X (i, j)

@[expose] def evalMat {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A) :
    MvPolynomial (Fin n × Fin n) ℤ →+* A :=
  eval₂Hom (Int.castRingHom A) fun ij => M ij.1 ij.2

theorem evalMat_X {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    evalMat M (X (i, j)) = M i j :=
  eval₂Hom_X' _ _ _

theorem mapMatrix_evalMat_coordMatrix {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A) :
    (evalMat M).mapMatrix (coordMatrix n) = M := by
  ext i j
  exact evalMat_X M i j

theorem evalMat_bigCellDet {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A) :
    evalMat M (bigCellDet (coordMatrix n)) = bigCellDet M := by
  rw [map_bigCellDet, mapMatrix_evalMat_coordMatrix]

theorem evalMat_mapMatrix {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (M : Matrix (Fin n) (Fin n) A) : evalMat (f.mapMatrix M) = f.comp (evalMat M) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [evalMat]
  · intro ij
    simp only [RingHom.comp_apply, evalMat, eval₂Hom_X']
    rfl

theorem exists_ringHom_mapMatrix_eq {R K A : Type*} [CommRing R] [CommRing K] [CommRing A]
    (g : Matrix (Fin n) (Fin n) R) (hunit : IsUnit (bigCellDet g))
    (hgen : ∀ T : Subring R, (∀ i j, g i j ∈ T) → (∃ y ∈ T, y * bigCellDet g = 1) → T = ⊤)
    (S : Set (Matrix (Fin n) (Fin n) K))
    (hS : ∀ z ∈ S, bigCellDet z ≠ 0 → ∃ φ : R →+* K, φ.mapMatrix g = z)
    (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ P : MvPolynomial (Fin n × Fin n) ℤ, (∀ z ∈ S, evalMat z P = 0) → evalMat M P = 0)
    (hMunit : IsUnit (bigCellDet M)) :
    ∃ ψ : R →+* A, ψ.mapMatrix g = M := by
  set δ := bigCellDet (coordMatrix n)
  let 𝒜 := Localization.Away δ
  have hg : IsUnit (evalMat g δ) := by rwa [evalMat_bigCellDet]
  have hMδ : IsUnit (evalMat M δ) := by rwa [evalMat_bigCellDet]
  let eg : 𝒜 →+* R := IsLocalization.Away.lift δ hg
  let eM : 𝒜 →+* A := IsLocalization.Away.lift δ hMδ
  have heg : ∀ P, eg (algebraMap _ 𝒜 P) = evalMat g P := IsLocalization.Away.lift_eq δ hg
  have heM : ∀ P, eM (algebraMap _ 𝒜 P) = evalMat M P := IsLocalization.Away.lift_eq δ hMδ
  have hsurj : Function.Surjective eg := by
    have htop := hgen eg.range (fun i j => ⟨algebraMap _ 𝒜 (X (i, j)), by rw [heg, evalMat_X]⟩)
      ⟨eg (IsLocalization.Away.invSelf δ), ⟨_, rfl⟩, by
        rw [← evalMat_bigCellDet, ← heg, ← map_mul, mul_comm,
          IsLocalization.Away.mul_invSelf, map_one]⟩
    intro r
    have hr : r ∈ eg.range := htop ▸ Subring.mem_top r
    exact hr
  have hker : RingHom.ker eg ≤ RingHom.ker eM := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    obtain ⟨k, P, hP⟩ := IsLocalization.Away.surj δ F
    have hgP : evalMat g P = 0 := by
      rw [← heg, ← hP, map_mul, hF, zero_mul]
    have hMP : evalMat M P = 0 := by
      have h := hM (δ * P) fun z hz => by
        rw [map_mul, evalMat_bigCellDet]
        by_cases hz0 : bigCellDet z = 0
        · rw [hz0, zero_mul]
        · obtain ⟨φ, rfl⟩ := hS z hz hz0
          rw [evalMat_mapMatrix, RingHom.comp_apply, hgP, map_zero, mul_zero]
      rw [map_mul] at h
      exact (hMδ.mul_right_eq_zero).1 h
    have h2 := congrArg eM hP
    rw [map_mul, heM, hMP, map_pow, heM] at h2
    exact ((hMδ.pow k).mul_left_eq_zero).1 h2
  refine ⟨eg.liftOfSurjective hsurj ⟨eM, hker⟩, ?_⟩
  ext i j
  change (eg.liftOfSurjective hsurj ⟨eM, hker⟩) (g i j) = M i j
  rw [← evalMat_X g i j, ← heg, RingHom.liftOfSurjective_comp_apply]
  change eM _ = _
  rw [heM, evalMat_X]

end CFSG.TauCetiBridge.BigCell
