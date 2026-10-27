module

public import CFSG.Adapters.TauCetiExceptional.MinusculeAd
public import CFSG.Adapters.TauCetiExceptional.BigCellCore
public import CFSG.Adapters.TauCetiExceptional.BigCellNative

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule MinData
open CFSG.TauCetiBridge.BigCell (evalMat coordMatrix mapMatrix_evalMat_coordMatrix)

variable {τ : Tag} (D : MinData τ) (S : AdjSigns τ)

@[expose] def adjMat : Label τ → Matrix (Fin D.d) (Fin D.d) ℤ
  | .inl k => Matrix.diagonal fun a : Fin D.d => S.epsZ k * D.wt a k
  | .inr β => Matrix.of fun i j => S.sRoot β.1 * rootMat D β.1 i j

theorem natMat_adjMap_single
    (R : Type*) [CommRing R] (l : Label τ) :
    natMat R (adjMap R S D (Finsupp.single l 1)) = (adjMat D S l).map (Int.cast : ℤ → R) := by
  rcases l with k | ⟨β, hβ⟩
  · rw [show (Finsupp.single (Sum.inl k) 1 : RootModule τ R) = hVec τ R k from rfl,
      adjMap_hVec, map_smul, natMat_cartanOp]
    ext i j
    by_cases h : i = j
    · subst h
      simp [adjMat]
    · simp [adjMat, Matrix.diagonal_apply_ne _ h]
  · rw [← rootVec_eq_single R hβ, adjMap_rootVec, map_smul, natMat_rootOp]
    ext i j
    simp [adjMat]

variable {D S}

@[expose] def projMat
    {R : Type*} [CommRing R] (N : Matrix (Fin D.d) (Fin D.d) R) :
    Matrix (Fin D.d) (Fin D.d) R :=
  ∑ l : Label τ, matCoord D R S N l • (adjMat D S l).map (Int.cast : ℤ → R)

theorem natMat_adjMap_adjInv
    {R : Type*} [CommRing R] (X : Module.End R (Fin D.d →₀ R)) :
    natMat R (adjMap R S D (adjInv R S D X)) = projMat (S := S) (natMat R X) := by
  have e : adjInv R S D X = ∑ l : Label τ, matCoord D R S (natMat R X) l • Finsupp.single l 1 := by
    ext l'
    rw [adjInv_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single l']
    · rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    · intro l _ hl
      rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne hl.symm, smul_zero]
    · simp
  rw [e, map_sum, map_sum, projMat]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, natMat_adjMap_single]

theorem mapMatrix_projMat
    {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (N : Matrix (Fin D.d) (Fin D.d) R) :
    f.mapMatrix (projMat (S := S) N) = projMat (S := S) (f.mapMatrix N) := by
  simp only [projMat, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    map_intCast, map_matCoord]

variable (S)

@[expose] def conjMat {R : Type*} [CommRing R] (M : Matrix (Fin D.d) (Fin D.d) R) (l : Label τ) :
    Matrix (Fin D.d) (Fin D.d) R :=
  M * (adjMat D S l).map (Int.cast : ℤ → R) * M.adjugate

theorem mapMatrix_conjMat {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (M : Matrix (Fin D.d) (Fin D.d) R) (l : Label τ) :
    f.mapMatrix (conjMat S M l) = conjMat S (f.mapMatrix M) l := by
  rw [conjMat, conjMat, map_mul, map_mul, RingHom.map_adjugate]
  congr 2
  ext i j
  simp

open CFSG.TauCetiBridge.BigCell (nLab posEquiv) in
@[expose] def adMat
    {R : Type*} [CommRing R] (M : Matrix (Fin D.d) (Fin D.d) R) :
    Matrix (Fin (nLab τ)) (Fin (nLab τ)) R :=
  Matrix.of fun i j => matCoord D R S (conjMat S M ((posEquiv τ).symm j)) ((posEquiv τ).symm i)

theorem mapMatrix_adMat
    {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (M : Matrix (Fin D.d) (Fin D.d) R) : f.mapMatrix (adMat S M) = adMat S (f.mapMatrix M) := by
  ext i j
  change f (adMat S M i j) = adMat S (f.mapMatrix M) i j
  simp only [adMat, Matrix.of_apply]
  rw [map_matCoord, mapMatrix_conjMat]

theorem evalMat_natural {d : ℕ} (q : ∀ (A : Type) [CommRing A], Matrix (Fin d) (Fin d) A → A)
    (hq : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix (Fin d) (Fin d) A),
      f (q A M) = q B (f.mapMatrix M))
    {A : Type} [CommRing A] (M : Matrix (Fin d) (Fin d) A) :
    evalMat M (q (MvPolynomial (Fin d × Fin d) ℤ) (coordMatrix d)) = q A M := by
  rw [hq _ _ (evalMat M), mapMatrix_evalMat_coordMatrix]

theorem natural_eq_zero {d : ℕ} (q : ∀ (A : Type) [CommRing A], Matrix (Fin d) (Fin d) A → A)
    (hq : ∀ (A B : Type) [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix (Fin d) (Fin d) A),
      f (q A M) = q B (f.mapMatrix M))
    {K : Type} [CommRing K] (T : Set (Matrix (Fin d) (Fin d) K)) (hT : ∀ N ∈ T, q K N = 0)
    {A : Type} [CommRing A] (M : Matrix (Fin d) (Fin d) A)
    (hM : ∀ P : MvPolynomial (Fin d × Fin d) ℤ, (∀ N ∈ T, evalMat N P = 0) → evalMat M P = 0) :
    q A M = 0 := by
  rw [← evalMat_natural q hq M]
  exact hM _ fun N hN => by rw [evalMat_natural q hq N, hT N hN]

section Units

variable {R : Type*} [CommRing R]

theorem natMat_inv_eq_adjugate (g : (Module.End R (Fin D.d →₀ R))ˣ)
    (hg : (natMat R (g : Module.End R (Fin D.d →₀ R))).det = 1) :
    natMat R ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) =
      (natMat R (g : Module.End R (Fin D.d →₀ R))).adjugate := by
  have h1 : natMat R (g : Module.End R (Fin D.d →₀ R)) *
      natMat R ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  calc natMat R ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) =
        ((natMat R (g : Module.End R (Fin D.d →₀ R))).adjugate *
          natMat R (g : Module.End R (Fin D.d →₀ R))) *
          natMat R ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R)) := by
        rw [Matrix.adjugate_mul, hg, one_smul, one_mul]
    _ = _ := by rw [mul_assoc, h1, mul_one]

theorem conjMat_natMat
    (g : (Module.End R (Fin D.d →₀ R))ˣ)
    (hg : (natMat R (g : Module.End R (Fin D.d →₀ R))).det = 1) (l : Label τ) :
    conjMat S (natMat R (g : Module.End R (Fin D.d →₀ R))) l =
      natMat R ((g : Module.End R (Fin D.d →₀ R)) * adjMap R S D (Finsupp.single l 1) *
        ((g⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R))) := by
  rw [map_mul, map_mul, natMat_inv_eq_adjugate g hg, natMat_adjMap_single, conjMat]

variable (hV : D.Valid) (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
include hV hpd

theorem conjMat_eq_projMat
    {g : (Module.End R (Fin D.d →₀ R))ˣ} (hgN : g ∈ adjNormalizer R S D)
    (hg : (natMat R (g : Module.End R (Fin D.d →₀ R))).det = 1) (l : Label τ) :
    conjMat S (natMat R (g : Module.End R (Fin D.d →₀ R))) l =
      projMat (S := S) (conjMat S (natMat R (g : Module.End R (Fin D.d →₀ R))) l) := by
  obtain ⟨w, hw⟩ := hgN.1 (Finsupp.single l 1)
  rw [conjMat_natMat S g hg, hw, ← natMat_adjMap_adjInv, adjInv_adjMap R hV hpd S]

theorem adMat_natMat
    (g : adjNormalizer R S D)
    (hg : (natMat R ((g : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R))).det =
      1) :
    adMat S (natMat R ((g : (Module.End R (Fin D.d →₀ R))ˣ) : Module.End R (Fin D.d →₀ R))) =
      BigCell.natMat τ R ((ad hV hpd S g : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) := by
  ext i j
  rw [adMat, Matrix.of_apply, conjMat_natMat S _ hg, BigCell.natMat_apply, coe_ad, adEnd_apply,
    adjInv_apply]

end Units

end CFSG.TauCetiBridge.Minuscule
