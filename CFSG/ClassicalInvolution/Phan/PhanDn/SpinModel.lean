module

public import CFSG.ClassicalInvolution.Phan.PhanDn.NormFormType
public import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
public import CFSG.LieType.Universal.Catalog

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CliffordAlgebra

section General

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {σ : K ≃+* K}

noncomputable def Qn.isometryEquivQuadPlus (E : QuadExt F K σ) {n : ℕ} (he : Even n)
    [Finite K] [CharP K 2] : (Qn E n).IsometryEquiv (Spin.quadPlus n F) :=
  Classical.choice (nonempty_isometryEquiv_quadPlus E he)

noncomputable def omegaEquivSpinPlus (E : QuadExt F K σ) {n : ℕ} (he : Even n)
    (hn : 3 ≤ n) [Finite K] [CharP K 2] :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E n),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E n)⁆ ≃* spinGroup (Spin.quadPlus n F) := by
  letI : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  exact commutatorEquivSpinPlusOfIsometry (Qn.isometryEquivQuadPlus E he) hn
    (CharP.cast_eq_zero F 2)

@[simp]
theorem spinAction_omegaEquivSpinPlus_apply (E : QuadExt F K σ) {n : ℕ}
    (he : Even n) (hn : 3 ≤ n) [Finite K] [CharP K 2]
    (g : ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E n),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E n)⁆) :
    spinAction (Spin.quadPlus n F) (omegaEquivSpinPlus E he hn g) =
      LinearEquiv.autCongr (Qn.isometryEquivQuadPlus E he).toLinearEquiv
        (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) := by
  rw [omegaEquivSpinPlus, spinAction_commutatorEquivSpinPlusOfIsometry_apply]

noncomputable def Qn.isometryEquivQuadMinus (E : QuadExt F K σ) {n : ℕ} (ho : Odd n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) [Finite K] [CharP K 2] :
    (Qn E n).IsometryEquiv (Spin.quadMinus n F b c) :=
  Classical.choice (nonempty_isometryEquiv_quadMinus E ho hirr)

noncomputable def omegaEquivSpinMinus (E : QuadExt F K σ) {n : ℕ} (ho : Odd n)
    (hn : 4 ≤ n) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    [Finite F] [Finite K] [CharP K 2] :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E n),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E n)⁆ ≃*
      spinGroup (Spin.quadMinus n F b c) := by
  letI : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  exact commutatorEquivSpinMinusOfIsometry (Qn.isometryEquivQuadMinus E ho hirr) hn hirr
    (CharP.cast_eq_zero F 2)

@[simp]
theorem spinAction_omegaEquivSpinMinus_apply (E : QuadExt F K σ) {n : ℕ}
    (ho : Odd n) (hn : 4 ≤ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) [Finite F] [Finite K] [CharP K 2]
    (g : ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E n),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E n)⁆) :
    spinAction (Spin.quadMinus n F b c) (omegaEquivSpinMinus E ho hn hirr g) =
      LinearEquiv.autCongr (Qn.isometryEquivQuadMinus E ho hirr).toLinearEquiv
        (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) := by
  rw [omegaEquivSpinMinus, spinAction_commutatorEquivSpinMinusOfIsometry_apply]

end General

section Universal

variable {K : Type} [Field K] {f : ℕ} [Algebra (GaloisField 2 f) K]
variable {σ : K ≃+* K}

@[expose] noncomputable def omegaEquivLieUniversalPlus (E : QuadExt (GaloisField 2 f) K σ) {n : ℕ}
    (he : Even n) (hn : 3 ≤ n) [Finite K] [CharP K 2] :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E n),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E n)⁆ ≃*
      (lieUniversal .POmegaPlus n 2 f Nat.prime_two).K :=
  (omegaEquivSpinPlus (F := GaloisField 2 f) E he hn).trans
    (MulEquiv.cast (M := fun L : LieUniversal => L.K)
      (Eq.symm (show lieUniversal .POmegaPlus n 2 f Nat.prime_two =
        (⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
          Spin.plusDatum n (GaloisField 2 f) hn⟩ : LieUniversal) from
        dite_eq_left hn)))

@[expose] noncomputable def omegaEquivLieUniversalMinus (E : QuadExt (GaloisField 2 f) K σ) {n : ℕ}
    (ho : Odd n) (hn : 4 ≤ n) [Finite K] [CharP K 2] :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E n),
      TauCeti.QuadraticMap.orthogonalGroup (Qn E n)⁆ ≃*
      (lieUniversal .POmegaMinus n 2 f Nat.prime_two).K :=
  (omegaEquivSpinMinus (F := GaloisField 2 f) E ho hn
    (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2)
    (minusCoeffs_irr 2 f)).trans
    (MulEquiv.cast (M := fun L : LieUniversal => L.K)
      (Eq.symm (show lieUniversal .POmegaMinus n 2 f Nat.prime_two =
        (⟨spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2),
          Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ : LieUniversal) from rfl)))

end Universal

end CFSG.ClassicalInvolution.PhanDn
