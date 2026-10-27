module

public import CFSG.LieType.SpecialLinear.FieldActor.SemilinearDescent
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_stdAut_eq_conj {σ : F ≃+* F} (hσ : σ.trans σ = RingEquiv.refl F)
    (hσne : σ ≠ 1)
    (hn : 3 ≤ n) {b : GL (Fin n) F} {lam : F} (hlam : lam ≠ 0)
    (hb : b * Matrix.GeneralLinearGroup.map σ.toRingHom b =
      Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 lam hlam)) :
    ∃ P : GL (Fin n) F, ∀ g : SpecialLinearGroup (Fin n) F,
      CFSG.QuasithinUnique.K1.stdAut b σ 0 g =
        CFSG.QuasithinUnique.K1.stdAut P (RingEquiv.refl F) 0
          (CFSG.QuasithinUnique.K1.stdAut 1 σ 0
            (CFSG.QuasithinUnique.K1.stdAut P⁻¹ (RingEquiv.refl F) 0 g)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, t, ht, hb'⟩ := exists_normalized_of_mul_map_eq_scalar hσ hσne hn1 hlam hb
  obtain ⟨P, hP⟩ := exists_eq_mul_map_inv_of_mul_map_eq_one hσ hσne hb'
  have hproj : conjAut n F P * fieldAut n F σ * (conjAut n F P)⁻¹ =
      conjAut n F b * fieldAut n F σ := by
    have hf : fieldAut n F σ * (conjAut n F P)⁻¹ =
        conjAut n F (Matrix.GeneralLinearGroup.map σ.toRingHom P⁻¹) * fieldAut n F σ := by
      rw [← map_inv]
      exact fieldAut_mul_conjAut σ P⁻¹
    have hP' : P * Matrix.GeneralLinearGroup.map σ.toRingHom P⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin n) t * b := hP.symm
    calc conjAut n F P * fieldAut n F σ * (conjAut n F P)⁻¹
        = conjAut n F P * (fieldAut n F σ * (conjAut n F P)⁻¹) := by group
      _ = conjAut n F P * (conjAut n F (Matrix.GeneralLinearGroup.map σ.toRingHom P⁻¹) *
            fieldAut n F σ) := by rw [hf]
      _ = (conjAut n F P * conjAut n F
            (Matrix.GeneralLinearGroup.map σ.toRingHom P⁻¹)) * fieldAut n F σ := by group
      _ = conjAut n F (P * Matrix.GeneralLinearGroup.map σ.toRingHom P⁻¹) *
            fieldAut n F σ := by rw [← map_mul]
      _ = conjAut n F (Matrix.GeneralLinearGroup.scalar (Fin n) t * b) *
            fieldAut n F σ := by rw [hP']
      _ = conjAut n F b * fieldAut n F σ := by rw [map_mul, conjAut_scalar, one_mul]
  have hstd : CFSG.QuasithinUnique.K1.stdAut b σ 0 =
      CFSG.QuasithinUnique.K1.stdAut P (RingEquiv.refl F) 0 *
        CFSG.QuasithinUnique.K1.stdAut 1 σ 0 *
        (CFSG.QuasithinUnique.K1.stdAut P (RingEquiv.refl F) 0)⁻¹ := by
    apply CFSG.RankThree.PartOne.AUTSL.descendAut_injective hn
    simp only [CFSG.QuasithinUnique.K1.descendAut_stdAut, map_mul, map_inv,
      ← RingAut.one_eq_refl, map_one, pow_zero, mul_one]
    exact hproj.symm
  refine ⟨P, fun g => ?_⟩
  have hstdinv : CFSG.QuasithinUnique.K1.stdAut P⁻¹ (RingEquiv.refl F) 0 =
      (CFSG.QuasithinUnique.K1.stdAut P (RingEquiv.refl F) 0)⁻¹ := by
    simp only [CFSG.QuasithinUnique.K1.stdAut, ← RingAut.one_eq_refl, map_one, pow_zero, mul_one]
    exact map_inv (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F) P
  rw [hstd, hstdinv]
  simp [MulAut.mul_apply]

end CFSG.LieType.SpecialLinear
