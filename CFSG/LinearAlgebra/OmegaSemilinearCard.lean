module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutGalois
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates

public section

namespace CFSG.LinearAlgebra

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem natCard_coordinateSemilinearGroup (d : ℕ) (K : Type*) [Field K] [Finite K] :
    Nat.card (coordinateSemilinearGroup d K) =
      Nat.card (GL (Fin d) K) * Nat.card (K ≃+* K) := by
  rw [coordinateSemilinearGroup, SemidirectProduct.card]

theorem natCard_coordinateSemilinearGroup_three_OmegaField :
    Nat.card (coordinateSemilinearGroup 3 OmegaField) = 362880 := by
  haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  haveI : Finite OmegaField := Module.finite_of_finite (ZMod 2)
  haveI : Fintype OmegaField := Fintype.ofFinite OmegaField
  rw [natCard_coordinateSemilinearGroup, Matrix.card_GL_field]
  have hcardField : Nat.card OmegaField = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_omegaField, Nat.card_zmod]
    norm_num
  have hcardFieldF : Fintype.card OmegaField = 4 := by
    rw [← Nat.card_eq_fintype_card, hcardField]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP OmegaField 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) OmegaField).injective 2
  have hcardAut : Nat.card (OmegaField ≃+* OmegaField) = 2 := by
    have h := CFSG.AGLEmbedding.UnitaryModel.card_ringEquiv OmegaField 2 2 (by rw [hcardField]; norm_num)
    simpa using h
  rw [hcardFieldF, hcardAut, Fin.prod_univ_three]
  norm_num

end CFSG.LinearAlgebra
