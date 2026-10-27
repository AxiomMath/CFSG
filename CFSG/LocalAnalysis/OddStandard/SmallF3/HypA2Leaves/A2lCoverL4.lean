module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverStated
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearFourThree

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartTwo.Census
open scoped MatrixGroups

noncomputable def a2lNineBaseEquiv {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 3) :
    nineBase ≃+* F :=
  haveI := Fintype.ofFinite nineBase
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP F 3 := charP_of_card_eq_prime hF
  (ZMod.ringEquiv (n := 3) nineBase fintype_card_nineBase).symm.trans
    (ZMod.ringEquiv (n := 3) F hF)

@[expose] noncomputable def a2lSLReindex {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {R : Type} [CommRing R] (e : m ≃ n) :
    Matrix.SpecialLinearGroup m R →* Matrix.SpecialLinearGroup n R where
  toFun A := ⟨Matrix.reindex e e (A : Matrix m m R), by
    rw [Matrix.det_reindex_self]; exact A.2⟩
  map_one' := Subtype.ext (by simp [Matrix.reindex_apply])
  map_mul' A B := Subtype.ext (by
    change Matrix.reindex e e ((A * B : Matrix.SpecialLinearGroup m R) : Matrix m m R) =
      Matrix.reindex e e (A : Matrix m m R) * Matrix.reindex e e (B : Matrix m m R)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.reindex_apply, Matrix.submatrix_mul_equiv])

theorem a2lSLReindex_injective {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {R : Type} [CommRing R] (e : m ≃ n) :
    Function.Injective (a2lSLReindex (R := R) e) := fun A B h =>
  Subtype.ext ((Matrix.reindex e e).injective (congrArg Subtype.val h))

@[expose] noncomputable def a2lNineSL4 {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 3) : SL(2, GaloisField 3 2) →* Matrix.SpecialLinearGroup (Fin 4) F :=
  (a2lSLReindex (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)).comp
    ((Matrix.SpecialLinearGroup.map (a2lNineBaseEquiv hF).toRingHom).comp nineSL)

theorem a2lNineSL4_coe {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 3)
    (A : SL(2, GaloisField 3 2)) :
    ((a2lNineSL4 hF A : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.reindex (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) finProdFinEquiv
        ((nineBlock (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))).map
          (a2lNineBaseEquiv hF)) :=
  rfl

theorem a2lNineSL4_injective {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 3) :
    Function.Injective (a2lNineSL4 hF) := by
  intro A B h
  have h1 := a2lSLReindex_injective _ h
  have h2 : nineSL A = nineSL B := Subtype.ext
    (Matrix.map_injective (a2lNineBaseEquiv hF).injective (congrArg Subtype.val h1))
  exact nineSL_injective h2

theorem a2lNineSL4_negOne {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 3) :
    ((a2lNineSL4 hF (a2lNegOne (GaloisField 3 2)) : Matrix.SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = -1 := by
  have h1 : nineBlock (-1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2)) = -1 := by
    rw [map_neg, map_one]
  rw [a2lNineSL4_coe]
  change Matrix.reindex _ _ ((nineBlock (-1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))).map _) = _
  rw [h1]
  ext i j
  simp [Matrix.reindex_apply, Matrix.one_apply]

theorem a2lNineSL4_negOne_mem_center {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 3) :
    a2lNineSL4 hF (a2lNegOne (GaloisField 3 2)) ∈
      center (Matrix.SpecialLinearGroup (Fin 4) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by rw [Fintype.card_fin]; norm_num, ?_⟩
  rw [a2lNineSL4_negOne, map_neg, map_one]

theorem a2l_centralDatum_psl43 (hC : HypA2.ChevOddInChev2) {K : Type} [Group K] [Finite K]
    (hq : IsQuasisimple K) (h2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    (hm : LieModel (K ⧸ center K) .PSL 4 3 1) : HypA2.CentralDatum K := by
  haveI : Group.IsPerfect K := hq.1
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  haveI := Fintype.ofFinite F
  classical
  have hF : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  obtain ⟨ψ, -⟩ := ComponentClassification.CatFactsL4U4.exists_equiv_statedSL_four h2 hZ
    (by rw [hF]) e
  haveI := Fintype.ofFinite (GaloisField 3 2)
  have hE : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, card_galoisField_three_two]
  have hTU : HypA2.TypU K := a2l_typU_of_not_inChev2 hq h2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))) (a2l_not_inChev2_psl43 hC hm)
  refine a2l_centralDatum_of_equiv ψ (by decide) (by norm_num) hE
    ((specialLinearGroupEquivStatedSL 4 F).toMonoidHom.comp (a2lNineSL4 hF))
    ((specialLinearGroupEquivStatedSL 4 F).injective.comp (a2lNineSL4_injective hF)) ?_ hTU
  exact a2l_mem_center_of_equiv (specialLinearGroupEquivStatedSL 4 F)
    (a2lNineSL4_negOne_mem_center hF)

end CFSG.OddStandard.SmallF3.HypA2Leaves
