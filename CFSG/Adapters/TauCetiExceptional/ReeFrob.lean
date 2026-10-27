module

public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.Adapters.TauCetiExceptional.ReePoints

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.TauCetiBridge.BigCell TauCeti
open CFSG.LieType.Chevalley

theorem coe_glMap {A : Type*} [CommRing A] (φ : A →+* A)
    (g : Matrix.GeneralLinearGroup (Fin 7) A) :
    ((Matrix.GeneralLinearGroup.map φ g : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = φ.mapMatrix (g : Matrix (Fin 7) (Fin 7) A) :=
  rfl

theorem adConj_map {A : Type*} [CommRing A] (φ : A →+* A)
    (g : Matrix.GeneralLinearGroup (Fin 7) A) :
    adConj (Matrix.GeneralLinearGroup.map φ g) = entrywise φ (adConj g) := by
  refine rootModule_ext fun b => Finsupp.ext fun x => ?_
  rw [entrywise_single, Finsupp.mapRange_apply, adOp_single_apply, adOp_single_apply, map_coord,
    ← map_inv, coe_glMap, coe_glMap, ← RingHom.mapMatrix_apply, map_mul, map_mul,
    mapMatrix_labMat]

theorem adPoints_frobenius {L : Type} [Field L] [Algebra (ZMod 3) L] (m : ℕ)
    (g : G2ShortRoot.PrimeField.points L) :
    adPoints L (G2ShortRoot.PrimeField.frobenius m L g) =
      Units.map (entrywiseHom (((FiniteField.frobeniusAlgHom (ZMod 3) L) ^ m :
        L →ₐ[ZMod 3] L) : L →+* L)) (adPoints L g) := by
  refine Units.ext ?_
  rw [coe_adPoints, G2ShortRoot.PrimeField.coe_frobenius, adConj_map]
  rfl

theorem frobenius_iterate_rootSubgroupPoints {A : Type} [CommRing A] [Algebra (ZMod 3) A]
    (m : ℕ) (k : Fin 2 ⊕ Fin 2) (u : A) :
    (G2ShortRoot.PrimeField.frobenius 1 A)^[m]
        (G2ShortRoot.PrimeField.rootSubgroupPoints k A (Multiplicative.ofAdd u)) =
      G2ShortRoot.PrimeField.rootSubgroupPoints k A (Multiplicative.ofAdd (u ^ 3 ^ m)) := by
  induction m with
  | zero => rw [Function.iterate_zero, id, pow_zero, pow_one]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, G2ShortRoot.PrimeField.frobenius_rootSubgroupPoints,
      toAdd_ofAdd, pow_one, ← pow_mul, ← pow_succ]

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

theorem mem_map_adjointGroup_G2_of_frobenius_fixed
    (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g : ModGL .G2 L} (hg : g ∈ adjointGroup .G2 L)
    (hfix : Units.map (entrywiseHom Fr) g = g) :
    g ∈ (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
  obtain ⟨S, hS⟩ := exists_finset_descent hg
  obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) S
  have : Finite E := hEf
  obtain ⟨y, hy, rfl⟩ := hS E hSE
  obtain ⟨σE, -, hJ, hfixE⟩ := exists_subfieldFrobenius_data (τ := .G2) Fr hFr E hKE
  have hyΓ := hfixE y hy hfix
  rw [CFSG.RankThree.entrywiseFixedGroup_eq_fixedFieldImage_of_det_one
    CFSG.RankThree.det_transpose_cartan_G2] at hyΓ
  rw [← hJ]
  exact ⟨y, hyΓ, rfl⟩

end CFSG.TauCetiBridge.Ree
