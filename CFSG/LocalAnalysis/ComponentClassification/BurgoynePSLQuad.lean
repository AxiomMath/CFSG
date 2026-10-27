module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLNormal
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.Data.Matrix.Composition
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag Module Polynomial
open scoped MatrixGroups

variable {K : Type} [Field K]

abbrev quadPoly (l : K) : K[X] := X ^ 2 - C l

abbrev QuadExt (l : K) := AdjoinRoot (quadPoly l)

theorem quadPoly_irreducible {l : K} (hl : ¬ IsSquare l) : Irreducible (quadPoly l) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => hl ⟨b, by rw [← hb, sq]⟩

@[expose] def compMat (l : K) : Matrix (Fin 2) (Fin 2) K := !![0, l; 1, 0]

theorem compMat_sq (l : K) : compMat l * compMat l = l • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [compMat]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem aeval_compMat_quadPoly (l : K) : aeval (compMat l) (quadPoly l) = 0 := by
  rw [quadPoly, map_sub, aeval_X_pow, aeval_C, pow_two, compMat_sq,
    Algebra.algebraMap_eq_smul_one, sub_self]

@[expose] def quadRep (l : K) : QuadExt l →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  Ideal.Quotient.liftₐ (Ideal.span {quadPoly l}) (aeval (compMat l)) fun a ha => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, aeval_compMat_quadPoly, mul_zero]

theorem quadRep_mk (l : K) (f : K[X]) :
    quadRep l (AdjoinRoot.mk (quadPoly l) f) = aeval (compMat l) f :=
  rfl

theorem quadRep_root (l : K) : quadRep l (AdjoinRoot.root (quadPoly l)) = compMat l := by
  rw [AdjoinRoot.root, quadRep_mk, aeval_X]

theorem quadRep_algebraMap (l c : K) : quadRep l (algebraMap K (QuadExt l) c) = c • 1 := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

theorem quadRep_add_mul_root (l a b : K) :
    quadRep l (algebraMap K _ a + algebraMap K _ b * AdjoinRoot.root (quadPoly l)) =
      !![a, b * l; b, a] := by
  rw [map_add, map_mul, quadRep_algebraMap, quadRep_algebraMap, quadRep_root, compMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_quadRep_of_commute (l : K) {Z : Matrix (Fin 2) (Fin 2) K}
    (h : Z * compMat l = compMat l * Z) : ∃ y : QuadExt l, quadRep l y = Z := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [compMat, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine ⟨algebraMap K _ (Z 0 0) + algebraMap K _ (Z 1 0) * AdjoinRoot.root (quadPoly l), ?_⟩
  rw [quadRep_add_mul_root]
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact e11
  · rfl
  · exact e10.symm

theorem quadRep_injective {l : K} (hl : ¬ IsSquare l) : Function.Injective (quadRep l) := by
  have : Fact (Irreducible (quadPoly l)) := ⟨quadPoly_irreducible hl⟩
  exact (quadRep l).toRingHom.injective

variable (l : K) (m : ℕ)

@[expose] def blockRep :
    Matrix (Fin m) (Fin m) (QuadExt l) →ₐ[K] Matrix (Fin (m * 2)) (Fin (m * 2)) K :=
  ((reindexAlgEquiv K K finProdFinEquiv).toAlgHom.comp
    (compAlgEquiv (Fin m) (Fin 2) K K).toAlgHom).comp (quadRep l).mapMatrix

variable {l m}

theorem blockRep_apply (Y : Matrix (Fin m) (Fin m) (QuadExt l)) (i j : Fin m) (a b : Fin 2) :
    blockRep l m Y (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) = quadRep l (Y i j) a b := by
  simp [blockRep]

theorem blockRep_injective (hl : ¬ IsSquare l) : Function.Injective (blockRep l m) := by
  intro Y Z h
  ext i j
  apply quadRep_injective hl
  ext a b
  rw [← blockRep_apply, ← blockRep_apply, h]

variable (l m) in
@[expose] def quadMat : Matrix (Fin (m * 2)) (Fin (m * 2)) K :=
  blockRep l m (Matrix.scalar (Fin m) (AdjoinRoot.root (quadPoly l)))

theorem quadMat_apply (i j : Fin m) (a b : Fin 2) :
    quadMat l m (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      if i = j then compMat l a b else 0 := by
  rw [quadMat, blockRep_apply, scalar_apply, diagonal_apply]
  split_ifs
  · rw [quadRep_root]
  · rw [map_zero, Matrix.zero_apply]

theorem mul_apply_prod (P Q : Matrix (Fin (m * 2)) (Fin (m * 2)) K) (x y : Fin m × Fin 2) :
    (P * Q) (finProdFinEquiv x) (finProdFinEquiv y) =
      ∑ k : Fin m, ∑ c : Fin 2, P (finProdFinEquiv x) (finProdFinEquiv (k, c)) *
        Q (finProdFinEquiv (k, c)) (finProdFinEquiv y) := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]

@[expose] def blockOf (X : Matrix (Fin (m * 2)) (Fin (m * 2)) K) (i j : Fin m) :
    Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun a b => X (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b))

theorem blockOf_mul_quadMat (X : Matrix (Fin (m * 2)) (Fin (m * 2)) K) (i j : Fin m) :
    blockOf (X * quadMat l m) i j = blockOf X i j * compMat l := by
  ext a b
  rw [blockOf, of_apply, mul_apply_prod, Matrix.mul_apply]
  simp only [quadMat_apply, mul_ite, mul_zero]
  rw [Finset.sum_comm, Fintype.sum_congr _ _ fun c => Finset.sum_ite_eq' _ j _]
  simp [blockOf]

theorem blockOf_quadMat_mul (X : Matrix (Fin (m * 2)) (Fin (m * 2)) K) (i j : Fin m) :
    blockOf (quadMat l m * X) i j = compMat l * blockOf X i j := by
  ext a b
  rw [blockOf, of_apply, mul_apply_prod, Matrix.mul_apply]
  simp only [quadMat_apply, ite_mul, zero_mul]
  rw [Finset.sum_comm, Fintype.sum_congr _ _ fun c => Finset.sum_ite_eq _ i _]
  simp [blockOf]

theorem exists_blockRep_of_commute {X : Matrix (Fin (m * 2)) (Fin (m * 2)) K}
    (h : X * quadMat l m = quadMat l m * X) : ∃ Y, blockRep l m Y = X := by
  have hb : ∀ i j, ∃ y : QuadExt l, quadRep l y = blockOf X i j := by
    intro i j
    refine exists_quadRep_of_commute l ?_
    rw [← blockOf_mul_quadMat, ← blockOf_quadMat_mul, h]
  choose Y hY using hb
  refine ⟨Matrix.of Y, ?_⟩
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective y
  rw [blockRep_apply, of_apply, hY]
  rfl

theorem root_sq (l : K) :
    AdjoinRoot.root (quadPoly l) * AdjoinRoot.root (quadPoly l) = algebraMap K (QuadExt l) l := by
  have h := AdjoinRoot.eval₂_root (quadPoly l)
  simp only [quadPoly, eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← pow_two]
  rw [sub_eq_zero] at h
  rw [h]
  rfl

theorem exists_quad_normal_form {l : K} (hl : ¬ IsSquare l) {A : GL (Fin (m * 2)) K}
    (hA : (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * A = l • 1) :
    ∃ H : GL (Fin (m * 2)) K, (H : Matrix (Fin (m * 2)) (Fin (m * 2)) K) *
      (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) *
        ((H⁻¹ : GL (Fin (m * 2)) K) : Matrix (Fin (m * 2)) (Fin (m * 2)) K) = quadMat l m := by
  classical
  have : Fact (Irreducible (quadPoly l)) := ⟨quadPoly_irreducible hl⟩
  set V := Fin (m * 2) → K
  set f := Matrix.toLin' (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) with hf
  have hff : aeval f (quadPoly l) = 0 := by
    rw [quadPoly, map_sub, aeval_X_pow, aeval_C, pow_two, hf, Module.End.mul_eq_comp,
      ← Matrix.toLin'_mul, hA, Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLin'_one]
    exact sub_self _
  set φ : QuadExt l →ₐ[K] Module.End K V :=
    Ideal.Quotient.liftₐ (Ideal.span {quadPoly l}) (aeval f) fun a ha => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hff, mul_zero] with hφ
  have hφroot : φ (AdjoinRoot.root (quadPoly l)) = f := by
    change φ (AdjoinRoot.mk _ X) = f
    rw [hφ]
    change aeval f X = f
    rw [aeval_X]
  let : Module (QuadExt l) V := Module.compHom V φ.toRingHom
  have hsmul : ∀ (y : QuadExt l) (v : V), y • v = φ y v := fun _ _ => rfl
  have : IsScalarTower K (QuadExt l) V := ⟨fun c y v => by
    rw [hsmul, hsmul, map_smul, LinearMap.smul_apply]⟩
  have : Module.Finite (QuadExt l) V := Module.Finite.of_restrictScalars_finite K _ V
  have hmonic : (quadPoly l).Monic := monic_X_pow_sub_C l two_ne_zero
  have hdeg : (quadPoly l).natDegree = 2 := natDegree_X_pow_sub_C
  set pb := AdjoinRoot.powerBasis' hmonic with hpb
  have hdim : pb.dim = 2 := hdeg
  set pbb : Basis (Fin 2) K (QuadExt l) := pb.basis.reindex (finCongr hdim) with hpbb
  have hpbb : ∀ k : Fin 2, pbb k = AdjoinRoot.root (quadPoly l) ^ (k : ℕ) := by
    intro k
    rw [hpbb, Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  have hrm : Module.finrank (QuadExt l) V = m := by
    have h1 := Module.finrank_mul_finrank K (QuadExt l) V
    rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis pbb, Fintype.card_fin] at h1
    omega
  set b := (Module.finBasis (QuadExt l) V).reindex (finCongr hrm) with hb
  set bb' := pbb.smulTower' b with hbb'
  set bb := bb'.reindex finProdFinEquiv with hbb
  have hbbapp : ∀ i k, bb (finProdFinEquiv (i, k)) = pbb k • b i := by
    intro i k
    rw [hbb, Basis.reindex_apply, Equiv.symm_apply_apply, hbb', Basis.smulTower'_apply]
  have hroot : ∀ (y : QuadExt l) (v : V), f (y • v) = (AdjoinRoot.root (quadPoly l) * y) • v := by
    intro y v
    rw [hsmul, hsmul, map_mul, ← hφroot]
    rfl
  have hf0 : ∀ i, f (bb (finProdFinEquiv (i, 0))) = bb (finProdFinEquiv (i, 1)) := by
    intro i
    rw [hbbapp, hbbapp, hroot, hpbb, hpbb]
    simp
  have hf1 : ∀ i, f (bb (finProdFinEquiv (i, 1))) = l • bb (finProdFinEquiv (i, 0)) := by
    intro i
    rw [hbbapp, hbbapp, hroot, hpbb, hpbb]
    simp only [Fin.val_one, Fin.val_zero, pow_one, pow_zero, one_smul]
    rw [root_sq, algebraMap_smul]
  obtain ⟨H, hH⟩ := exists_conj_eq_toMatrix bb A
  refine ⟨H, ?_⟩
  rw [hH]
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j, c⟩, rfl⟩ := finProdFinEquiv.surjective y
  rw [LinearMap.toMatrix_apply, ← hf, quadMat_apply]
  fin_cases c
  · simp only [Fin.zero_eta, hf0, Basis.repr_self, Finsupp.single_apply,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
    fin_cases a <;> by_cases hij : i = j <;> simp [hij, compMat, eq_comm]
  · simp only [Fin.mk_one, hf1, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, smul_eq_mul]
    fin_cases a <;> by_cases hij : i = j <;> simp [hij, compMat, eq_comm]

end CFSG.ComponentClassification.Burgoyne.PSL