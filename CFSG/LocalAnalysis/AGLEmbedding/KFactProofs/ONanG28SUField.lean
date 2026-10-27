module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28SUBase
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28.SU

open CFSG.Quasithin Polynomial
open scoped Matrix

noncomputable section

@[expose] def pF : GF8[X] := X ^ 2 + X + 1

theorem pF_natDegree : pF.natDegree = 2 := by
  unfold pF
  compute_degree!

theorem pF_irreducible : Irreducible pF := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [pF_natDegree]
    simp
  · intro x
    have h : ∀ x : GF8, x ^ 2 + x + 1 ≠ 0 := by decide
    simpa [pF, IsRoot] using h x

instance instFactIrreduciblePF : Fact (Irreducible pF) := ⟨pF_irreducible⟩

abbrev F64 : Type := AdjoinRoot pF

theorem Rm_sq : Rm * Rm + Rm + 1 = 0 := by decide

theorem aeval_pF : Polynomial.aeval Rm pF = 0 := by
  simp only [pF, map_add, map_pow, aeval_X, map_one]
  rw [pow_two]
  exact Rm_sq

@[expose] def rhoL : F64 →+* Matrix (Fin 2) (Fin 2) GF8 :=
  Ideal.Quotient.lift (Ideal.span {pF})
    (Polynomial.aeval Rm : GF8[X] →ₐ[GF8] Matrix (Fin 2) (Fin 2) GF8).toRingHom (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [aeval_pF])

theorem rhoL_mk (g : GF8[X]) : rhoL (AdjoinRoot.mk pF g) = Polynomial.aeval Rm g := rfl

theorem rhoL_of (a : GF8) : rhoL (AdjoinRoot.of pF a) = Matrix.scalar (Fin 2) a := by
  rw [← AdjoinRoot.mk_C, rhoL_mk, aeval_C]
  ext i j
  simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem rhoL_root : rhoL (AdjoinRoot.root pF) = Rm := by
  rw [AdjoinRoot.root, rhoL_mk]
  simp

theorem rhoL_injective : Function.Injective rhoL := rhoL.injective

theorem shape_of_comm {B : Matrix (Fin 2) (Fin 2) GF8} (h : B * Rm = Rm * B) :
    B = !![B 0 0, B 0 1; B 0 1, B 0 0 + B 0 1] := by
  have h00 : B 0 1 = B 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Rm] using congrFun (congrFun h 0) 0
  have h01 : B 0 0 + B 0 1 = B 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Rm] using congrFun (congrFun h 0) 1
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simp
  · simpa using h00.symm
  · simpa using h01.symm

theorem rhoL_comm (x : F64) : rhoL x * Rm = Rm * rhoL x := by
  rw [← rhoL_root, ← map_mul, ← map_mul, mul_comm]

theorem rhoL_shape (x : F64) :
    rhoL x = !![rhoL x 0 0, rhoL x 0 1; rhoL x 0 1, rhoL x 0 0 + rhoL x 0 1] :=
  shape_of_comm (rhoL_comm x)

theorem exists_rhoL_eq {B : Matrix (Fin 2) (Fin 2) GF8} (h : B * Rm = Rm * B) :
    ∃ x : F64, rhoL x = B := by
  refine ⟨AdjoinRoot.of pF (B 0 0) + AdjoinRoot.of pF (B 0 1) * AdjoinRoot.root pF, ?_⟩
  rw [map_add, map_mul, rhoL_of, rhoL_of, rhoL_root, shape_of_comm h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rm, Matrix.scalar_apply]

theorem eight_pow_shape : ∀ p q : GF8, (!![p, q; q, p + q] : Matrix (Fin 2) (Fin 2) GF8) ^ 8 =
    !![p + q, q; q, p] := by decide

theorem rhoL_transpose (x : F64) : (rhoL x)ᵀ = rhoL x := by
  rw [rhoL_shape x]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rhoL_conj (x : F64) : Km * rhoL x * Km = rhoL (x ^ 8) := by
  rw [map_pow, rhoL_shape x, eight_pow_shape]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Km, Matrix.mul_apply, Fin.sum_univ_two]

theorem Km_sq : Km * Km = 1 := by decide

theorem omega_quad : AdjoinRoot.root pF * AdjoinRoot.root pF + AdjoinRoot.root pF + 1 = 0 := by
  apply rhoL_injective
  rw [map_add, map_add, map_mul, rhoL_root, map_one, map_zero]
  exact Rm_sq

theorem omega_pow_three : AdjoinRoot.root pF ^ 3 = 1 := by
  apply rhoL_injective
  rw [map_pow, rhoL_root, map_one]
  decide

@[expose] def coords : F64 ≃ GF8 × GF8 :=
  Equiv.ofBijective (fun x => (rhoL x 0 0, rhoL x 0 1)) (by
    constructor
    · intro x y h
      apply rhoL_injective
      rw [rhoL_shape x, rhoL_shape y]
      simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
    · rintro ⟨p, q⟩
      refine ⟨AdjoinRoot.of pF p + AdjoinRoot.of pF q * AdjoinRoot.root pF, ?_⟩
      dsimp only
      rw [map_add, map_mul, rhoL_of, rhoL_of, rhoL_root]
      simp [Rm, Matrix.scalar_apply])

theorem fintype_card_gf8 : Fintype.card GF8 = 8 := by decide

theorem card_F64 : Nat.card F64 = 64 := by
  rw [Nat.card_congr coords, Nat.card_prod, Nat.card_eq_fintype_card, fintype_card_gf8]

instance instFiniteF64 : Finite F64 := Finite.of_equiv _ coords.symm

theorem two_eq_zero_F64 : (2 : F64) = 0 := by
  apply rhoL_injective
  rw [map_zero]
  have : rhoL (2 : F64) = 2 := map_ofNat rhoL 2
  rw [this]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

instance instCharPF64 : CharP F64 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero two_eq_zero_F64

@[expose] def blockMat : Matrix (Fin 3) (Fin 3) F64 →+* Matrix (Fin 6) (Fin 6) GF8 :=
  blockEquiv.toRingHom.comp (RingHom.mapMatrix rhoL)

theorem blockMat_eq (G : Matrix (Fin 3) (Fin 3) F64) : blockMat G = blockEquiv (G.map rhoL) := rfl

theorem blockMat_apply (G : Matrix (Fin 3) (Fin 3) F64) (i j : Fin 3) (r s : Fin 2) :
    blockMat G (sIdx i r) (sIdx j s) = rhoL (G i j) r s := by
  rw [blockMat_eq, blockEquiv_apply]
  rfl

theorem blockMat_injective : Function.Injective blockMat := by
  intro G H h
  ext i j
  apply rhoL_injective
  ext r s
  rw [← blockMat_apply G i j r s, ← blockMat_apply H i j r s, h]

@[expose] def omegaMat : Matrix (Fin 3) (Fin 3) F64 := Matrix.diagonal fun _ => AdjoinRoot.root pF

theorem blockMat_omegaMat : blockMat omegaMat = rbM := by
  rw [blockMat_eq, omegaMat, Matrix.diagonal_map (map_zero rhoL), rhoL_root]
  rfl

theorem blockMat_surj_of_comm {A : Matrix (Fin 6) (Fin 6) GF8} (h : A * rbM = rbM * A) :
    ∃ G, blockMat G = A := by
  set A' := blockEquiv.symm A with hA'
  have h' : A' * Matrix.diagonal (fun _ => Rm) = Matrix.diagonal (fun _ => Rm) * A' := by
    apply blockEquiv.injective
    rw [map_mul, map_mul, hA', RingEquiv.apply_symm_apply]
    exact h
  have hij : ∀ i j, A' i j * Rm = Rm * A' i j := by
    intro i j
    have := congrFun (congrFun h' i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  choose G hG using fun i j => exists_rhoL_eq (hij i j)
  refine ⟨Matrix.of G, ?_⟩
  rw [blockMat_eq]
  have : (Matrix.of G).map rhoL = A' := by
    refine Matrix.ext fun i j => ?_
    exact hG i j
  rw [this, hA', RingEquiv.apply_symm_apply]

theorem jbM_sq : jbM * jbM = 1 := by
  rw [jbM, ← map_mul, Matrix.diagonal_mul_diagonal, Km_sq]
  have : (Matrix.diagonal fun _ : Fin 3 => (1 : Matrix (Fin 2) (Fin 2) GF8)) = 1 :=
    Matrix.diagonal_one
  rw [this, map_one]

theorem jbM_mul_blockMat (Y : Matrix (Fin 3) (Fin 3) F64) :
    jbM * blockMat Y = blockMat (Y.map (· ^ 8)) * jbM := by
  rw [jbM, blockMat_eq, blockMat_eq, ← map_mul, ← map_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.map_apply]
  have h := rhoL_conj (Y i j)
  calc Km * rhoL (Y i j) = Km * rhoL (Y i j) * (Km * Km) := by rw [Km_sq, mul_one]
    _ = (Km * rhoL (Y i j) * Km) * Km := by simp only [mul_assoc]
    _ = rhoL (Y i j ^ 8) * Km := by rw [h]

theorem blockMat_transpose (G : Matrix (Fin 3) (Fin 3) F64) : (blockMat G)ᵀ = blockMat Gᵀ := by
  ext a b
  obtain ⟨⟨i, r⟩, rfl⟩ := sEquiv.surjective a
  obtain ⟨⟨j, s⟩, rfl⟩ := sEquiv.surjective b
  rw [sEquiv_apply, sEquiv_apply, Matrix.transpose_apply, blockMat_apply, blockMat_apply,
    Matrix.transpose_apply]
  have := congrFun (congrFun (rhoL_transpose (G j i)) r) s
  simpa [Matrix.transpose_apply] using this

theorem unitary_of_symp {G : Matrix (Fin 3) (Fin 3) F64}
    (h : (blockMat G)ᵀ * jbM * blockMat G = jbM) : (G.map (· ^ 8))ᵀ * G = 1 := by
  rw [blockMat_transpose, mul_assoc, jbM_mul_blockMat, ← mul_assoc, ← map_mul] at h
  have h2 : blockMat (Gᵀ * G.map (· ^ 8)) = blockMat 1 := by
    have := congrArg (fun X => X * jbM) h
    simpa [mul_assoc, jbM_sq] using this
  have h3 := blockMat_injective h2
  have := congrArg Matrix.transpose h3
  simpa [Matrix.transpose_mul] using this

theorem blk_blockMat (G : Matrix (Fin 3) (Fin 3) F64) (i j : Fin 3) :
    blk (blockMat G) i j = rhoL (G i j) := by
  ext r s
  exact blockMat_apply G i j r s

theorem gf8_neg (a : GF8) : -a = a := by
  revert a
  decide

theorem m2_neg (X : Matrix (Fin 2) (Fin 2) GF8) : -X = X := by
  ext i j
  simp [gf8_neg]

theorem rhoL_det (G : Matrix (Fin 3) (Fin 3) F64) : rhoL G.det = detBlk (blockMat G) := by
  rw [Matrix.det_fin_three]
  simp only [map_add, map_sub, map_mul]
  simp only [detBlk, blk_blockMat]
  simp only [sub_eq_add_neg, m2_neg]
  abel

end

end CFSG.AGLEmbedding.KFactProofs.G28.SU
