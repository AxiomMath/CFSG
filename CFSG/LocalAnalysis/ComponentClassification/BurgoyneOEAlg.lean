module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix Polynomial

variable {K : Type} [Field K]

@[expose] def jMat (c : K) : Matrix (Fin 2) (Fin 2) K := !![0, c; 1, 0]

theorem jMat_mul_self (c : K) : jMat c * jMat c = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem smul_add_smul_jMat (c x y : K) :
    x • (1 : Matrix (Fin 2) (Fin 2) K) + y • jMat c = !![x, c * y; y, x] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat, mul_comm]

theorem eq_of_commute_jMat {c : K} (hc : c ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : M * jMat c = jMat c * M) :
    M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) + M 1 0 • jMat c := by
  have e : ∀ i j, (M * jMat c) i j = (jMat c * M) i j := fun i j => by rw [hM]
  have e01 := e 0 1
  have e00 := e 0 0
  simp [jMat, Matrix.mul_apply, Fin.sum_univ_two] at e01 e00
  rw [smul_add_smul_jMat]
  have h11 : M 1 1 = M 0 0 := mul_left_cancel₀ hc (by linear_combination -e01)
  have h01 : M 0 1 = c * M 1 0 := by linear_combination e00
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h11, h01]

theorem commute_jMat (c x y : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • jMat c) * jMat c =
      jMat c * (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • jMat c) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

@[expose] def wMat (a b : K) : Matrix (Fin 2) (Fin 2) K := diagonal ![a, b]

theorem transpose_mul_wOne (c x y : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • jMat c)ᵀ * wMat 1 c =
      wMat 1 c * (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • jMat c) := by
  rw [smul_add_smul_jMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem transpose_mul_wNeg (c x y : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • jMat c)ᵀ * wMat 1 (-c) =
      wMat 1 (-c) * (x • (1 : Matrix (Fin 2) (Fin 2) K) + (-y) • jMat c) := by
  rw [smul_add_smul_jMat, smul_add_smul_jMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

abbrev sqPoly (c : K) : K[X] := X ^ 2 - C c

theorem irreducible_sqPoly {c : K} (hc : ¬ IsSquare c) : Irreducible (sqPoly c) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two fun μ hμ => hc ⟨μ, by rw [← hμ, sq]⟩

abbrev EAlg (c : K) : Type := AdjoinRoot (sqPoly c)

theorem aeval_sqPoly_jMat (c : K) : aeval (jMat c) (sqPoly c) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, sq, jMat_mul_self, Algebra.algebraMap_eq_smul_one,
    sub_self]

@[expose] def phiE (c : K) : EAlg c →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  Ideal.Quotient.liftₐ (Ideal.span {sqPoly c}) (aeval (jMat c)) fun a ha => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, aeval_sqPoly_jMat, mul_zero]

theorem phiE_root (c : K) : phiE c (AdjoinRoot.root (sqPoly c)) = jMat c :=
  aeval_X (jMat c)

theorem phiE_algebraMap (c a : K) :
    phiE c (algebraMap K (EAlg c) a) = algebraMap K (Matrix (Fin 2) (Fin 2) K) a :=
  (phiE c).commutes a

theorem phiE_add_root (c a b : K) :
    phiE c (algebraMap K (EAlg c) a + algebraMap K (EAlg c) b * AdjoinRoot.root (sqPoly c)) =
      a • (1 : Matrix (Fin 2) (Fin 2) K) + b • jMat c := by
  rw [map_add, map_mul, phiE_algebraMap, phiE_algebraMap, phiE_root,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul]

theorem phiE_commute (c : K) (x : EAlg c) : phiE c x * jMat c = jMat c * phiE c x := by
  rw [← phiE_root, ← map_mul, ← map_mul, mul_comm]

section Field

variable {c : K} [Fact (Irreducible (sqPoly c))]

theorem phiE_injective (c : K) [Fact (Irreducible (sqPoly c))] :
    Function.Injective (phiE c) :=
  (phiE c).toRingHom.injective

theorem eq_add_root (hc : c ≠ 0) (x : EAlg c) :
    x = algebraMap K (EAlg c) (phiE c x 0 0) +
      algebraMap K (EAlg c) (phiE c x 1 0) * AdjoinRoot.root (sqPoly c) := by
  apply phiE_injective c
  rw [phiE_add_root]
  exact eq_of_commute_jMat hc (phiE_commute c x)

theorem phiE_mem_range (hc : c ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : M * jMat c = jMat c * M) : ∃ x : EAlg c, phiE c x = M :=
  ⟨algebraMap K (EAlg c) (M 0 0) + algebraMap K (EAlg c) (M 1 0) * AdjoinRoot.root (sqPoly c),
    by rw [phiE_add_root]; exact (eq_of_commute_jMat hc hM).symm⟩

theorem add_root_inj {a b a' b' : K}
    (h : algebraMap K (EAlg c) a + algebraMap K (EAlg c) b * AdjoinRoot.root (sqPoly c) =
      algebraMap K (EAlg c) a' + algebraMap K (EAlg c) b' * AdjoinRoot.root (sqPoly c)) :
    a = a' ∧ b = b' := by
  have e := congrArg (phiE c) h
  rw [phiE_add_root, phiE_add_root, smul_add_smul_jMat, smul_add_smul_jMat] at e
  exact ⟨by simpa using congrFun (congrFun e 0) 0, by simpa using congrFun (congrFun e 1) 0⟩

theorem card_EAlg (hc : c ≠ 0) : Nat.card (EAlg c) = Nat.card K ^ 2 := by
  have hbij : Function.Bijective fun x : K × K =>
      algebraMap K (EAlg c) x.1 + algebraMap K (EAlg c) x.2 * AdjoinRoot.root (sqPoly c) := by
    refine ⟨fun x y h => ?_, fun x => ⟨(phiE c x 0 0, phiE c x 1 0), (eq_add_root hc x).symm⟩⟩
    obtain ⟨h1, h2⟩ := add_root_inj h
    exact Prod.ext h1 h2
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, sq]

theorem root_sq : AdjoinRoot.root (sqPoly c) ^ 2 = algebraMap K (EAlg c) c := by
  have h := AdjoinRoot.eval₂_root (sqPoly c)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact sub_eq_zero.1 h

variable [Finite K]

theorem root_pow_card (hK : ringChar K ≠ 2) (hc : ¬ IsSquare c) :
    AdjoinRoot.root (sqPoly c) ^ Nat.card K = -AdjoinRoot.root (sqPoly c) := by
  have : Fintype K := Fintype.ofFinite K
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have hsq : ¬ c ^ (Fintype.card K / 2) = 1 := fun h => hc ((FiniteField.isSquare_iff hK hc0).2 h)
  have hm1 := (FiniteField.pow_dichotomy hK hc0).resolve_left hsq
  have hodd : Nat.card K = 2 * (Fintype.card K / 2) + 1 := by
    have h1 := Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hK)
    have h2 := Fintype.card_pos (α := K)
    rw [Nat.card_eq_fintype_card]
    omega
  rw [hodd, pow_succ, pow_mul, root_sq, ← map_pow, hm1, map_neg, map_one, neg_one_mul]

theorem pow_card_add_root (hK : ringChar K ≠ 2) (hc : ¬ IsSquare c) (a b : K) :
    (algebraMap K (EAlg c) a + algebraMap K (EAlg c) b * AdjoinRoot.root (sqPoly c)) ^
        Nat.card K =
      algebraMap K (EAlg c) a + algebraMap K (EAlg c) (-b) * AdjoinRoot.root (sqPoly c) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hn⟩ := FiniteField.card' K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (EAlg c) p := charP_of_injective_algebraMap (algebraMap K (EAlg c)).injective p
  have hq : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hfrob : ∀ x y : EAlg c, (x + y) ^ Nat.card K = x ^ Nat.card K + y ^ Nat.card K := by
    intro x y
    rw [hq]
    exact add_pow_char_pow x y p n
  have hK' : ∀ a : K, algebraMap K (EAlg c) a ^ Nat.card K = algebraMap K (EAlg c) a := by
    intro a
    rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rw [hfrob, mul_pow, hK', hK', root_pow_card hK hc, map_neg]
  ring

end Field

@[expose] def phiS (h2 : (2 : K) ≠ 0) {s : K} (hs : s ≠ 0) :
    K × K →ₐ[K] Matrix (Fin 2) (Fin 2) K where
  toFun x := ((x.1 + x.2) / 2) • (1 : Matrix (Fin 2) (Fin 2) K) +
    ((x.1 - x.2) / (2 * s)) • jMat (s ^ 2)
  map_one' := by
    rw [smul_add_smul_jMat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [one_add_one_eq_two, h2]
  map_mul' x y := by
    rw [smul_add_smul_jMat, smul_add_smul_jMat, smul_add_smul_jMat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring
  map_zero' := by
    rw [smul_add_smul_jMat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' x y := by
    rw [smul_add_smul_jMat, smul_add_smul_jMat, smul_add_smul_jMat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  commutes' r := by
    have e1 : (algebraMap K (K × K) r).1 = r := rfl
    have e2 : (algebraMap K (K × K) r).2 = r := rfl
    simp only [e1, e2, sub_self, zero_div, zero_smul, add_zero]
    rw [Algebra.algebraMap_eq_smul_one]
    congr 1
    field_simp
    ring

theorem phiS_apply (h2 : (2 : K) ≠ 0) {s : K} (hs : s ≠ 0) (x : K × K) :
    phiS h2 hs x = ((x.1 + x.2) / 2) • (1 : Matrix (Fin 2) (Fin 2) K) +
      ((x.1 - x.2) / (2 * s)) • jMat (s ^ 2) := rfl

theorem phiS_root (h2 : (2 : K) ≠ 0) {s : K} (hs : s ≠ 0) : phiS h2 hs (s, -s) = jMat (s ^ 2) := by
  rw [phiS_apply, smul_add_smul_jMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat] <;> field_simp <;> ring

theorem phiS_injective (h2 : (2 : K) ≠ 0) {s : K} (hs : s ≠ 0) :
    Function.Injective (phiS h2 hs) := by
  intro x y h
  rw [phiS_apply, phiS_apply, smul_add_smul_jMat, smul_add_smul_jMat] at h
  have e0 := congrFun (congrFun h 0) 0
  have e1 := congrFun (congrFun h 1) 0
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at e0 e1
  have e0' := (div_left_inj' h2).1 e0
  have e1' := (div_left_inj' (mul_ne_zero h2 hs)).1 e1
  refine Prod.ext ?_ ?_
  · apply mul_left_cancel₀ h2
    linear_combination e0' + e1'
  · apply mul_left_cancel₀ h2
    linear_combination e0' - e1'

theorem phiS_mem_range (h2 : (2 : K) ≠ 0) {s : K} (hs : s ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : M * jMat (s ^ 2) = jMat (s ^ 2) * M) : ∃ x : K × K, phiS h2 hs x = M := by
  refine ⟨(M 0 0 + M 1 0 * s, M 0 0 - M 1 0 * s), ?_⟩
  rw [phiS_apply]
  conv_rhs => rw [eq_of_commute_jMat (pow_ne_zero 2 hs) hM]
  congr 2
  · field_simp
    ring
  · field_simp
    ring

abbrev swapS : K × K →+* K × K := (RingEquiv.prodComm (R := K) (S := K)).toRingHom

theorem transpose_phiS_mul (h2 : (2 : K) ≠ 0) {s : K} (hs : s ≠ 0) (x : K × K) :
    (phiS h2 hs x)ᵀ * wMat 1 (-(s ^ 2)) = wMat 1 (-(s ^ 2)) * phiS h2 hs (swapS x) := by
  rw [phiS_apply, phiS_apply, transpose_mul_wNeg]
  congr 3
  · change _ = (x.2 + x.1) / 2
    ring
  · change _ = (x.2 - x.1) / (2 * s)
    ring

end CFSG.ComponentClassification.Burgoyne.O
