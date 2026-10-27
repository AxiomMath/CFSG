module

public import CFSG.LocalAnalysis.SectionRank.OddCover.SymSquare
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.SectionRank.OddCover

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K] {m : ℕ}

@[expose] def blk (X : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin (2 + m)) (Fin (2 + m)) K :=
  (fromBlocks X 0 0 Y).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem blk_mul (X X' : Matrix (Fin 2) (Fin 2) K) (Y Y' : Matrix (Fin m) (Fin m) K) :
    blk X Y * blk X' Y' = blk (X * X') (Y * Y') := by
  rw [blk, blk, blk, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blk_transpose (X : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin m) (Fin m) K) :
    (blk X Y)ᵀ = blk Xᵀ Yᵀ := by
  rw [blk, blk, transpose_submatrix, fromBlocks_transpose]
  simp

theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [blk, fromBlocks_one, submatrix_one_equiv]

theorem blk_add (X X' : Matrix (Fin 2) (Fin 2) K) :
    blk (X + X') (0 : Matrix (Fin m) (Fin m) K) = blk X 0 + blk X' 0 := by
  ext i j
  simp only [blk, submatrix_apply, Matrix.add_apply]
  rw [← Matrix.add_apply, fromBlocks_add, add_zero, add_zero, add_zero]

theorem blk_zero : blk (0 : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin m) (Fin m) K) = 0 := by
  rw [blk, fromBlocks_zero]
  rfl

theorem blk_apply_inl (X : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin m) (Fin m) K)
    (i j : Fin 2) :
    blk X Y (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = X i j := by
  simp [blk]

abbrev spJ (m : ℕ) (K : Type) [Field K] :
    Matrix (Fin (2 + m) ⊕ Fin (2 + m)) (Fin (2 + m) ⊕ Fin (2 + m)) K :=
  fromBlocks 0 1 (-1) 0

@[expose] def spUMat (S : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin (2 + m) ⊕ Fin (2 + m)) (Fin (2 + m) ⊕ Fin (2 + m)) K :=
  fromBlocks 1 (blk S 0) 0 1

theorem spUMat_add (S S' : Matrix (Fin 2) (Fin 2) K) :
    spUMat (m := m) (S + S') = spUMat S * spUMat S' := by
  rw [spUMat, spUMat, spUMat, fromBlocks_multiply, blk_add]
  simp only [mul_one, mul_zero, add_zero, one_mul, zero_mul, zero_add]
  rw [add_comm (blk S 0)]

theorem spUMat_zero : spUMat (m := m) (0 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [spUMat, blk_zero, fromBlocks_one]

theorem spUMat_symplectic {S : Matrix (Fin 2) (Fin 2) K} (hS : Sᵀ = S) :
    (spUMat (m := m) S)ᵀ * spJ m K * spUMat S = spJ m K := by
  rw [spUMat, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, blk_transpose, hS]
  simp

@[expose] def spLMat (R N : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin (2 + m) ⊕ Fin (2 + m)) (Fin (2 + m) ⊕ Fin (2 + m)) K :=
  fromBlocks (blk R 1) 0 0 (blk N 1)

theorem spLMat_symplectic {R N : Matrix (Fin 2) (Fin 2) K} (hRN : Rᵀ * N = 1) :
    (spLMat (m := m) R N)ᵀ * spJ m K * spLMat R N = spJ m K := by
  have hNR : Nᵀ * R = 1 := by
    have := congrArg transpose hRN
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  rw [spLMat, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, blk_transpose,
    blk_transpose]
  simp only [add_zero, mul_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, neg_mul,
    blk_mul, hRN, hNR, transpose_one, blk_one, transpose_zero, Matrix.zero_mul, neg_zero]

theorem spLMat_mul_inv {R N : Matrix (Fin 2) (Fin 2) K} (hRN : Rᵀ * N = 1) :
    spLMat (m := m) R N * spLMat Nᵀ Rᵀ = 1 := by
  have hNR : N * Rᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hRN
  have hRN' : R * Nᵀ = 1 := by
    have := congrArg transpose hNR
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  rw [spLMat, spLMat, fromBlocks_multiply]
  simp only [blk_mul, hRN', hNR, Matrix.mul_one, mul_zero, add_zero, zero_mul, zero_add, blk_one,
    fromBlocks_one]

theorem spLMat_mul_spUMat {R N : Matrix (Fin 2) (Fin 2) K} (hRN : Rᵀ * N = 1)
    (S : Matrix (Fin 2) (Fin 2) K) :
    spLMat (m := m) R N * spUMat S = spUMat (R * S * Rᵀ) * spLMat R N := by
  rw [spLMat, spUMat, spUMat, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, mul_zero, add_zero, zero_mul, zero_add, Matrix.one_mul, blk_mul,
    Matrix.mul_assoc, hRN]

section Model

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

abbrev castK (p : ℕ) (K : Type) [Field K] [CharP K p] : ZMod p →+* K :=
  ZMod.castHom (dvd_refl p) K

theorem castK_injective : Function.Injective (castK p K) :=
  (castK p K).injective

@[expose] noncomputable def spUHom (m : ℕ) (K : Type) [Field K] [CharP K p] :
    Multiplicative (symTwo p) →* GL (Fin (2 + m) ⊕ Fin (2 + m)) K :=
  ClassicalOdd.glOfAdd
    (fun B : symTwo p => spUMat ((B : Matrix (Fin 2) (Fin 2) (ZMod p)).map (castK p K)))
    (by rw [AddSubgroup.coe_zero, Matrix.map_zero _ (map_zero _), spUMat_zero])
    (fun B C => by rw [AddSubgroup.coe_add, Matrix.map_add _ (map_add _), spUMat_add])

theorem coe_spUHom (B : Multiplicative (symTwo p)) :
    (spUHom m K B : Matrix (Fin (2 + m) ⊕ Fin (2 + m)) (Fin (2 + m) ⊕ Fin (2 + m)) K) =
      spUMat (((Multiplicative.toAdd B : symTwo p) : Matrix (Fin 2) (Fin 2) (ZMod p)).map
        (castK p K)) :=
  rfl

theorem spUHom_mem (B : Multiplicative (symTwo p)) : spUHom m K B ∈ StatedSp (2 + m) K := by
  refine Subgroup.subset_closure ?_
  change (spUHom m K B).1ᵀ * fromBlocks 0 1 (-1) 0 * (spUHom m K B).1 = fromBlocks 0 1 (-1) 0
  rw [coe_spUHom]
  refine spUMat_symplectic ?_
  rw [← Matrix.transpose_map]
  exact congrArg (fun M => M.map (castK p K)) (Multiplicative.toAdd B).2

@[expose] noncomputable def spPsi (m : ℕ) (K : Type) [Field K] [CharP K p] :
    Multiplicative (symTwo p) →* StatedProj (StatedSp (2 + m) K) :=
  (QuotientGroup.mk' _).comp ((spUHom m K).codRestrict _ spUHom_mem)

theorem spPsi_injective : Function.Injective (spPsi (p := p) m K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro B hB
  rw [MonoidHom.mem_ker, spPsi, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hB
  obtain ⟨c, hc⟩ := hB
  have hcm : Matrix.scalar (Fin (2 + m) ⊕ Fin (2 + m)) (c : K) =
      spUMat (m := m) (((Multiplicative.toAdd B : symTwo p) : Matrix (Fin 2) (Fin 2) (ZMod p)).map
        (castK p K)) := by
    rw [← coe_spUHom, ← GeneralLinearGroup.coe_scalar, hc]
    rfl
  have h00 := congrFun (congrFun hcm (Sum.inl (finSumFinEquiv (Sum.inl 0))))
    (Sum.inl (finSumFinEquiv (Sum.inl 0)))
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, spUMat, fromBlocks_apply₁₁,
    Matrix.one_apply_eq] at h00
  have hB0 : Multiplicative.toAdd B = 0 := by
    apply Subtype.ext
    ext i j
    have hij := congrFun (congrFun hcm (Sum.inl (finSumFinEquiv (Sum.inl i))))
      (Sum.inr (finSumFinEquiv (Sum.inl j)))
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ Sum.inl_ne_inr, spUMat,
      fromBlocks_apply₁₂, blk_apply_inl, Matrix.map_apply] at hij
    apply castK_injective (K := K)
    rw [AddSubgroup.coe_zero, Matrix.zero_apply, map_zero]
    exact hij.symm
  rw [Subgroup.mem_bot, ← ofAdd_toAdd B, hB0, ofAdd_zero]

@[expose] noncomputable def spLGL (m : ℕ) {R N : Matrix (Fin 2) (Fin 2) K} (hRN : Rᵀ * N = 1) :
    GL (Fin (2 + m) ⊕ Fin (2 + m)) K :=
  ⟨spLMat R N, spLMat Nᵀ Rᵀ, spLMat_mul_inv hRN, by
    have hNR : N * Rᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hRN
    have h := spLMat_mul_inv (m := m) (R := Nᵀ) (N := Rᵀ) (by rw [transpose_transpose]; exact hNR)
    rwa [transpose_transpose, transpose_transpose] at h⟩

theorem spLGL_mem {R N : Matrix (Fin 2) (Fin 2) K} (hRN : Rᵀ * N = 1) :
    spLGL m hRN ∈ StatedSp (2 + m) K :=
  Subgroup.subset_closure (spLMat_symplectic hRN)

theorem spLGL_conj {R N : Matrix (Fin 2) (Fin 2) (ZMod p)} (hRN : Rᵀ * N = 1)
    (hRN' : (R.map (castK p K))ᵀ * N.map (castK p K) = 1) (B : Multiplicative (symTwo p)) :
    spLGL m hRN' * spUHom m K B * (spLGL m hRN')⁻¹ =
      spUHom m K (Multiplicative.ofAdd (symConj R (Multiplicative.toAdd B))) := by
  have _ := hRN
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_spUHom, coe_spUHom, toAdd_ofAdd, coe_symConj]
  change spLMat _ _ * spUMat _ = spUMat _ * spLMat _ _
  rw [spLMat_mul_spUMat hRN', Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

end Model

theorem symD_transpose_mul {p : ℕ} : (symD p)ᵀ * symD p = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, symD]

theorem symS_transpose_mul {p : ℕ} : (symS p)ᵀ * symS p = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, symS]

theorem symT_transpose_mul {p : ℕ} : (symT p)ᵀ * !![1, -1; 0, 1] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, symT]

theorem odd_symplectic_central_cover_rank_three {G : Type} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] (hAZ : A ≤ Subgroup.center G) {n p f : ℕ} (hp2 : p ≠ 2)
    (h : StatedClassicalModel (G ⧸ A) .PSp n p f) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) ∧ ¬ IsStronglyQuasithin G := by
  obtain ⟨⟨hp, -, hn2, -⟩, K, _, _, hK, ⟨θ⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  set ρ : G →* StatedProj (StatedSp (2 + m) K) := θ.toMonoidHom.comp (QuotientGroup.mk' A)
  have hρ : Function.Surjective ρ := θ.surjective.comp (QuotientGroup.mk'_surjective A)
  have hker : ρ.ker = A := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ θ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmapRN : ∀ {R N : Matrix (Fin 2) (Fin 2) (ZMod p)}, Rᵀ * N = 1 →
      (R.map (castK p K))ᵀ * N.map (castK p K) = 1 := fun {R N} hRN => by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, hRN, Matrix.map_one _ (map_zero _) (map_one _)]
  let lev : ∀ {R N : Matrix (Fin 2) (Fin 2) (ZMod p)}, Rᵀ * N = 1 →
      StatedProj (StatedSp (2 + m) K) := fun hRN =>
    QuotientGroup.mk ⟨spLGL m (hmapRN hRN), spLGL_mem _⟩
  have hlev : ∀ {R N : Matrix (Fin 2) (Fin 2) (ZMod p)} (hRN : Rᵀ * N = 1) (B),
      lev hRN * spPsi m K B * (lev hRN)⁻¹ =
        spPsi m K (Multiplicative.ofAdd (symConj R (Multiplicative.toAdd B))) := by
    intro R N hRN B
    change (QuotientGroup.mk' _ _ * QuotientGroup.mk' _ _ * (QuotientGroup.mk' _ _)⁻¹ :
      StatedProj (StatedSp (2 + m) K)) = QuotientGroup.mk' _ _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.codRestrict_apply]
    exact spLGL_conj hRN (hmapRN hRN) B
  have h3 := three_le_pRank_of_symmetric_square hp2 A hAZ ρ hρ hker (spPsi m K) spPsi_injective
    (lev symD_transpose_mul) (lev symS_transpose_mul) (lev symT_transpose_mul)
    (hlev symD_transpose_mul) (hlev symS_transpose_mul) (hlev symT_transpose_mul)
  refine ⟨h3, fun hSQT => ?_⟩
  have := (isStronglyQuasithin_iff.1 hSQT) p hp hp2
  omega

end CFSG.SectionRank.OddCover
