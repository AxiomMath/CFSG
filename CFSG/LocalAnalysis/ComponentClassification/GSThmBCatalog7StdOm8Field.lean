module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {K : Type} [Field K] {d : ℕ}

@[expose] def gram (Q : QuadraticForm K (Fin d → K)) : Matrix (Fin d) (Fin d) K :=
  LinearMap.toMatrix₂' K Q.polarBilin

theorem gram_apply (Q : QuadraticForm K (Fin d → K)) (i j : Fin d) :
    gram Q i j = Q.polarBilin (Pi.single i 1) (Pi.single j 1) := rfl

theorem gram_similarity (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q) :
    (g.val.left : Matrix (Fin d) (Fin d) K)ᵀ * gram Q * (g.val.left : Matrix (Fin d) (Fin d) K) =
      (multiplier Q g : K) • (gram Q).map g.val.right := by
  set A := (g.val.left : Matrix (Fin d) (Fin d) K)
  have hform := CatalogueBOrthogonalFieldFixed.semilinear_polar_similarity Q g.val.right
    (coordinateSemilinearMap g.val) (multiplier Q g) (multiplier_spec Q g)
  have h1 : Aᵀ * gram Q * A =
      LinearMap.toMatrix₂' K (Q.polarBilin.compl₁₂ (Matrix.toLin' A) (Matrix.toLin' A)) := by
    rw [LinearMap.toMatrix₂'_compl₁₂, LinearMap.toMatrix'_toLin']
    rfl
  rw [h1]
  ext i j
  have hs : ∀ k : Fin d, A *ᵥ Pi.single k 1 = coordinateSemilinearMap g.val (Pi.single k 1) := by
    intro k
    rw [coordinateSemilinearMap_apply]
    congr 1
    funext l
    by_cases hl : l = k
    · subst hl
      simp
    · simp [hl]
  rw [LinearMap.toMatrix₂'_apply, LinearMap.compl₁₂_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply, hs, hs, hform]
  rfl

theorem isSquare_det_gram_of_field_pair [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hd : Even d) (Q : QuadraticForm K (Fin d → K))
    (hnd : Q.polarBilin.Nondegenerate) (hD : (gram Q).det ≠ 0) (g : similarityPairs Q)
    (hσ2 : g.val.right ^ 2 = 1) (hσ1 : g.val.right ≠ 1) (c : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c) :
    IsSquare (gram Q).det := by
  have : Fintype K := Fintype.ofFinite K
  set σ := g.val.right with hσdef
  set A := (g.val.left : Matrix (Fin d) (Fin d) K) with hAdef
  set μ := (multiplier Q g : K) with hμdef
  set D := (gram Q).det with hDdef
  set δ := A.det with hδdef
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hμ0 : μ ≠ 0 := Units.ne_zero _
  have hc0 : (c : K) ≠ 0 := Units.ne_zero c
  obtain ⟨hcardk, -⟩ := CatalogueBOrthogonalInvolutionRepresentation.field_involution_facts hp hf
    hK hσ2 hσ1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (show Nat.card {x : K // σ x = x} ∣ p ^ f from hK ▸ hcardk ▸ dvd_pow_self _ two_ne_zero)
  have hfj : f = 2 * j := by
    have h1 : p ^ f = p ^ (2 * j) := by rw [← hK, hcardk, hj, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective hp.two_le h1
  have hj1 : 1 ≤ j := by omega
  have hU : LocalAnalysis.ComponentInitial.UnitaryFieldData p j K :=
    ⟨hp, hj1, by rw [hK, hfj]⟩
  have hσσ : σ * σ = 1 := by rw [← pow_two]; exact hσ2
  have hbar : ∀ x, σ x = x ^ (p ^ j) := by
    rcases LocalAnalysis.ComponentInitial.UnitaryHigher.ringEquiv_eq_refl_or_bar hU hσσ with h | h
    · exact absurd h hσ1
    · intro x
      rw [h x]
      rfl
  set q := p ^ j with hqdef
  have hqodd : Odd q := (hp.odd_of_ne_two hp2).pow
  have hdet1 : δ * D * δ = μ ^ d * σ D := by
    have h := congrArg Matrix.det (gram_similarity Q g)
    rw [det_mul, det_mul, det_transpose, det_smul, Fintype.card_fin] at h
    have hσD : σ D = ((gram Q).map σ).det := RingHom.map_det σ.toRingHom (gram Q)
    rw [hσD]
    exact h
  have hdet2 : δ * σ δ = (c : K) ^ d := by
    have h := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K).det) hc
    simp only [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar] at h
    have hsc : ((Matrix.scalar (Fin d)) (c : K)).det = (c : K) ^ d := by
      simp [Matrix.scalar_apply, det_diagonal, Finset.prod_const]
    rw [hsc] at h
    rw [← h]
    congr 1
    change σ δ = (σ.toRingHom.mapMatrix A).det
    exact RingHom.map_det σ.toRingHom A
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    exact ⟨1, by simp [D]⟩
  have : Nontrivial (Fin d → K) :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [Module.finrank_fin_fun]; exact hd0)
  have hmuc : μ * σ μ = (c : K) ^ 2 :=
    CatalogueBOrthogonalDescent.square_multiplier_identity σ hσ2 Q.polarBilin hnd
      (coordinateSemilinearMap g.val) μ (c : K)
      (CatalogueBOrthogonalFieldFixed.semilinear_polar_similarity Q σ
        (coordinateSemilinearMap g.val) (multiplier Q g) (multiplier_spec Q g))
      (CatalogueBOrthogonalFixedTransfer.coordinateSemilinearMap_sq_apply g.val c hσ2 hc)
  rw [hbar] at hdet1 hdet2 hmuc
  have hδ0 : δ ≠ 0 := by
    rw [hδdef, hAdef]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g.val.left) |>.ne_zero
  obtain ⟨k, hk⟩ := hqodd
  obtain ⟨d', hd'⟩ := hd
  have hq1 : q + 1 = 2 * (k + 1) := by omega
  have hδpow : δ ^ (2 * (k + 1)) = (c : K) ^ d := by
    rw [← hq1, pow_succ, mul_comm]
    exact hdet2
  have hμpow : μ ^ (d * (k + 1)) = (c : K) ^ d := by
    rw [hd', show (d' + d') * (k + 1) = 2 * (k + 1) * d' by ring, pow_mul, ← hq1, pow_succ,
      mul_comm, hmuc, ← pow_mul, show 2 * d' = d' + d' by ring]
  have hpow : (c : K) ^ d * D ^ (k + 1) = (c : K) ^ d * D ^ (q * (k + 1)) := by
    have h := congrArg (fun x : K => x ^ (k + 1)) hdet1
    rw [show δ * D * δ = δ ^ 2 * D by ring, mul_pow, mul_pow, ← pow_mul, ← pow_mul, hδpow,
      hμpow, ← pow_mul] at h
    exact h
  have hpow' : D ^ (k + 1) = D ^ (q * (k + 1)) := mul_left_cancel₀ (pow_ne_zero _ hc0) hpow
  have hfin : D ^ (2 * k * (k + 1)) = 1 := by
    have h3 : D ^ (q * (k + 1)) = D ^ (k + 1) * D ^ (2 * k * (k + 1)) := by
      rw [← pow_add]
      congr 1
      rw [hk]
      ring
    have h4 := hpow'.trans h3
    exact (mul_left_cancel₀ (pow_ne_zero (k + 1) hD) (h4.symm.trans (mul_one _).symm))
  rw [FiniteField.isSquare_iff hK2 hD]
  have hcardq : Fintype.card K = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hK, hfj, hqdef, ← pow_mul, mul_comm]
  have hcard2 : Fintype.card K / 2 = 2 * k * (k + 1) := by
    rw [hcardq, hk, show (2 * k + 1) ^ 2 = 1 + 2 * (2 * k * (k + 1)) by ring,
      Nat.add_mul_div_left _ _ two_pos]
    simp
  rw [hcard2]
  exact hfin

@[expose] def pairIndex (m : ℕ) : (Fin 2 × Fin m) ⊕ Fin 2 ≃ Fin m ⊕ Fin m ⊕ Fin 2 where
  toFun x := match x with
    | .inl (a, i) => if a = 0 then .inl i else .inr (.inl i)
    | .inr j => .inr (.inr j)
  invFun y := match y with
    | .inl i => .inl (0, i)
    | .inr (.inl i) => .inl (1, i)
    | .inr (.inr j) => .inr j
  left_inv x := by
    rcases x with ⟨a, i⟩ | j
    · fin_cases a <;> rfl
    · rfl
  right_inv y := by
    rcases y with i | i | j <;> rfl

open CFSG.LieType.Universal.Spin in
theorem polar_quadMinus_pairIndex (n : ℕ) (b c : K) (x y : (Fin 2 × Fin (n - 1)) ⊕ Fin 2) :
    QuadraticMap.polar (quadMinus n K b c) (Pi.single (pairIndex (n - 1) x) 1)
      (Pi.single (pairIndex (n - 1) y) 1) =
      Matrix.fromBlocks (blockDiagonal fun _ : Fin (n - 1) => !![(0 : K), 1; 1, 0]) 0 0
        !![2, b; b, 2 * c] x y := by
  rcases x with ⟨a, i⟩ | j <;> rcases y with ⟨a', i'⟩ | j'
  · fin_cases a <;> fin_cases a' <;>
      simp [pairIndex, polar_quadMinus, Pi.single_apply, blockDiagonal_apply', eq_comm]
  · fin_cases a <;> fin_cases j' <;> simp [pairIndex, polar_quadMinus]
  · fin_cases j <;> fin_cases a' <;> simp [pairIndex, polar_quadMinus]
  · fin_cases j <;> fin_cases j' <;> rw [polar_quadMinus] <;> simp [pairIndex]

theorem det_gram_coordinateQuadMinus (n : ℕ) (hn : 1 ≤ n) (b c : K) :
    (gram (coordinateQuadMinus n K hn b c)).det = (-1) ^ (n - 1) * (4 * c - b ^ 2) := by
  set ε := (pairIndex (n - 1)).trans (minusIndexEquiv n hn)
  have hsub : (gram (coordinateQuadMinus n K hn b c)).submatrix ε ε =
      Matrix.fromBlocks (blockDiagonal fun _ : Fin (n - 1) => !![(0 : K), 1; 1, 0]) 0 0
        !![2, b; b, 2 * c] := by
    ext x y
    rw [submatrix_apply, gram_apply, ← polar_quadMinus_pairIndex n b c x y]
    have hv : ∀ z, (CatalogueBOrthogonalPointData.reindexVectorEquiv (K := K)
        (minusIndexEquiv n hn)).symm (Pi.single (ε z) 1) = Pi.single (pairIndex (n - 1) z) 1 := by
      intro z
      funext i
      rw [CatalogueBOrthogonalPointData.reindexVectorEquiv_symm_apply]
      simp only [ε, Equiv.trans_apply, Pi.single_apply, (minusIndexEquiv n hn).apply_eq_iff_eq]
    rw [QuadraticMap.polarBilin_apply_apply, coordinateQuadMinus, reindexQuadraticForm]
    simp only [QuadraticMap.polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_add, hv]
  rw [← det_submatrix_equiv_self ε, hsub, det_fromBlocks_zero₂₁, det_blockDiagonal, det_fin_two_of]
  simp only [det_fin_two_of, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem not_isSquare_disc (h2 : (2 : K) ≠ 0) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ IsSquare (b ^ 2 - 4 * c) := by
  rintro ⟨t, ht⟩
  apply hirr ((t - b) / 2)
  field_simp
  linear_combination (-1 : K) * ht

theorem false_of_field_pair [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hnd : (coordinateQuadMinus 4 K (by norm_num) b c).polarBilin.Nondegenerate)
    (g : similarityPairs (coordinateQuadMinus 4 K (by norm_num) b c))
    (hσ2 : g.val.right ^ 2 = 1) (hσ1 : g.val.right ≠ 1) (c' : Kˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin (2 * 4)) K g.val.right
      g.val.left = GeneralLinearGroup.scalar (Fin (2 * 4)) c') : False := by
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hdet := det_gram_coordinateQuadMinus 4 (by norm_num) b c
  have hdisc : (gram (coordinateQuadMinus 4 K (by norm_num) b c)).det = b ^ 2 - 4 * c := by
    rw [hdet]
    norm_num
  have hns := not_isSquare_disc h2 hirr
  rw [← hdisc] at hns
  have hD : (gram (coordinateQuadMinus 4 K (by norm_num) b c)).det ≠ 0 := by
    intro h0
    exact hns ⟨0, by rw [h0, mul_zero]⟩
  exact hns (isSquare_det_gram_of_field_pair hp hp2 hf hK ⟨4, rfl⟩ _ hnd hD g hσ2 hσ1 c' hc)

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
