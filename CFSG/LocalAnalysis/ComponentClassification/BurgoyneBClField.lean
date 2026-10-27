module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClEmb
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLBlocks
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBFinal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBTypeInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL4

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ComponentClassification.Burgoyne.PSL (fixField fieldFixedSL range_map_fixField
  map_fixField_injective gfLift fieldAut_mul_dualAut_proj unitarySL mem_unitarySL
  gfLift_eq_iff isQuasisimple_unitarySL)
open CFSG.ComponentClassification.CatLeafProof.EndOddLin (slBlkR coe_slBlkR blkMatR blkMatR_mul
  blkMatR_one blkMatR_castAdd blkMatR_natAdd coe_neg_one_SL2' QuatBlock quatBlock_map_of_sl2)
open scoped MatrixGroups

theorem ringChar_subfield_ne_two {K : Type*} [Field K] (hK : ringChar K ≠ 2) (L : Subfield K) :
    ringChar L ≠ 2 := by
  intro h
  have h2 : (2 : L) = 0 := by
    have := ringChar.spec L 2
    exact_mod_cast this.2 (by rw [h])
  exact Ring.two_ne_zero hK (by rw [← map_ofNat L.subtype 2, h2, map_zero])

theorem not_mem_scalars_of_diag {n : ℕ} {K : Type*} [Field K]
    {g : SpecialLinearGroup (Fin n) K} {i j : Fin n}
    (h : (g : Matrix (Fin n) (Fin n) K) i i ≠ (g : Matrix (Fin n) (Fin n) K) j j) :
    g ∉ scalars n K := by
  rintro ⟨c, -, hc⟩
  apply h
  rw [hc, scalar_apply, diagonal_apply_eq, diagonal_apply_eq]

section Blk

variable {R S : Type*} [CommRing R] [CommRing S] (m : ℕ)

theorem blkMatR_map {f : R → S} (h0 : f 0 = 0) (h1 : f 1 = 1) (g : Matrix (Fin 2) (Fin 2) R) :
    (blkMatR m g).map f = blkMatR m (g.map f) := by
  rw [blkMatR, blkMatR, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_zero _ h0,
    Matrix.map_zero _ h0, Matrix.map_one _ h0 h1]

theorem blkMatR_transpose (g : Matrix (Fin 2) (Fin 2) R) :
    (blkMatR m g)ᵀ = blkMatR m gᵀ := by
  rw [blkMatR, blkMatR, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, transpose_zero,
    transpose_zero, transpose_one]

theorem slBlkR_neg_one_not_mem_scalars {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (hm : 1 ≤ m) :
    slBlkR m (-1 : SL(2, K)) ∉ scalars (2 + m) K := by
  refine not_mem_scalars_of_diag (i := Fin.castAdd m 0) (j := Fin.natAdd 2 ⟨0, hm⟩) ?_
  have e1 : ((slBlkR m (-1 : SL(2, K)) : SL(2 + m, K)) : Matrix (Fin (2 + m)) (Fin (2 + m)) K)
      (Fin.castAdd m 0) (Fin.castAdd m 0) = -1 := by
    rw [coe_slBlkR, blkMatR_castAdd, coe_neg_one_SL2']
    simp
  have e2 : ((slBlkR m (-1 : SL(2, K)) : SL(2 + m, K)) : Matrix (Fin (2 + m)) (Fin (2 + m)) K)
      (Fin.natAdd 2 ⟨0, hm⟩) (Fin.natAdd 2 ⟨0, hm⟩) = 1 := by
    rw [coe_slBlkR, blkMatR_natAdd]
  rw [e1, e2]
  intro h
  apply h2
  linear_combination -h

end Blk

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem quatBlock_fieldFixed (hK : ringChar K ≠ 2) (hn : 3 ≤ n) (σ : K ≃+* K) :
    QuatBlock ((fieldFixedSL n σ).map (QuotientGroup.mk' (scalars n K))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have hE : IsQuasisimple (fieldFixedSL (2 + m) σ) := by
    rw [← range_map_fixField]
    exact LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (map_fixField_injective (n := 2 + m) σ))
      (CatalogueBGeneralLinear.specialLinear_quasisimple (2 + m) (fixField σ) (by omega)
        (Or.inl (by omega)) (Or.inl (by omega)))
  refine quatBlock_map_of_sl2 hE (ringChar_subfield_ne_two hK (fixField σ))
    ((SpecialLinearGroup.map (fixField σ).subtype).comp (slBlkR m)) (fun g => ?_) ?_
  · rw [← range_map_fixField]
    exact ⟨_, rfl⟩
  · intro hmem
    refine not_mem_scalars_of_diag (i := Fin.castAdd m 0) (j := Fin.natAdd 2 ⟨0, hm⟩) ?_ hmem
    rw [MonoidHom.comp_apply, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.map_apply, coe_slBlkR, blkMatR_castAdd, blkMatR_natAdd,
      coe_neg_one_SL2', Matrix.neg_apply, Matrix.one_apply_eq]
    intro h
    apply h2
    rw [map_neg, map_one] at h
    linear_combination -h

theorem noL2At_fieldAut (hK : ringChar K ≠ 2) (hn : 3 ≤ n) (σ : K ≃+* K) :
    NoL2At (fieldAut n K σ) :=
  noL2At_of_fix (scalars_le_center n K) (fun g => fieldAut_proj σ g)
    (quatBlock_fieldFixed hK hn σ)

theorem noL2At_field {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = p ^ f) (hn : 3 ≤ n) {A : GL (Fin n) K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1) :
    NoL2At (conjAut n K A * fieldAut n K σ) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨H, hH⟩ := LocalAnalysis.ComponentInitial.OddHigherLinear.field_involution_conjugacy
    hp hp2 hf hKc hn A σ hσ hα
  refine NoL2At.of_conj (conjAut n K H)⁻¹ ?_
  have e : (conjAut n K H)⁻¹ * (conjAut n K A * fieldAut n K σ) * (conjAut n K H)⁻¹⁻¹ =
      fieldAut n K σ := by
    rw [hH]
    group
  rw [e]
  exact noL2At_fieldAut hK hn σ

section GraphField

variable {p e : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem fixOf_gfLift {σ : K ≃+* K} (hσσ : ∀ x, σ (σ x) = x) :
    fixOf (gfLift (n := n) σ) = unitarySL n σ := by
  ext g
  exact gfLift_eq_iff hσσ g

omit [Finite K] in
theorem slBlkR_mem_unitarySL {m : ℕ} {σ : K ≃+* K} {g : SL(2, K)}
    (hg : conjTr σ (g : Matrix (Fin 2) (Fin 2) K) * g = 1) :
    slBlkR m g ∈ unitarySL (2 + m) σ := by
  rw [mem_unitarySL, coe_slBlkR, conjTr, blkMatR_map m (map_zero σ) (map_one σ),
    blkMatR_transpose, blkMatR_mul, ← conjTr, hg, blkMatR_one]

theorem quatBlock_unitarySL (hp2 : p ≠ 2) (hKe : Nat.card K = (p ^ e) ^ 2) (hn : 3 ≤ n) :
    QuatBlock ((unitarySL n (unitaryInvolution K p e)).map
      (QuotientGroup.mk' (scalars n K))) := by
  set σ := unitaryInvolution K p e with hσdef
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  obtain ⟨η, hη0, hση⟩ := exists_unitaryInvolution_eq_neg hKe
  replace hση : σ η = -η := hση
  have hc : σ (-(η ^ 2)⁻¹) = -(η ^ 2)⁻¹ := by
    rw [map_neg, map_inv₀, map_pow, hση, neg_sq]
  obtain ⟨a, b, hab⟩ := LocalAnalysis.ComponentInitial.finite_odd_field_two_squares
    (ringChar_subfield_ne_two hK (fixField σ)) (⟨-(η ^ 2)⁻¹, hc⟩ : fixField σ)
  set s : K := (a : K) with hs
  set t : K := (b : K) with ht
  have hσs : σ s = s := a.2
  have hσt : σ t = t := b.2
  have hst : s ^ 2 + t ^ 2 = -(η ^ 2)⁻¹ := by
    have := congrArg (fun x : fixField σ => (x : K)) hab
    simpa [hs, ht] using this
  have hst' : η ^ 2 * (s ^ 2 + t ^ 2) = -1 := by
    rw [hst]
    field_simp
  set X : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0] with hX
  set Y : Matrix (Fin 2) (Fin 2) K := !![η * s, η * t; η * t, -(η * s)] with hY
  have hXd : X.det = 1 := by rw [hX, det_fin_two_of]; ring
  have hYd : Y.det = 1 := by rw [hY, det_fin_two_of]; linear_combination -hst'
  set x₂ : SL(2, K) := ⟨X, hXd⟩
  set y₂ : SL(2, K) := ⟨Y, hYd⟩
  have hXX : X * X = -1 := by
    rw [hX]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hYY : Y * Y = -1 := by
    rw [hY]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hst'
  have hXY : X * Y = -(Y * X) := by
    rw [hX, hY]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hXU : conjTr σ X * X = 1 := by
    rw [conjTr, hX]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hYU : conjTr σ Y * Y = 1 := by
    rw [conjTr, hY]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hση, hσs, hσt] <;>
      first | ring1 | linear_combination -hst'
  have hx2 : x₂ ^ 2 = -1 := Subtype.ext (by rw [pow_two]; exact hXX)
  have hy2 : y₂ ^ 2 = -1 := Subtype.ext (by rw [pow_two]; exact hYY)
  have hxy : x₂ * y₂ = -1 * (y₂ * x₂) := Subtype.ext (by
    change X * Y = ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (Y * X)
    rw [coe_neg_one_SL2', Matrix.neg_mul, Matrix.one_mul]
    exact hXY)
  have hz2 : (-1 : SL(2, K)) ^ 2 = 1 := by rw [neg_one_sq]
  refine quatBlock_map_of_pair (isQuasisimple_unitarySL hp2 hKe hn)
    (x := slBlkR m x₂) (y := slBlkR m y₂) (z := slBlkR m (-1))
    (slBlkR_mem_unitarySL hXU) (slBlkR_mem_unitarySL hYU)
    (by rw [← map_pow, hz2, map_one]) (by rw [← map_pow, hx2]) (by rw [← map_pow, hy2])
    (by rw [← map_mul, ← map_mul, ← map_mul, hxy]) (slBlkR_neg_one_not_mem_scalars m h2 hm)

theorem noL2At_fieldAut_mul_dualAut (hp2 : p ≠ 2) (hKe : Nat.card K = (p ^ e) ^ 2)
    (hn : 3 ≤ n) : NoL2At (fieldAut n K (unitaryInvolution K p e) * dualAut n K) := by
  have hσσ : ∀ x, unitaryInvolution K p e (unitaryInvolution K p e x) = x :=
    unitaryInvolution_involutive hKe
  refine noL2At_of_fix (scalars_le_center n K)
    (fun g => fieldAut_mul_dualAut_proj (unitaryInvolution K p e) g) ?_
  rw [fixOf_gfLift hσσ]
  exact quatBlock_unitarySL hp2 hKe hn

end GraphField

theorem noL2At_graphField {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = p ^ f) (hn : 3 ≤ n) {A : GL (Fin n) K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hα : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    NoL2At (conjAut n K A * fieldAut n K σ * dualAut n K) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  obtain ⟨hfe, hσp, H, hH⟩ :=
    LocalAnalysis.ComponentInitial.LinearFlag.odd_linear_graph_field_involution_conjugacy hp hf
      hKc hn A σ hσ hα
  obtain ⟨e, he⟩ : ∃ e, f = 2 * e := ⟨f / 2, by obtain ⟨k, hk⟩ := hfe; omega⟩
  have hKe : Nat.card K = (p ^ e) ^ 2 := by rw [hKc, he, ← pow_mul, mul_comm]
  have hσe : σ = unitaryInvolution K p e := by
    ext x
    rw [hσp, unitaryInvolution_apply, he, Nat.mul_div_cancel_left _ two_pos]
  refine NoL2At.of_conj (conjAut n K H)⁻¹ ?_
  have e' : (conjAut n K H)⁻¹ * (conjAut n K A * fieldAut n K σ * dualAut n K) *
      (conjAut n K H)⁻¹⁻¹ = fieldAut n K σ * dualAut n K := by
    rw [hH]
    group
  rw [e', hσe]
  exact noL2At_fieldAut_mul_dualAut hp2 hKe hn

end CFSG.ComponentClassification.Burgoyne.Cl
