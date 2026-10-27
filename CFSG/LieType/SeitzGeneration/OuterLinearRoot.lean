module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLTv

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP

section Algebra

theorem commutator_aux {R : Type*} [Ring R] (A B : R) (hAA : A * A = 0) (hBB : B * B = 0)
    (hBA : B * A = 0) : (1 + A) * (1 + B) * ((1 - A) * (1 - B)) = 1 + A * B := by
  have h1 : A * (A * B) = 0 := by rw [← mul_assoc, hAA, zero_mul]
  have h2 : B * (A * B) = 0 := by rw [← mul_assoc, hBA, zero_mul]
  have h3 : A * B * A = 0 := by rw [mul_assoc, hBA, mul_zero]
  have h4 : A * B * B = 0 := by rw [mul_assoc, hBB, mul_zero]
  have h5 : A * B * (A * B) = 0 := by rw [← mul_assoc, h3, zero_mul]
  have e : (1 + A) * (1 + B) * ((1 - A) * (1 - B)) = 1 + A * B +
      (-(A * A) + A * (A * B) - B * A - B * B + B * (A * B) - A * B * A - A * B * B +
        A * B * (A * B)) := by noncomm_ring
  rw [e, hAA, h1, hBA, hBB, h2, h3, h4, h5]
  simp

end Algebra

section Tv

variable {n : ℕ} {K : Type} [Field K]

theorem tv_inv (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0) :
    (tv v φ h)⁻¹ = tv v (-φ) (by rw [neg_dotProduct, h, neg_zero]) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, tv_coe, tv_coe, Matrix.SpecialLinearGroup.coe_one,
    vecMulVec_neg]
  have hAA : vecMulVec v φ * vecMulVec v φ = 0 := by
    rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]
  have e : (1 + vecMulVec v φ) * (1 + -vecMulVec v φ) =
      1 - vecMulVec v φ * vecMulVec v φ := by noncomm_ring
  rw [e, hAA, sub_zero]

theorem commutator_tv_single {i₀ j l : Fin n} (hli : l ≠ i₀) (hlj : l ≠ j) {γ : Fin n → K}
    (hγ : γ ⬝ᵥ Pi.single i₀ 1 = 0) :
    tv (Pi.single i₀ 1) γ hγ * tv (Pi.single j 1) (Pi.single l 1) (by simp [hlj]) *
        (tv (Pi.single i₀ 1) γ hγ)⁻¹ * (tv (Pi.single j 1) (Pi.single l 1) (by simp [hlj]))⁻¹ =
      SpecialLinearGroup.transvection (Ne.symm hli) (γ j) := by
  have hψj : (Pi.single l 1 : Fin n → K) ⬝ᵥ Pi.single j 1 = 0 := by simp [hlj]
  rw [tv_inv, tv_inv, transvection_eq_tv (Ne.symm hli)]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, tv_coe]
  set A : Matrix (Fin n) (Fin n) K := vecMulVec (Pi.single i₀ 1) γ with hA
  set B : Matrix (Fin n) (Fin n) K := vecMulVec (Pi.single j 1) (Pi.single l 1) with hB
  have hAA : A * A = 0 := by
    rw [hA, vecMulVec_mul_vecMulVec, hγ, zero_smul, vecMulVec_zero]
  have hBB : B * B = 0 := by
    rw [hB, vecMulVec_mul_vecMulVec, hψj, zero_smul, vecMulVec_zero]
  have hBA : B * A = 0 := by
    rw [hB, hA, vecMulVec_mul_vecMulVec]
    simp [hli]
  have hAB : A * B = vecMulVec (Pi.single i₀ 1) (γ j • (Pi.single l 1 : Fin n → K)) := by
    rw [hA, hB, vecMulVec_mul_vecMulVec, dotProduct_single_one, vecMulVec_smul]
  have e1 : (1 + vecMulVec (Pi.single i₀ 1) (-γ)) = 1 - A := by
    rw [vecMulVec_neg, hA]
    abel
  have e2 : (1 + vecMulVec (Pi.single j 1) (-(Pi.single l 1 : Fin n → K))) = 1 - B := by
    rw [vecMulVec_neg, hB]
    abel
  rw [e1, e2, Matrix.mul_assoc ((1 + A) * (1 + B)) (1 - A) (1 - B),
    commutator_aux A B hAA hBB hBA, hAB]

end Tv

section Rational

variable {n : ℕ} {K : Type} [Field K] {k : Subfield K}
  {H : Subgroup (SpecialLinearGroup (Fin n) K)}

theorem root_mem_of_tv_single_free (hk : slSub n k ≤ H) (hn : 3 ≤ n) {i₀ : Fin n}
    {γ : Fin n → K} (hγ : γ ⬝ᵥ Pi.single i₀ 1 = 0) (hmem : tv (Pi.single i₀ 1) γ hγ ∈ H)
    (j : Fin n) :
    ∃ l, ∃ hl : i₀ ≠ l, SpecialLinearGroup.transvection hl (γ j) ∈ H := by
  obtain ⟨l, hl1, hl2⟩ := exists_fin_ne_ne' hn i₀ j
  refine ⟨l, hl1.symm, ?_⟩
  have hjl : j ≠ l := hl2.symm
  have hψ : (Pi.single l 1 : Fin n → K) ⬝ᵥ Pi.single j 1 = 0 := by simp [hl2]
  have hs : tv (Pi.single j 1) (Pi.single l 1) hψ ∈ H := by
    have h0 : SpecialLinearGroup.transvection hjl (1 : K) ∈ H :=
      hk (transvection_mem_slSub hjl k.one_mem)
    rw [transvection_eq_tv hjl 1] at h0
    exact tv_mem_congr (one_smul K _) _ hψ h0
  have h1 := H.mul_mem (H.mul_mem (H.mul_mem hmem hs) (H.inv_mem hmem)) (H.inv_mem hs)
  rw [commutator_tv_single hl1 hl2 hγ] at h1
  exact h1

theorem eq_top_of_tv_irrational [Finite K] (hk : slSub n k ≤ H) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hK : Nat.card K = Nat.card k ^ p) {w φ : Fin n → K} (hw : ∀ i, w i ∈ k)
    (hw0 : w ≠ 0) (hφw : φ ⬝ᵥ w = 0) (hφ : ∃ j, φ j ∉ k) (hmem : tv w φ hφw ∈ H) : H = ⊤ := by
  let i₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨g, hgk, c, hck, hc0, hge⟩ := exists_slSub_mulVec_eq_smul_single hw hw0 i₀
  have hconj : g * tv w φ hφw * g⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (hk hgk) hmem) (H.inv_mem (hk hgk))
  rw [conj_tv g hφw] at hconj
  set φ₁ : Fin n → K := φ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hφ₁
  have hd := dot_conj g w φ
  rw [hge, dotProduct_smul, hφw, smul_eq_mul] at hd
  have hφ1 : φ₁ ⬝ᵥ (Pi.single i₀ 1 : Fin n → K) = 0 := (mul_eq_zero.mp hd).resolve_left hc0
  have hγ'e : (c • φ₁) ⬝ᵥ (Pi.single i₀ 1 : Fin n → K) = 0 := by
    rw [smul_dotProduct, hφ1, smul_zero]
  have h1 : tv (Pi.single i₀ 1) (c • φ₁) hγ'e ∈ H := by
    have heq : tv ((g : Matrix (Fin n) (Fin n) K) *ᵥ w) φ₁ (by rw [hφ₁, dot_conj, hφw]) =
        tv (Pi.single i₀ 1) (c • φ₁) hγ'e :=
      (tv_eq_of_eq hge rfl _ (by rw [dotProduct_smul, hφ1, smul_zero])).trans (tv_smul c hφ1)
    exact heq ▸ hconj
  have hγeq : (c • φ₁) ᵥ* ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • φ := by
    rw [smul_vecMul, hφ₁, vecMul_vecMul, coe_inv_mul_self, vecMul_one]
  obtain ⟨j, hj⟩ : ∃ j, (c • φ₁) j ∉ k := by
    by_contra hall
    push Not at hall
    obtain ⟨m, hm⟩ := hφ
    apply hm
    have hcm : c * φ m ∈ k := by
      have h2 := congrFun hγeq m
      rw [Pi.smul_apply, smul_eq_mul] at h2
      rw [← h2, Matrix.vecMul, dotProduct]
      exact k.sum_mem fun i _ => k.mul_mem (hall i) ((mem_slSub.mp hgk) i m)
    have : φ m = c⁻¹ * (c * φ m) := by field_simp
    rw [this]
    exact k.mul_mem (k.inv_mem hck) hcm
  obtain ⟨l, hl, hroot⟩ := root_mem_of_tv_single_free hk hn hγ'e h1 j
  exact eq_top_of_root_not_mem hk hn hp hK hj hl hroot

end Rational

end CFSG.LieType.SeitzGeneration
