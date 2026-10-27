module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.TorusInv
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NumTheory
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKlein
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_proj_inverted (σ : K ≃+* K) (hσσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ 1) (j k n : ℕ)
    (hσ : ∀ x, σ x = x ^ 2 ^ j) (hK : Nat.card K = 2 ^ (2 * j)) (hk : Odd k) (hkn : k ≤ n)
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ (2 ^ j) ^ k + 1) (hpq : ¬ p ∣ Nat.card K - 1) :
    ∃ y : projectiveSL n K, orderOf y = p ∧ fieldAut n K σ y = y⁻¹ := by
  obtain ⟨M, M', hMσ, hMM', hMp, hdet, hns⟩ := exists_inverted_matrix σ hσσ hσ1 j k n hσ hK hk hkn hp hpd hpq
  let g : Matrix.SpecialLinearGroup (Fin n) K := ⟨M, hdet⟩
  have hdet' : M'.det = 1 := by
    have := congrArg Matrix.det hMM'
    rwa [Matrix.det_mul, hdet, one_mul, Matrix.det_one] at this
  let g' : Matrix.SpecialLinearGroup (Fin n) K := ⟨M', hdet'⟩
  have hgg' : g * g' = 1 := Subtype.ext hMM'
  have hginv : g' = g⁻¹ := (inv_eq_of_mul_eq_one_right hgg').symm
  have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom g = g⁻¹ := by
    rw [← hginv]
    exact Subtype.ext hMσ
  refine ⟨proj n K g, ?_, ?_⟩
  · have h1 : proj n K g ^ p = 1 := by
      rw [← map_pow]
      have : g ^ p = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]; exact hMp)
      rw [this, map_one]
    have : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime h1 ?_
    intro h
    rw [proj_eq_one_iff, mem_scalars] at h
    obtain ⟨c, -, hc⟩ := h
    exact hns c hc
  · rw [fieldAut_proj, hmap, map_inv]


omit [CharP K 2] in
theorem bigInv_conj_field {n : ℕ} (H : GL (Fin n) K) (σ : K ≃+* K) (y : projectiveSL n K) {p : ℕ}
    (hp : p.Prime) (h11 : 11 ≤ p ∨ p = 7) (hy : orderOf y = p) (hinv : fieldAut n K σ y = y⁻¹) :
    BigInv (conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹) := by
  refine ⟨conjAut n K H y, p, hp, h11, ?_⟩
  have h1 : (conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹) (conjAut n K H y) =
      (conjAut n K H y)⁻¹ := by
    simp only [MulAut.mul_apply]
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply, hinv, map_inv]
  rw [h1, ← mul_inv_rev, ← pow_two]
  have hx : orderOf (conjAut n K H y) = p := by
    rw [← hy]
    exact (MulEquiv.orderOf_eq (conjAut n K H) y)
  have hg : Nat.gcd p 2 = 1 :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      rcases h11 with h | h <;> omega)
  rw [orderOf_inv, orderOf_pow, hx, hg, Nat.div_one]


theorem not_two_dvd_card_sub_one (n : ℕ) : ¬ 2 ∣ Nat.gcd n (Nat.card K - 1) := by
  intro h
  have h2 : 2 ∣ Nat.card K - 1 := h.trans (Nat.gcd_dvd_right _ _)
  have := Fintype.ofFinite K
  obtain ⟨f, hp, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [← Nat.card_eq_fintype_card] at hf; exact hf
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have h2K : 2 ∣ Nat.card K := by rw [hK]; exact dvd_pow_self 2 (by omega)
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  omega

theorem kleinBigInv_projectiveSL {n : ℕ} (hn : 3 ≤ n) (hexc : ¬ (Nat.card K = 4 ∧ n ≤ 4)) :
    KleinBigInv (projectiveSL n K) := by
  intro B hcomm hsq hcard hinn
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have : Finite (MulAut (projectiveSL n K)) := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.finite_mulAut_projectiveSL n
  obtain ⟨α, ⟨hαB, hαE⟩, hα1⟩ := exists_mem_inf_of_index_le_two B _ hidx' (by omega)
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hαE
  have hα2 : (conjAut n K A * fieldAut n K σ) ^ 2 = 1 := by rw [pow_two]; exact hsq _ hαB
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    subst hσ1
    rw [map_one, mul_one] at hαB hα1 hα2
    have hDinn : conjAut n K A ∈ CFSG.RankThree.PartOne.OutStructure.Inn (projectiveSL n K) :=
      CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two hn
        (not_two_dvd_card_sub_one n) _ (conjAut_mem_linearAutGroup A) 1
        (by rw [pow_one, hα2]; exact Subgroup.one_mem _)
    have : conjAut n K A ∈ B ⊓ CFSG.RankThree.PartOne.OutStructure.Inn (projectiveSL n K) :=
      ⟨hαB, hDinn⟩
    rw [hinn] at this
    exact hα1 (by simpa using this)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [← Nat.card_eq_fintype_card] at hf; exact hf
  obtain ⟨hfe, hσpow, H, hH⟩ := even_linear_field_involution_descent f.pos hK hn A σ hσ1 hα2
  obtain ⟨j, hj⟩ := hfe
  have hj2 : (f : ℕ) / 2 = j := by omega
  rw [hj2] at hσpow
  have hK' : Nat.card K = 2 ^ (2 * j) := by rw [hK, hj]; ring_nf
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    rw [hσpow, hσpow, ← pow_mul, ← pow_add, ← two_mul, ← hK', Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hj1 : 1 ≤ j := by have := f.pos; omega
  refine ⟨conjAut n K A * fieldAut n K σ, hαB, ?_⟩
  rw [hH]
  rcases Nat.lt_or_ge j 2 with hj3 | hj3
  · have hj1' : j = 1 := by omega
    subst hj1'
    have hn5 : 5 ≤ n := by
      by_contra h
      exact hexc ⟨by rw [hK']; norm_num, by omega⟩
    obtain ⟨hp, h11, hpd, hpq⟩ := good_prime_two
    obtain ⟨y, hy, hyσ⟩ := exists_proj_inverted σ hσσ hσ1 1 5 n hσpow hK' (by decide) hn5 hp hpd
      (by rw [hK']; exact hpq)
    exact bigInv_conj_field H σ y hp (Or.inl h11) hy hyσ
  · obtain ⟨p, hp, h11, hpd, hpq⟩ := exists_good_prime_three j hj3
    obtain ⟨y, hy, hyσ⟩ := exists_proj_inverted σ hσσ hσ1 j 3 n hσpow hK' (by decide) hn hp hpd
      (by rw [hK']; exact hpq)
    exact bigInv_conj_field H σ y hp (Or.inl h11) hy hyσ


open CFSG.Assembly.LowTwoRank in
theorem kleinBigInv_PSL_ge_three {X : Type} [Group X] {n m : ℕ} (hn : 3 ≤ n)
    (hexc : ¬ (m = 2 ∧ n ≤ 4)) (h : StatedClassicalModel X .PSL n 2 m) : KleinBigInv X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have e' : X ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  refine KleinBigInv.of_mulEquiv e'.symm (kleinBigInv_projectiveSL hn ?_)
  rintro ⟨h4, hn4⟩
  apply hexc
  refine ⟨?_, hn4⟩
  rw [hK] at h4
  exact Nat.pow_right_injective (le_refl 2) (by simpa using h4)

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
