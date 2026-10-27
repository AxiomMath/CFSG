module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLNonsplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.PSL
open scoped MatrixGroups

variable {K : Type} [Field K]

section Quad

variable {l : K} {m : ℕ}

theorem compInd_commute_blockRep_scalar' (k : Fin m) (x : QuadExt l) :
    compInd K {finProdFinEquiv (k, 0), finProdFinEquiv (k, 1)} *
        blockRep l m (Matrix.scalar (Fin m) x) =
      blockRep l m (Matrix.scalar (Fin m) x) *
        compInd K {finProdFinEquiv (k, 0), finProdFinEquiv (k, 1)} := by
  rw [commute_compInd_iff]
  intro u v huv
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective v
  have hmem : ∀ k' c, finProdFinEquiv (k', c) ∈ ({finProdFinEquiv (k, 0),
      finProdFinEquiv (k, 1)} : Finset (Fin (m * 2))) ↔ k' = k := by
    intro k' c
    simp only [Finset.mem_insert, Finset.mem_singleton, EmbeddingLike.apply_eq_iff_eq,
      Prod.mk.injEq]
    fin_cases c <;> simp
  rw [hmem, hmem] at huv
  have hij : i ≠ j := by
    rintro rfl
    tauto
  rw [blockRep_scalar_apply]
  simp [hij]

theorem blockRep_scalar_eq_smul_of_block (k : Fin m) {x : QuadExt l}
    (h1 : blockRep l m (Matrix.scalar (Fin m) x) (finProdFinEquiv (k, 0))
      (finProdFinEquiv (k, 0)) =
      blockRep l m (Matrix.scalar (Fin m) x) (finProdFinEquiv (k, 1)) (finProdFinEquiv (k, 1)))
    (h3 : blockRep l m (Matrix.scalar (Fin m) x) (finProdFinEquiv (k, 1))
      (finProdFinEquiv (k, 0)) = 0) :
    ∃ α : K, blockRep l m (Matrix.scalar (Fin m) x) = α • 1 := by
  simp only [blockRep_scalar_apply, ↓reduceIte] at h1 h3
  have hcx : quadRep l x * compMat l = compMat l * quadRep l x := by
    rw [← quadRep_root, ← map_mul, ← map_mul, mul_comm]
  have e01 := congrFun (congrFun hcx 0) 0
  simp [compMat, Matrix.mul_apply, Fin.sum_univ_two] at e01
  set α := quadRep l x 0 0 with hα
  have hρ : quadRep l x = α • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e01, h3, hα, ← h1]
  refine ⟨α, ?_⟩
  ext u v
  obtain ⟨⟨i, a'⟩, rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j, b'⟩, rfl⟩ := finProdFinEquiv.surjective v
  rw [blockRep_scalar_apply, hρ]
  by_cases hij : i = j
  · subst hij
    by_cases hab' : a' = b'
    · subst hab'
      simp
    · simp [hab']
  · simp [hij]

end Quad

variable [Finite K]

theorem nonsplit_oddCoreIn_eq_bot_three {l : K} (hl : ¬ IsSquare l) {m : ℕ} (hm : 2 ≤ m)
    (h3 : Nat.card K = 3)
    (hinj : Function.Injective (MulAut.conj : projectiveSL (m * 2) K →*
      MulAut (projectiveSL (m * 2) K)))
    {B : Subgroup (MulAut (projectiveSL (m * 2) K))}
    (hB : (MulAut.conj : projectiveSL (m * 2) K →* MulAut (projectiveSL (m * 2) K)).range ≤ B) :
    oddCoreIn B (conjAut (m * 2) K (quadGL l m hl)) = ⊥ := by
  have : Fact (Irreducible (quadPoly l)) := ⟨quadPoly_irreducible hl⟩
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  obtain ⟨D, x, rfl, hD⟩ := nonsplit_oddCoreIn hl hm hinj hB hy
  have : Module.Finite K (QuadExt l) := (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C l
    two_ne_zero)).finite
  have : Finite (QuadExt l) := Module.finite_of_finite K
  have : Fintype (QuadExt l) := Fintype.ofFinite _
  have : Fintype K := Fintype.ofFinite K
  have hcardE : Fintype.card (QuadExt l) = 9 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := QuadExt l),
      (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C l two_ne_zero)).finrank,
      ← Nat.card_eq_fintype_card, h3]
    change 3 ^ (quadPoly l).natDegree = 9
    rw [Polynomial.natDegree_X_pow_sub_C]
    norm_num
  have hx : x ≠ 0 := by
    rintro rfl
    have hdet := D.isUnit.map Matrix.detMonoidHom
    rw [Matrix.coe_detMonoidHom, hD, scalar_apply] at hdet
    simp only [diagonal_zero, map_zero] at hdet
    have : Nonempty (Fin (m * 2)) := ⟨⟨0, by omega⟩⟩
    rw [det_zero] at hdet
    exact not_isUnit_zero hdet
  have hx8 : x ^ 8 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [hcardE] at this
  have hx4 : x ^ 4 = 1 ∨ x ^ 4 = -1 := by
    have : (x ^ 4 - 1) * (x ^ 4 + 1) = 0 := by linear_combination hx8
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hD4 : ∃ c : Kˣ, D ^ 4 = GeneralLinearGroup.scalar (Fin (m * 2)) c := by
    rcases hx4 with h | h
    · refine ⟨1, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val, hD, ← map_pow, ← map_pow, h, map_one, map_one]
      simp [GeneralLinearGroup.scalar]
    · refine ⟨-1, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val, hD, ← map_pow, ← map_pow, h, map_neg, map_one, map_neg,
        map_one]
      simp [GeneralLinearGroup.scalar]
  obtain ⟨c, hc⟩ := hD4
  have h1 : conjAut (m * 2) K D ^ 4 = 1 := by rw [← map_pow, hc, conjAut_scalar]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  have : orderOf (conjAut (m * 2) K D) = 1 := by
    have h4' : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4'] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hk] at hodd ⊢
    rcases k with _ | k
    · rfl
    · exact absurd hodd (by rw [pow_succ]; simp)
  exact orderOf_eq_one_iff.1 this

theorem split_oddCoreIn_eq_bot_three {n : ℕ} (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (h3 : Nat.card K = 3)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J) :
    oddCoreIn B (conjAut n K (signGL K J)) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  obtain ⟨α, β, rfl⟩ := split_oddCoreIn hK hn hinj hB ha hb hy
  have hsq : ∀ γ : Kˣ, γ * γ = 1 := by
    intro γ
    have h := FiniteField.pow_card_sub_one_eq_one (γ : K) γ.ne_zero
    rw [← Nat.card_eq_fintype_card, h3] at h
    exact Units.ext (by rw [Units.val_mul, Units.val_one, ← pow_two]; exact h)
  have h2 : conjAut n K (blockScalarGL J α β) ^ 2 = 1 := by
    rw [← map_pow]
    have : blockScalarGL J α β ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, coe_blockScalarGL, Units.val_one, pow_two,
        diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      split_ifs
      · exact congrArg Units.val (hsq α)
      · exact congrArg Units.val (hsq β)
    rw [this, map_one]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  have : orderOf (conjAut n K (blockScalarGL J α β)) = 1 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf (conjAut n K (blockScalarGL J α β)) ∣ 2 ^ 1 by rw [pow_one]; exact hdvd)
    rw [hk] at hodd ⊢
    rcases k with _ | k
    · rfl
    · exact absurd hodd (by rw [pow_succ]; simp)
  exact orderOf_eq_one_iff.1 this

end CFSG.ComponentClassification.Burgoyne.B
