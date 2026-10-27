module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222UnitaryTwoLin
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222TwoB

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

section Entries

variable {K : Type} [Field K] {ℓ r : ℕ}

theorem entry_smul_one_add_sum_w_x (d : K) (c : Fin ℓ → K) (j : Fin ℓ) :
    (d • (1 : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K) +
      ∑ i, c i • Matrix.single (Sum.inr (Sum.inl i) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
        (Sum.inl i : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K)) (Sum.inr (Sum.inl j)) (Sum.inl j) =
      c j := by
  simp [Matrix.sum_apply, Matrix.single_apply]

theorem entry_smul_one_add_sum_x_x (d : K) (c : Fin ℓ → K) (j : Fin ℓ) :
    (d • (1 : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K) +
      ∑ i, c i • Matrix.single (Sum.inr (Sum.inl i) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
        (Sum.inl i : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K)) (Sum.inl j) (Sum.inl j) = d := by
  simp [Matrix.sum_apply]

end Entries

section Unitary

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem eq_of_pairOrbit_unitary_two {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {e : rankTwoQuot A ≃* StatedProj (StatedSU n (2 ^ 1) K)}
    (hZ : Odd (Nat.card (center ↥A))) {p : G} (hp2 : orderOf p = 2) {M : GL (Fin n) K}
    (hpM : Represents e p M) (hM2 : orderOf M = 2) {v : G}
    (hv : v ∈ A ⊓ centralizer ({p} : Set G)) (hv2 : v ^ 2 = 1)
    (horb : ∀ a ∈ A ⊓ centralizer ({p} : Set G), a * v * a⁻¹ = v ∨ a * v * a⁻¹ = v * p) :
    (SandwichScalar ((M : Matrix (Fin n) (Fin n) K) - 1) → v = 1 ∨ v = p) ∧
      (v = 1 ∨ v = p ∨ ∃ V : GL (Fin n) K, Represents e v V ∧ orderOf V = 2 ∧
        SandwichScalar ((V : Matrix (Fin n) (Fin n) K) - 1)) := by
  have hU : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_refl 1, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := hU.charP
  have hp2' : p ^ 2 = 1 := by rw [← hp2]; exact pow_orderOf_eq_one p
  have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
  set σ := hU.bar with hσdef
  have hσ : ∀ x, σ (σ x) = x := hU.bar_bar
  have hσq : ∀ x, σ x = x ^ 2 ^ 1 := hU.bar_apply
  have hMu := adjM_mul_self_of_mem_statedSU hσ hσq hpM.2.1
  have hMM : (M : Matrix (Fin n) (Fin n) K) * M = 1 := by
    rw [← Units.val_mul, ← sq, ← hM2, pow_orderOf_eq_one, Units.val_one]
  have hMadj : adjM σ (M : Matrix (Fin n) (Fin n) K) = M := by
    calc adjM σ (M : Matrix (Fin n) (Fin n) K) =
        adjM σ (M : Matrix (Fin n) (Fin n) K) * (M * M) := by rw [hMM, mul_one]
      _ = M := by rw [← mul_assoc, hMu, one_mul]
  have hNh : adjM σ ((M : Matrix (Fin n) (Fin n) K) - 1) =
      (M : Matrix (Fin n) (Fin n) K) - 1 := by
    rw [adjM_sub, hMadj, adjM_one]
  have hN := sub_one_mul_self_eq_zero hM2
  have hM1 : M ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hM2
    omega
  have hN0 := sub_one_ne_zero hM1
  obtain ⟨ω, hω3, hω1⟩ := exists_norm_one_ne_one hK
  have hσω : σ ω = ω * ω := by rw [hσq]; ring
  have hω : ω * ω + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hω1)
  obtain ⟨ℓ, r, φ, hℓ0, hn', hφN, hdet, hunit⟩ := exists_unitary_adapted hU hN hNh hN0
  have hφM : φ (M : Matrix (Fin n) (Fin n) K) = 1 + sqZeroStd ℓ r := by
    rw [show (M : Matrix (Fin n) (Fin n) K) = 1 + ((M : Matrix (Fin n) (Fin n) K) - 1) from
      (add_sub_cancel 1 _).symm, map_add, map_one, hφN]
  obtain ⟨U, hUr⟩ := exists_represents e (mem_inf.mp hv).1
  have hup : v * p = p * v := mem_centralizer_singleton_iff.mp (mem_inf.mp hv).2
  have hUM := hUr.mul_comm_of_commute hpM hMsq hup
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : K, (U : Matrix (Fin n) (Fin n) K) * U = c₀ • 1 := by
    have h1 : Represents e (v * v) (U * U) := hUr.mul hUr
    rw [← sq, hv2] at h1
    obtain ⟨c, hc⟩ := represents_one.exists_scalar h1
    refine ⟨c, ?_⟩
    have h := congrArg (fun Y : GL (Fin n) K => (Y : Matrix (Fin n) (Fin n) K)) hc
    simp only [Units.val_mul, one_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [h, Matrix.smul_one_eq_diagonal]
    rfl
  have hBS : Commute (φ (U : Matrix (Fin n) (Fin n) K)) (sqZeroStd ℓ r) := by
    have h2 := congrArg φ hUM
    rw [map_mul, map_mul, hφM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h2
    exact add_left_cancel h2
  have hlift : ∀ R : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
      adjM σ R * unitGram K ℓ r * R = unitGram K ℓ r → R.det = 1 →
      Commute R (sqZeroStd ℓ r) →
      ∃ Rv : GL (Fin n) K, Rv ∈ StatedSU n (2 ^ 1) K ∧ Rv * M = M * Rv ∧
        φ (Rv : Matrix (Fin n) (Fin n) K) = R := by
    intro R hRJ hRdet hRS
    have hdet' : (φ.symm R).det ≠ 0 := by rw [hdet, hRdet]; exact one_ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet',
      mem_statedSU_of hσq (by rw [show ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet' :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = φ.symm R from rfl, hdet, hRdet])
        (hunit R hRJ), Units.ext (φ.injective ?_), AlgEquiv.apply_symm_apply φ R⟩
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul,
      show ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet' : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = φ.symm R from rfl, AlgEquiv.apply_symm_apply, hφM,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hRS.eq]
  have hodd : ∀ R : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
      adjM σ R * unitGram K ℓ r * R = unitGram K ℓ r → R.det = 1 →
      Commute R (sqZeroStd ℓ r) → R * R * R = 1 →
      Commute (φ (U : Matrix (Fin n) (Fin n) K)) R := by
    intro R hRJ hRd hRS hR3
    obtain ⟨Rv, hH, hRM, hφR⟩ := hlift R hRJ hRd hRS
    have hRv3 : (Rv : Matrix (Fin n) (Fin n) K) * Rv * Rv = 1 := by
      apply φ.injective
      rw [map_mul, map_mul, hφR, hR3, map_one]
    have h1 := commute_sq_of_pairOrbit hZ hp2' hpM horb hUr hc₀ (mul_mem hH hH)
      (show Rv * Rv * M = M * (Rv * Rv) by rw [mul_assoc, hRM, ← mul_assoc, hRM, mul_assoc])
    have h4 : (((Rv * Rv) * (Rv * Rv) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Rv := by
      simp only [Units.val_mul]
      calc (Rv : Matrix (Fin n) (Fin n) K) * Rv * (Rv * Rv) = (Rv * Rv * Rv) * Rv := by
            simp only [mul_assoc]
        _ = Rv := by rw [hRv3, one_mul]
    rw [h4] at h1
    have h' := congrArg φ h1
    rw [map_mul, map_mul, hφR] at h'
    exact h'.symm
  have hcard : 4 ≤ 2 * ℓ + r := by omega
  obtain ⟨lam, β, hV, hβ⟩ := commutant_odd_unitary hσ hω hσω hcard hℓ0 hodd hBS
  set E' : Fin ℓ → Matrix (Fin n) (Fin n) K :=
    fun i => φ.symm (Matrix.single (.inr (.inl i)) (.inl i) 1) with hE'
  have hsing : ∀ i j : Fin ℓ, Matrix.single (Sum.inr (Sum.inl i) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
      (Sum.inl i : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K) *
        Matrix.single (Sum.inr (Sum.inl j) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
          (Sum.inl j : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) 1 = 0 := fun i j =>
    Matrix.single_mul_single_of_ne (1 : K) _ _ _ (by simp) 1
  have hEE : ∀ i j, E' i * E' j = 0 := fun i j => by
    show φ.symm _ * φ.symm _ = 0
    rw [← map_mul, hsing, map_zero]
  have hT : ∀ i, ∃ Rv : GL (Fin n) K, Rv ∈ StatedSU n (2 ^ 1) K ∧
      (Rv : Matrix (Fin n) (Fin n) K) = 1 + E' i := by
    intro i
    have hEJ : adjM σ (Matrix.single (Sum.inr (Sum.inl i) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
        (Sum.inl i : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K)) * unitGram K ℓ r =
        unitGram K ℓ r * Matrix.single (Sum.inr (Sum.inl i)) (Sum.inl i) 1 := by
      have h := adjM_tv2_mul_unitGram hσ (Pi.single (Sum.inr (Sum.inl i) :
        Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K)) (Pi.single (Sum.inr (Sum.inl i)) 1)
      rwa [tv2_single] at h
    have hxx : (1 + Matrix.single (Sum.inr (Sum.inl i) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
        (Sum.inl i : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K)) *
        (1 + Matrix.single (Sum.inr (Sum.inl i)) (Sum.inl i) 1) = 1 := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hsing, add_zero, add_assoc, matrix_add_self, add_zero]
    have hES : Commute (Matrix.single (Sum.inr (Sum.inl i) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
        (Sum.inl i : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K)) (sqZeroStd ℓ r) := by
      show _ * _ = _ * _
      rw [sqZeroStd_eq_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_zero
        (fun j _ => hsing i j), Finset.sum_eq_zero (fun j _ => hsing j i)]
    obtain ⟨Rv, hH, -, hφR⟩ := hlift _
      (by
        have h := adjM_one_add_smul_mul_unitGram hEJ (hsing i i) (map_one σ)
        rwa [one_smul] at h)
      (by
        apply eq_one_of_sq_eq_one_of_charTwo
        rw [sq, ← Matrix.det_mul, hxx, Matrix.det_one])
      ((Commute.one_left _).add_left hES)
    refine ⟨Rv, hH, ?_⟩
    rw [← AlgEquiv.symm_apply_apply φ (Rv : Matrix (Fin n) (Fin n) K), hφR, map_add, map_one]
  have hEh : ∀ i, adjM σ (E' i) = E' i := by
    intro i
    obtain ⟨Rv, hH, hRv⟩ := hT i
    have h1 := adjM_mul_self_of_mem_statedSU hσ hσq hH
    rw [hRv] at h1
    have h2 : (1 + E' i) * (1 + E' i) = 1 := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hEE, add_zero, add_assoc, matrix_add_self, add_zero]
    have h3 : adjM σ (1 + E' i) = 1 + E' i := by
      calc adjM σ (1 + E' i) = adjM σ (1 + E' i) * ((1 + E' i) * (1 + E' i)) := by
            rw [h2, Matrix.mul_one]
        _ = 1 + E' i := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [adjM_add, adjM_one] at h3
    exact add_left_cancel h3
  have hUe : (U : Matrix (Fin n) (Fin n) K) = lam • 1 + ∑ i, β i • E' i := by
    apply φ.injective
    rw [hV, map_add, map_smul, map_one, map_sum]
    simp only [map_smul, hE', AlgEquiv.apply_symm_apply]
  have hNe : (M : Matrix (Fin n) (Fin n) K) - 1 = ∑ i, E' i := by
    apply φ.injective
    rw [hφN, map_sum]
    simp only [hE', AlgEquiv.apply_symm_apply]
    exact sqZeroStd_eq_sum
  have hUu := adjM_mul_self_of_mem_statedSU hσ hσq hUr.2.1
  rw [hUe, adjM_add, adjM_smul, adjM_one, adjM_sum] at hUu
  simp only [adjM_smul, hEh] at hUu
  have hprod : (∑ i, σ (β i) • E' i) * (∑ i, β i • E' i) = 0 := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hEE, smul_zero, smul_zero]
  have hexp : (σ lam • (1 : Matrix (Fin n) (Fin n) K) + ∑ i, σ (β i) • E' i) *
      (lam • 1 + ∑ i, β i • E' i) =
      (σ lam * lam) • 1 + ∑ i, (σ lam * β i + lam * σ (β i)) • E' i := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hprod, add_zero]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
      Finset.mul_sum, Finset.sum_mul, add_smul, Finset.sum_add_distrib]
    rw [add_assoc]
    congr 2
    · ring
    · exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp] at hUu
  have hφu := congrArg φ hUu
  rw [map_add, map_smul, map_one, map_sum] at hφu
  simp only [map_smul, hE', AlgEquiv.apply_symm_apply] at hφu
  have hℓpos : 0 < ℓ := Nat.pos_of_ne_zero hℓ0
  have hlam : σ lam * lam = 1 := by
    have h := congrFun (congrFun hφu (.inl ⟨0, hℓpos⟩)) (.inl ⟨0, hℓpos⟩)
    rwa [entry_smul_one_add_sum_x_x, Matrix.one_apply_eq] at h
  have hc : ∀ i, σ lam * β i + lam * σ (β i) = 0 := fun i => by
    have h := congrFun (congrFun hφu (.inr (.inl i))) (.inl i)
    rwa [entry_smul_one_add_sum_w_x, Matrix.one_apply_ne (by simp)] at h
  have hlam0 : lam ≠ 0 := fun h => by
    rw [h, mul_zero] at hlam
    exact zero_ne_one hlam
  have hb : ∀ i, β i = 0 ∨ β i = lam := by
    intro i
    have h := hc i
    rw [hσq, hσq] at h
    have h' : lam * β i * (lam + β i) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact Or.inl ((mul_eq_zero.mp h1).resolve_left hlam0)
    · exact Or.inr (by linear_combination h1 - lam * CharTwo.two_eq_zero (R := K))
  have hscal : ∀ Y : GL (Fin n) K, Y ∈ StatedSU n (2 ^ 1) K →
      (U : Matrix (Fin n) (Fin n) K) = lam • (Y : Matrix (Fin n) (Fin n) K) →
      Represents e v Y := by
    intro Y hY h
    refine hUr.of_eq_mul_scalar hY (c := Units.mk0 lam hlam0) (Units.ext ?_)
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, h, Units.val_mk0, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hv1 : (U : Matrix (Fin n) (Fin n) K) = lam • 1 → v = 1 := fun h =>
    eq_of_represents hZ (hscal 1 (one_mem _) (by rw [h, Units.val_one])) represents_one
      (k := 1) (k' := 1) (by rw [pow_one]; exact hv2) (by simp)
  have hvp : (U : Matrix (Fin n) (Fin n) K) = lam • (M : Matrix (Fin n) (Fin n) K) → v = p :=
    fun h => eq_of_represents hZ (hscal M hpM.2.1 h) hpM (k := 1) (k' := 1)
      (by rw [pow_one]; exact hv2) (by rw [pow_one]; exact hp2')
  have hconst : (∀ i j, β i = β j) → v = 1 ∨ v = p := by
    intro hβc
    rcases hb ⟨0, hℓpos⟩ with h0 | h0
    · refine Or.inl (hv1 ?_)
      rw [hUe, Finset.sum_eq_zero (fun i _ => by rw [hβc i ⟨0, hℓpos⟩, h0, zero_smul]),
        add_zero]
    · refine Or.inr (hvp ?_)
      rw [hUe, show (M : Matrix (Fin n) (Fin n) K) = 1 + ∑ i, E' i by rw [← hNe, add_sub_cancel],
        smul_add, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [hβc i ⟨0, hℓpos⟩, h0]
  refine ⟨fun hS => hconst (hβ ?_), ?_⟩
  ·
    have h1 := hS.map φ
    rw [hφN] at h1
    have := le_one_of_sandwichScalar h1
    omega
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have htv : ∀ i : Fin 2, (U : Matrix (Fin n) (Fin n) K) = lam • (1 + E' i) →
        ∃ V : GL (Fin n) K, Represents e v V ∧ orderOf V = 2 ∧
          SandwichScalar ((V : Matrix (Fin n) (Fin n) K) - 1) := by
      intro i h
      obtain ⟨Rv, hH, hRv⟩ := hT i
      refine ⟨Rv, hscal Rv hH (by rw [hRv]; exact h), orderOf_eq_prime ?_ ?_, ?_⟩
      · refine Units.ext ?_
        rw [Units.val_pow_eq_pow_val, hRv, sq, Units.val_one, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hEE, add_zero,
          add_assoc, matrix_add_self, add_zero]
      · intro h1
        have h2 := congrArg (fun Y : GL (Fin n) K => (Y : Matrix (Fin n) (Fin n) K)) h1
        simp only [hRv, Units.val_one, add_eq_left] at h2
        have h3 := congrArg φ h2
        simp only [hE', AlgEquiv.apply_symm_apply, map_zero] at h3
        have h4 := congrFun (congrFun h3 (.inr (.inl i))) (.inl i)
        simp at h4
      · rw [hRv, add_sub_cancel_left, hE']
        exact (sandwichScalar_single _ _).map φ.symm
    rcases hb 0 with h0 | h0 <;> rcases hb 1 with h1 | h1
    · rcases hconst (fun i j => by fin_cases i <;> fin_cases j <;> simp [h0, h1]) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (htv 1 ?_))
      rw [hUe, Fin.sum_univ_two, h0, h1, zero_smul, zero_add, smul_add]
    · refine Or.inr (Or.inr (htv 0 ?_))
      rw [hUe, Fin.sum_univ_two, h0, h1, zero_smul, add_zero, smul_add]
    · rcases hconst (fun i j => by fin_cases i <;> fin_cases j <;> simp [h0, h1]) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · rcases hconst (hβ hℓ2) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem unitaryCaseIITwo : UnitaryCaseIITwo := by
  intro G _ _ A D hD _ hZ hq t u hconf
  have ht2 : orderOf t = 2 := orderOf_eq_prime hconf.t_sq hconf.t_ne_one
  have hu2 : orderOf u = 2 := orderOf_eq_prime hconf.u_sq hconf.u_ne_one
  have htu : u * t = t * u := hconf.comm.symm
  obtain ⟨ℓt, hℓt⟩ := D.exists_hasRank hZ hconf.mem_t ht2
  have horbt : ∀ b ∈ A ⊓ centralizer ({t} : Set G), b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * t := by
    intro b hb
    obtain ⟨hbA, hbt⟩ := mem_inf.mp hb
    have hbt' : b * t = t * b := mem_centralizer_singleton_iff.mp hbt
    have hmem := hconf.invariant t (by simp) b hbA hbt' u (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1 | h1 | h1
    · exfalso
      apply hconf.u_ne
      calc u = b⁻¹ * (b * u * b⁻¹) * b := by group
        _ = b⁻¹ * t * b := by rw [h1]
        _ = t := by rw [mul_assoc, ← hbt', inv_mul_cancel_left]
    · exact Or.inl h1
    · exact Or.inr (h1.trans htu.symm)
  have horbu : ∀ b ∈ A ⊓ centralizer ({u} : Set G), b * t * b⁻¹ = t ∨ b * t * b⁻¹ = t * u := by
    intro b hb
    obtain ⟨hbA, hbu⟩ := mem_inf.mp hb
    have hbu' : b * u = u * b := mem_centralizer_singleton_iff.mp hbu
    have hmem := hconf.invariant u (by simp) b hbA hbu' t (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1 | h1 | h1
    · exact Or.inl h1
    · exfalso
      have h2 : b * u * b⁻¹ = u := by rw [hbu', mul_assoc, mul_inv_cancel, mul_one]
      have h3 : b * t * b⁻¹ = b * u * b⁻¹ := by rw [h1, h2]
      exact hconf.u_ne (mul_left_cancel (mul_right_cancel h3)).symm
    · exact Or.inr h1
  have huC : u ∈ A ⊓ centralizer ({t} : Set G) :=
    mem_inf.mpr ⟨hconf.mem_u, mem_centralizer_singleton_iff.mpr htu⟩
  have htC : t ∈ A ⊓ centralizer ({u} : Set G) :=
    mem_inf.mpr ⟨hconf.mem_t, mem_centralizer_singleton_iff.mpr hconf.comm⟩
  cases D with
  | unitary n m hn hm K hK e =>
    have hm1 : m = 1 := by
      have h2 : 2 ^ m = 2 ^ 1 := hq
      exact Nat.pow_right_injective (le_refl 2) h2
    subst hm1
    obtain ⟨-, T, hT, hT2, -⟩ := hℓt
    obtain ⟨-, h2⟩ := eq_of_pairOrbit_unitary_two hn hK hZ ht2 hT hT2 huC hconf.u_sq horbt
    rcases h2 with h | h | ⟨V, hV, hV2, hVs⟩
    · exact hconf.u_ne_one h
    · exact hconf.u_ne h
    · obtain ⟨h1, -⟩ := eq_of_pairOrbit_unitary_two hn hK hZ hu2 hV hV2 htC hconf.t_sq horbu
      rcases h1 hVs with h | h
      · exact hconf.t_ne_one h
      · exact hconf.u_ne h.symm
  | linear => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end Unitary

end CFSG.ComponentClassification.RankTwoClassical
