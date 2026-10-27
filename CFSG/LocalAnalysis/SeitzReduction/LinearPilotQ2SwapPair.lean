module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2SwapUniquePair
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapFactorNormalTypes
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphFour

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup)
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor exists_isPrimitivePrimeDivisor)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.OutcomeLocal (oneRestrictEquiv
  nonempty_altIsometry_mulEquiv_statedSp dotForm_restrict_isAlt dotForm_restrict_nondegenerate
  finrank_dotForm_ker)

section Arith

theorem q2_inner_inner_arith {n r v₁ v₂ : ℕ} (hn : 3 ≤ n) (hr : 2 * r ≤ n) (hr' : n ≤ 2 * r + 1)
    (h1 : n * (n - 1) ≤ 2 * v₁ + r * (r - 1)) (h2 : n * (n - 1) ≤ 2 * v₂ + r * (r - 1))
    (h3 : 2 * (v₁ + v₂) ≤ n * (n - 1) + 4) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2 h3
  nlinarith

theorem q2_inner_graph_arith {n r v₁ v₂ : ℕ} (hn : 4 ≤ n) (hr : 2 * r ≤ n) (hr' : n ≤ 2 * r + 1)
    (h1 : n * (n - 1) ≤ 2 * v₁ + r * (r - 1)) (h2 : r ^ 2 ≤ v₂)
    (h3 : 2 * (v₁ + v₂) ≤ n * (n - 1) + 4) : False := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  simp only [show s + 2 - 1 = s + 1 by omega] at h1
  nlinarith

theorem q2_graph_graph_even_arith {r v₁ v₂ : ℕ} (hr : 3 ≤ r) (h1 : r ^ 2 ≤ v₁) (h2 : r ^ 2 ≤ v₂)
    (h3 : 2 * (v₁ + v₂) ≤ 2 * r * (2 * r - 1) + 4) : False := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
  simp only [show 2 * (s + 3) - 1 = 2 * s + 5 by omega] at h3
  nlinarith

end Arith

section TwoParts

variable {n : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem not_fieldTypeCore_one {θ : MulAut (projectiveSL n K)} : ¬ FieldTypeCore n 1 K θ :=
  fun h => by
    obtain ⟨a, ha⟩ := h.1
    omega

theorem factorization_two_mul_card_mulAut_le_of_card_two (hn : 3 ≤ n) (hK : Nat.card K = 2) :
    (2 * Nat.card (MulAut (projectiveSL n K))).factorization 2 ≤ n * (n - 1) / 2 + 2 := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have h := factorization_card_mulAut_projectiveSL_le (K := K) hn le_rfl hK1
  rw [Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two]
  simp only [one_mul, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, add_zero] at h
  omega

theorem involution_types_of_card_two [CharP K 2] (hn : 4 ≤ n) (hK : Nat.card K = 2)
    {θ : MulAut (projectiveSL n K)} (hθ : θ * θ = 1) (hθ1 : θ ≠ 1) :
    (∃ y : projectiveSL n K, orderOf y = 2 ∧ θ = MulAut.conj y) ∨
      ∃ A : GL (Fin n) K, θ = conjAut n K A * dualAut n K := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  rcases involution_types hn le_rfl hK1 hθ hθ1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (not_fieldTypeCore_one h).elim

theorem le_two_mul_factorization_inner_of_card_two [CharP K 2] (hn : 1 ≤ n) (hK : Nat.card K = 2)
    {y : projectiveSL n K} (hy : orderOf y = 2) :
    n * (n - 1) ≤ 2 * (Nat.card (fixedSubgroup (MulAut.conj y))).factorization 2 +
      (n / 2) * (n / 2 - 1) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have h := le_two_mul_factorization_card_centralizer_projectiveSL le_rfl hK1 hn hy
  rw [one_mul] at h
  rw [fixedSubgroup_mulAut_conj_eq]
  have hle : (n / 2) * (n / 2 - 1) ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem le_factorization_graph_of_card_two (hn : 3 ≤ n) (hK : Nat.card K = 2) (A : GL (Fin n) K)
    (hθ : (conjAut n K A * dualAut n K) * (conjAut n K A * dualAut n K) = 1) :
    (n / 2) ^ 2 ≤ (Nat.card (fixedSubgroup (conjAut n K A * dualAut n K))).factorization 2 := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have h := le_factorization_card_fixedSubgroup_graph hn le_rfl hK1 A hθ
  rwa [one_mul] at h

end TwoParts

section Cores

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem commutator_matrixIsometryGroup_one_of_odd [CharP K 2] (hK : Nat.card K = 2) {n r : ℕ}
    (hr : n = 2 * r + 1) (hr3 : 3 ≤ r) :
    ⁅matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K),
      matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)⁆ =
      matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨e⟩ := nonempty_altIsometry_mulEquiv_statedSp _
    (dotForm_restrict_isAlt (k := K) (n := n)) (dotForm_restrict_nondegenerate hr)
    (finrank_dotForm_ker hr)
  have : Group.IsPerfect (StatedSp r K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp r K (Or.inr (Or.inr ⟨hK, hr3⟩))
  have : Group.IsPerfect (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K)) :=
    Group.IsPerfect.ofSurjective (f := ((oneRestrictEquiv hr).trans e).symm.toMonoidHom)
      ((oneRestrictEquiv hr).trans e).symm.surjective
  exact Subgroup.isPerfect_iff.mp this

theorem card_statedSp_dvd_card_perfectCore_graph (hK : Nat.card K = 2) {n r : ℕ}
    (hr : n = 2 * r + 1) (hr3 : 3 ≤ r) (A : GL (Fin n) K)
    (hθ : (conjAut n K A * dualAut n K) * (conjAut n K A * dualAut n K) = 1) :
    Nat.card (StatedSp r K) ∣
      Nat.card (perfectCore (fixedSubgroup (conjAut n K A * dualAut n K))) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK1
  obtain ⟨C, hC, -, hcore⟩ := card_fixedSubgroup_graph_eq le_rfl hK1 (by omega) A hθ
  have hC1 : (C : Matrix (Fin n) (Fin n) K) = 1 := by
    rcases hC with h | ⟨r', hr', -⟩
    · exact h
    · omega
  obtain ⟨E⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv le_rfl
    hK1 (by omega) C (Or.inl hC1)
  rw [hC1] at E
  rw [hcore, ← card_matrixIsometryGroup_one_of_odd hr]
  exact card_dvd_card_perfectCore_of_mulEquiv E le_rfl
    (commutator_matrixIsometryGroup_one_of_odd hK hr hr3)

omit [Finite K] in
theorem permMatrixHom_toHomUnits_mem_matrixIsometryGroup {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (Matrix.permMatrixHom (n := Fin m) (R := K)).toHomUnits σ ∈
      matrixIsometryGroup (1 : Matrix (Fin m) (Fin m) K) := by
  rw [mem_matrixIsometryGroup, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply,
    Matrix.mul_one, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul, inv_mul_cancel,
    Matrix.permMatrix_one]

omit [Finite K] in
theorem permMatrixHom_toHomUnits_injective {m : ℕ} :
    Function.Injective (Matrix.permMatrixHom (n := Fin m) (R := K)).toHomUnits := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have h1 : (σ⁻¹).toPEquiv.toMatrix = ((1 : Equiv.Perm (Fin m)).toPEquiv.toMatrix :
      Matrix (Fin m) (Fin m) K) := by
    have h := congrArg Units.val hσ
    rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Units.val_one] at h
    exact h.trans Matrix.permMatrix_one.symm
  have h2 := PEquiv.toMatrix_injective h1
  have h3 : σ⁻¹ = 1 := by
    refine Equiv.ext fun x => ?_
    have := congrArg (fun f => f x) h2
    simpa [Equiv.toPEquiv_apply] using this
  exact inv_eq_one.mp h3

theorem sixty_dvd_card_perfectCore_graph_five (hK : Nat.card K = 2) (A : GL (Fin 5) K)
    (hθ : (conjAut 5 K A * dualAut 5 K) * (conjAut 5 K A * dualAut 5 K) = 1) :
    60 ∣ Nat.card (perfectCore (fixedSubgroup (conjAut 5 K A * dualAut 5 K))) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK1
  obtain ⟨C, hC, -, hcore⟩ := card_fixedSubgroup_graph_eq le_rfl hK1 (by norm_num) A hθ
  have hC1 : (C : Matrix (Fin 5) (Fin 5) K) = 1 := by
    rcases hC with h | ⟨r', hr', -⟩
    · exact h
    · omega
  obtain ⟨E⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv le_rfl
    hK1 (by norm_num) C (Or.inl hC1)
  rw [hC1] at E
  set φ := (Matrix.permMatrixHom (n := Fin 5) (R := K)).toHomUnits with hφ
  set M := (alternatingGroup (Fin 5)).map φ with hM
  have hMO : M ≤ matrixIsometryGroup (1 : Matrix (Fin 5) (Fin 5) K) := by
    rintro _ ⟨σ, -, rfl⟩
    exact permMatrixHom_toHomUnits_mem_matrixIsometryGroup σ
  have hMp : ⁅M, M⁆ = M := by
    rw [hM, ← map_commutator, commutator_alternatingGroup_eq_self (by simp)]
  have hMc : Nat.card M = 60 := by
    rw [hM, card_map_of_injective permMatrixHom_toHomUnits_injective,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [hcore, ← hMc]
  exact card_dvd_card_perfectCore_of_mulEquiv E hMO hMp

end Cores

section OddPrimes

variable {K : Type} [Field K] [Finite K]

theorem prod_Icc_two_pow_two_mul_split {r : ℕ} (hr : 1 ≤ r) :
    ∏ j ∈ Finset.Icc 1 r, (2 ^ (2 * j) - 1) =
      (∏ j ∈ Finset.Icc 1 (r - 1), (2 ^ (2 * j) - 1)) * (2 ^ (2 * r) - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Finset.prod_Icc_succ_top (by omega), Nat.add_sub_cancel]

theorem prod_Icc_two_pow_split {r : ℕ} (hr : 1 ≤ r) :
    ∏ j ∈ Finset.Icc 2 (2 * r + 1), (2 ^ j - 1) =
      (∏ j ∈ Finset.Icc 2 (2 * r - 1), (2 ^ j - 1)) * (2 ^ (2 * r) - 1) *
        (2 ^ (2 * r + 1) - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Finset.prod_Icc_succ_top (by omega), show 2 * (s + 1) = 2 * s + 1 + 1 by ring,
    Finset.prod_Icc_succ_top (by omega), show 2 * s + 1 + 1 - 1 = 2 * s + 1 by omega]

theorem not_card_statedSp_mul_self_dvd_card_SL_two (hK : Nat.card K = 2) {r : ℕ} (hr : 4 ≤ r) :
    ¬ Nat.card (StatedSp r K) * Nat.card (StatedSp r K) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin (2 * r + 1)) K) := by
  intro h
  rw [SymplecticFlag.card_statedSp, card_SL_eq (by omega), hK, prod_Icc_two_pow_two_mul_split
    (by omega), prod_Icc_two_pow_split (by omega)] at h
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * r) (by omega) (by omega)
  set M := 2 ^ (2 * r) - 1 with hM
  set A := ∏ j ∈ Finset.Icc 1 (r - 1), (2 ^ (2 * j) - 1) with hA
  set B := ∏ j ∈ Finset.Icc 2 (2 * r - 1), (2 ^ j - 1) with hB
  set C := 2 ^ (2 * r + 1) - 1 with hC
  set N := (2 * r + 1) * (2 * r + 1 - 1) / 2 with hN
  have hM0 : M ≠ 0 := by
    have : 2 ≤ 2 ^ (2 * r) := Nat.le_self_pow (by omega) 2
    omega
  have h1 : M * (2 ^ r ^ 2 * A * (2 ^ r ^ 2 * A * M)) ∣ M * (2 ^ N * (B * C)) := by
    have e1 : M * (2 ^ r ^ 2 * A * (2 ^ r ^ 2 * A * M)) = 2 ^ r ^ 2 * (A * M) * (2 ^ r ^ 2 * (A * M)) := by
      ring
    have e2 : M * (2 ^ N * (B * C)) = 2 ^ N * (B * M * C) := by ring
    rw [e1, e2]
    exact h
  have h2' := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hM0)).1 h1
  have h2 : M ∣ 2 ^ N * (B * C) :=
    (Dvd.intro_left (2 ^ r ^ 2 * A * (2 ^ r ^ 2 * A)) (by ring)).trans h2'
  have hpM : p ∣ M := hp.2.1
  have hp2 : p ≠ 2 := hp.ne_two (by omega)
  rcases (Nat.Prime.dvd_mul hp.1).1 (hpM.trans h2) with h3 | h3
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).1 (hp.1.dvd_of_dvd_pow h3))
  rcases (Nat.Prime.dvd_mul hp.1).1 h3 with h4 | h4
  · rw [hB, Prime.dvd_finsetProd_iff hp.1.prime] at h4
    obtain ⟨j, hj, hpj⟩ := h4
    rw [Finset.mem_Icc] at hj
    exact hp.2.2 j (by omega) (by omega) hpj
  · have h5 := (hp.dvd_sub_one_iff (by omega) (2 * r + 1)).1 h4
    obtain ⟨c, hc⟩ := h5
    rcases Nat.lt_or_ge c 1 with hc0 | hc1
    · interval_cases c
      omega
    · have : 2 * r * c ≥ 2 * r * 1 := Nat.mul_le_mul_left _ hc1
      rcases Nat.lt_or_ge c 2 with hc2 | hc2
      · interval_cases c
        omega
      · have : 2 * r * c ≥ 2 * r * 2 := Nat.mul_le_mul_left _ hc2
        omega

theorem not_card_statedSp_mul_self_dvd_card_SL_of_three_le (hK : Nat.card K = 2) {r : ℕ}
    (hr : 3 ≤ r) :
    ¬ Nat.card (StatedSp r K) * Nat.card (StatedSp r K) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin (2 * r + 1)) K) := by
  rcases Nat.lt_or_ge r 4 with h4 | h4
  · obtain rfl : r = 3 := by omega
    rw [SymplecticFlag.card_statedSp, card_SL_eq (by norm_num), hK]
    decide
  · exact not_card_statedSp_mul_self_dvd_card_SL_two hK h4

end OddPrimes

theorem swapPairExclusion_projectiveSL_two {n : ℕ} (hn : 5 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : SeitzQ2.SwapPairExclusion (projectiveSL n K) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK1
  intro θ θ' hθ hθ1 hθ' hθ'1 h2 hcore
  have hA := factorization_two_mul_card_mulAut_le_of_card_two (K := K) (by omega : 3 ≤ n) hK
  have hN := two_mul_choose_two_eq n
  have hv : 2 * ((Nat.card (fixedSubgroup θ)).factorization 2 +
      (Nat.card (fixedSubgroup θ')).factorization 2) ≤ n * (n - 1) + 4 := by omega
  have hP : Nat.card (projectiveSL n K) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) K) :=
    Subgroup.card_quotient_dvd_card _
  rcases involution_types_of_card_two (by omega) hK hθ hθ1 with ⟨y, hy, rfl⟩ | ⟨A, rfl⟩
  · have h1 := le_two_mul_factorization_inner_of_card_two (by omega) hK hy
    rcases involution_types_of_card_two (by omega) hK hθ' hθ'1 with ⟨y', hy', rfl⟩ | ⟨A', rfl⟩
    · have h1' := le_two_mul_factorization_inner_of_card_two (by omega) hK hy'
      exact q2_inner_inner_arith (by omega) (by omega) (by omega) h1 h1' hv
    · have h2' := le_factorization_graph_of_card_two (by omega) hK A' hθ'
      exact q2_inner_graph_arith (by omega) (by omega) (by omega) h1 h2' hv
  · have h1 := le_factorization_graph_of_card_two (by omega) hK A hθ
    rcases involution_types_of_card_two (by omega) hK hθ' hθ'1 with ⟨y', hy', rfl⟩ | ⟨A', rfl⟩
    · have h1' := le_two_mul_factorization_inner_of_card_two (by omega) hK hy'
      rw [add_comm] at hv
      exact q2_inner_graph_arith (by omega) (by omega) (by omega) h1' h1 hv
    · have h1' := le_factorization_graph_of_card_two (by omega) hK A' hθ'
      obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n
      · subst hr
        rw [show 2 * r / 2 = r by omega] at h1 h1'
        exact q2_graph_graph_even_arith (by omega) h1 h1' hv
      · subst hr
        rcases Nat.lt_or_ge r 3 with hr3 | hr3
        · obtain rfl : r = 2 := by omega
          have hc := sixty_dvd_card_perfectCore_graph_five hK A hθ
          have hc' := sixty_dvd_card_perfectCore_graph_five hK A' hθ'
          have h := ((Nat.mul_dvd_mul hc hc').trans hcore).trans hP
          rw [card_SL_eq (by norm_num), hK] at h
          revert h
          decide
        · have hc := card_statedSp_dvd_card_perfectCore_graph hK rfl hr3 A hθ
          have hc' := card_statedSp_dvd_card_perfectCore_graph hK rfl hr3 A' hθ'
          exact not_card_statedSp_mul_self_dvd_card_SL_of_three_le hK hr3
            (((Nat.mul_dvd_mul hc hc').trans hcore).trans hP)

end CFSG.SeitzReduction.LinearPilot
