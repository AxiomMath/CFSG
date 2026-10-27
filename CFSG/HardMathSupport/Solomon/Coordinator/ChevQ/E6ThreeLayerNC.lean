module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeHeisSL3
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP

section Center

variable {K : Type*} [Field K]

theorem conjUnit_mem_center {g : GL (Fin 3) K} {x : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) :
    conjUnit g x ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨r, hr, ?_⟩
  rw [conjUnit_coe, ← hrx]
  have hc : Matrix.scalar (Fin 3) r * (g : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) r :=
    (Matrix.scalar_commute r (fun s => Commute.all _ s) _).eq
  rw [← hc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem diagSL_notMem_center {a b d : K} (h : a * b * d = 1) (hne : a ≠ d) :
    diagSL a b d h ∉ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
  intro hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have h0 := congrFun (congrFun hr 0) 0
  have h2 := congrFun (congrFun hr 2) 2
  simp [diagSL] at h0 h2
  exact hne (h0.symm.trans h2)

end Center

section OrderThree

variable {K : Type*} [Field K]

theorem exists_notMem_center_commute_of_pow_three {ω : K} (hω : IsPrimitiveRoot ω 3)
    {γ : GL (Fin 3) K} (hγ : γ ^ 3 = 1) :
    ∃ k : SpecialLinearGroup (Fin 3) K,
      k ∉ Subgroup.center (SpecialLinearGroup (Fin 3) K) ∧
        (γ : Matrix (Fin 3) (Fin 3) K) * k = k * γ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hd : ω * ω ^ 2 * 1 = 1 := by linear_combination hω3
  have hcommE : ∀ x ∈ Subgroup.zpowers γ, ∀ y ∈ Subgroup.zpowers γ, x * y = y * x := by
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact (Commute.zpow_zpow_self γ m n).eq
  have hexpE : ∀ x ∈ Subgroup.zpowers γ, x ^ 3 = 1 := by
    rintro x ⟨m, rfl⟩
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, hγ, _root_.one_zpow]
  obtain ⟨P, hP⟩ := exists_conj_diagonal_of_exponent_prime (p := 3) ⟨ω, hω⟩ _ hcommE hexpE
  have hoff := hP γ (Subgroup.mem_zpowers γ)
  set N : Matrix (Fin 3) (Fin 3) K := ((P * γ * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hN
  have hMN : (γ : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N := by
    rw [hN, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have h01 : N 0 1 = 0 := hoff 0 1 (by decide)
  have h02 : N 0 2 = 0 := hoff 0 2 (by decide)
  have h10 : N 1 0 = 0 := hoff 1 0 (by decide)
  have h12 : N 1 2 = 0 := hoff 1 2 (by decide)
  have h20 : N 2 0 = 0 := hoff 2 0 (by decide)
  have h21 : N 2 1 = 0 := hoff 2 1 (by decide)
  have hk : ((diagSL ω (ω ^ 2) 1 hd : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) * N =
      N * (diagSL ω (ω ^ 2) 1 hd : SpecialLinearGroup (Fin 3) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagSL, Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21, mul_comm]
  refine ⟨conjUnit P⁻¹ (diagSL ω (ω ^ 2) 1 hd), fun hc => ?_,
    (commute_conjUnit_of_intertwine hMN hk).symm⟩
  have := conjUnit_mem_center (g := P) hc
  rw [conjUnit_conjUnit_inv] at this
  exact diagSL_notMem_center hd hω1 this

end OrderThree

section NonCube

variable {K : Type*} [Field K]

theorem charpoly_eq_of_pow_three_not_cube {α : K} (hα : ∀ b : K, b ^ 3 ≠ α)
    {A : Matrix (Fin 3) (Fin 3) K} (hA : A ^ 3 = α • 1) :
    A.charpoly = Polynomial.X ^ 3 - Polynomial.C α := by
  have hmon : (Polynomial.X ^ 3 - Polynomial.C α : Polynomial K).Monic :=
    Polynomial.monic_X_pow_sub_C α (by norm_num)
  have hirr : Irreducible (Polynomial.X ^ 3 - Polynomial.C α : Polynomial K) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_three hα
  have haeval : Polynomial.aeval A (Polynomial.X ^ 3 - Polynomial.C α) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hA,
      Algebra.algebraMap_eq_smul_one, sub_self]
  have hmin : Polynomial.X ^ 3 - Polynomial.C α = minpoly K A :=
    minpoly.eq_of_irreducible_of_monic hirr haeval hmon
  have hdvd : (Polynomial.X ^ 3 - Polynomial.C α : Polynomial K) ∣ A.charpoly := by
    rw [hmin]
    exact Matrix.minpoly_dvd_charpoly A
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic A) hdvd ?_
  rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_X_pow_sub_C]
  simp

theorem det_sub_smul_one_of_pow_three_not_cube {α : K} (hα : ∀ b : K, b ^ 3 ≠ α)
    {A : Matrix (Fin 3) (Fin 3) K} (hA : A ^ 3 = α • 1) (c : K) :
    (A - c • (1 : Matrix (Fin 3) (Fin 3) K)).det = α - c ^ 3 := by
  have h := Matrix.eval_charpoly A c
  rw [charpoly_eq_of_pow_three_not_cube hα hA] at h
  have h2 : A - c • (1 : Matrix (Fin 3) (Fin 3) K) = -(Matrix.scalar (Fin 3) c - A) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    abel
  rw [h2, Matrix.det_neg, ← h]
  simp
  ring

theorem exists_notMem_center_commute_of_not_cube {ω α : K} (hω : IsPrimitiveRoot ω 3)
    (hα : ∀ b : K, b ^ 3 ≠ α) {A : Matrix (Fin 3) (Fin 3) K} (hA : A ^ 3 = α • 1) :
    ∃ k : SpecialLinearGroup (Fin 3) K,
      k ∉ Subgroup.center (SpecialLinearGroup (Fin 3) K) ∧
        A * k = (k : Matrix (Fin 3) (Fin 3) K) * A := by
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hs : α - 1 ≠ 0 := sub_ne_zero.2 fun h => hα 1 (by rw [one_pow]; exact h.symm)
  set s : K := α - 1 with hsdef
  set Q : Matrix (Fin 3) (Fin 3) K := A ^ 2 + A + 1 with hQ
  have hBQ : (A - 1) * Q = s • 1 := by
    calc (A - 1) * Q = A ^ 3 - 1 := by rw [hQ]; noncomm_ring
      _ = s • 1 := by rw [hA, hsdef, sub_smul, one_smul]
  have hQB : Q * (A - 1) = s • 1 := by
    calc Q * (A - 1) = A ^ 3 - 1 := by rw [hQ]; noncomm_ring
      _ = s • 1 := by rw [hA, hsdef, sub_smul, one_smul]
  have hdB : (A - 1).det = s := by
    have := det_sub_smul_one_of_pow_three_not_cube hα hA 1
    simpa [hsdef] using this
  have hdC : (A - ω • (1 : Matrix (Fin 3) (Fin 3) K)).det = s := by
    rw [det_sub_smul_one_of_pow_three_not_cube hα hA ω, hω3]
  have hdQ : Q.det = s ^ 2 := by
    have h := congrArg Matrix.det hBQ
    rw [Matrix.det_mul, hdB, Matrix.det_smul, Matrix.det_one] at h
    simp only [Fintype.card_fin, mul_one] at h
    apply mul_left_cancel₀ hs
    linear_combination h
  set Y : Matrix (Fin 3) (Fin 3) K := s⁻¹ • ((A - ω • 1) * Q) with hY
  have hdY : Y.det = 1 := by
    rw [hY, Matrix.det_smul, Matrix.det_mul, hdC, hdQ]
    simp only [Fintype.card_fin]
    field_simp
  have hcomm : A * Y = Y * A := by
    have h1 : Commute A (A - ω • 1) :=
      (Commute.refl A).sub_right ((Commute.one_right A).smul_right ω)
    have h2 : Commute A Q :=
      (((Commute.refl A).pow_right 2).add_right (Commute.refl A)).add_right (Commute.one_right A)
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, (h1.mul_right h2).eq]
  refine ⟨⟨Y, hdY⟩, fun hc => ?_, hcomm⟩
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hYr : Y = r • (1 : Matrix (Fin 3) (Fin 3) K) := by
    have : Matrix.scalar (Fin 3) r = Y := hr
    rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have h1 : A - ω • 1 = r • (A - 1) := by
    have e : Y * (A - 1) = A - ω • 1 := by
      rw [hY, Matrix.smul_mul, Matrix.mul_assoc, hQB, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        inv_mul_cancel₀ hs, one_smul]
    rw [← e, hYr, Matrix.smul_mul, Matrix.one_mul]
  have h2 : (1 - r) • A = (ω - r) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    linear_combination (norm := module) h1
  by_cases hr1 : r = 1
  · subst hr1
    rw [sub_self, zero_smul] at h2
    have h3 := congrFun (congrFun h2 0) 0
    simp at h3
    exact hω1 (sub_eq_zero.1 h3.symm)
  · have hr1' : 1 - r ≠ 0 := sub_ne_zero.2 (Ne.symm hr1)
    have hA' : A = ((ω - r) / (1 - r)) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hr1', one_smul]
    apply hα ((ω - r) / (1 - r))
    have h3 : (((ω - r) / (1 - r)) ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K) = α • 1 := by
      rw [← hA, hA', smul_pow, one_pow]
    have h4 := congrFun (congrFun h3 0) 0
    simpa using h4

end NonCube

section Centralizer

theorem exists_notMem_center_commute {K : Type*} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {γ : GL (Fin 3) K} (hγ : ∃ α : K, (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) :
    ∃ k : SpecialLinearGroup (Fin 3) K,
      k ∉ Subgroup.center (SpecialLinearGroup (Fin 3) K) ∧
        (γ : Matrix (Fin 3) (Fin 3) K) * k = k * γ := by
  obtain ⟨α, hα⟩ := hγ
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_three h3
  by_cases hcube : ∃ μ : K, μ ^ 3 = α
  · obtain ⟨μ, hμ⟩ := hcube
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      apply ne_zero_of_pow_three_eq_smul hα
      rw [← hμ]
      norm_num
    obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = μ⁻¹ := ⟨Units.mk0 _ (inv_ne_zero hμ0), rfl⟩
    set γ' : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) u * γ with hγ'
    have hγ'c : (γ' : Matrix (Fin 3) (Fin 3) K) = μ⁻¹ • (γ : Matrix (Fin 3) (Fin 3) K) := by
      rw [hγ', coe_scalarGL_mul, hu]
    have hγ'3 : γ' ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hγ'c, smul_pow, hα, smul_smul, ← hμ, ← mul_pow,
        inv_mul_cancel₀ hμ0, one_pow, one_smul, Units.val_one]
    obtain ⟨k, hk, hkc⟩ := exists_notMem_center_commute_of_pow_three hω hγ'3
    refine ⟨k, hk, ?_⟩
    have hγc : (γ : Matrix (Fin 3) (Fin 3) K) = μ • (γ' : Matrix (Fin 3) (Fin 3) K) := by
      rw [hγ'c, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    rw [hγc, Matrix.smul_mul, Matrix.mul_smul, hkc]
  · exact exists_notMem_center_commute_of_not_cube hω (fun b hb => hcube ⟨b, hb⟩) hα

end Centralizer

section NormalClosure

theorem normal_le_center_or_eq_top_of_isPerfect {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  have := hperf
  have := hs
  let quotient := QuotientGroup.mk' (Subgroup.center Q)
  have hnormal : (N.map quotient).Normal :=
    Subgroup.Normal.map inferInstance quotient (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : N ≤ quotient.ker := N.map_eq_bot_iff.mp hbot
    change N ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker at hkernel
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq quotient N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hderived
    exact top_unique hderived

theorem normalClosure_singleton_eq_top {K : Type*} [Field K] {k : SpecialLinearGroup (Fin 3) K}
    (hk : k ∉ Subgroup.center (SpecialLinearGroup (Fin 3) K)) :
    Subgroup.normalClosure ({k} : Set (SpecialLinearGroup (Fin 3) K)) = ⊤ := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) K) :=
    (CFSG.LinearGroups.linear_projective_simple (n := 3) (K := K) (by norm_num)
      (Or.inl le_rfl)).2.1
  rcases normal_le_center_or_eq_top_of_isPerfect hperf hsimple
    (Subgroup.normalClosure ({k} : Set (SpecialLinearGroup (Fin 3) K))) with h | h
  · exact absurd (h (Subgroup.subset_normalClosure (Set.mem_singleton k))) hk
  · exact h

theorem eq_top_of_forall_commute_conj_mem {K : Type*} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) {γ : GL (Fin 3) K}
    (hγ : ∃ α : K, (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    {Q : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hQ : ∀ q x : SpecialLinearGroup (Fin 3) K,
      (γ : Matrix (Fin 3) (Fin 3) K) * q = q * γ → x * q * x⁻¹ ∈ Q) : Q = ⊤ := by
  obtain ⟨k, hk, hkγ⟩ := exists_notMem_center_commute h3 hγ
  have hle : Subgroup.normalClosure ({k} : Set (SpecialLinearGroup (Fin 3) K)) ≤ Q := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe]
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨x, rfl⟩ := isConj_iff.1 hconj
    exact hQ a x hkγ
  rw [normalClosure_singleton_eq_top hk] at hle
  exact top_le_iff.1 hle

end NormalClosure

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
