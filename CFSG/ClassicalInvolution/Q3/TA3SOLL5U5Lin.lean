module

public import CFSG.ClassicalInvolution.Models.Transfer.Linear
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

variable {X : Type} [Group X]

theorem exists_sq_eq_one_lift_of_pow_five {G : Type*} [Group G] (θ : G →* X)
    (hker : θ.ker ≤ Subgroup.center G) (hZ : ∀ k ∈ Subgroup.center G, k ^ 5 = 1) {a : X}
    (ha : a ∈ θ.range) (ha2 : a * a = 1) : ∃ z : G, z * z = 1 ∧ θ z = a := by
  obtain ⟨g, rfl⟩ := ha
  have hg : g * g ∈ θ.ker := by rw [MonoidHom.mem_ker, map_mul]; exact ha2
  refine ⟨g ^ 5, ?_, ?_⟩
  · rw [← (Commute.refl g).mul_pow 5]
    exact hZ _ (hker hg)
  · have h2 : θ g ^ 2 = 1 := by rw [sq]; exact ha2
    rw [map_pow, show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_succ, pow_mul, h2, one_pow, one_mul]

theorem map_le_centralizer_of_le {G : Type*} [Group G] (θ : G →* X) {L : Subgroup G} {z : G}
    (hL : L ≤ Subgroup.centralizer ({z} : Set G)) :
    L.map θ ≤ Subgroup.centralizer ({θ z} : Set X) := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hL hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx' ⊢
  rw [← map_mul, ← map_mul, hx']

variable {K : Type} [Field K]

theorem diagonal_mul_blockMat_comm_of_eq {m j : ℕ} {d : Fin m → K}
    (hd : ∀ a b : Fin m, (j ≤ a.val ∧ a.val < j + 2) → (j ≤ b.val ∧ b.val < j + 2) → d a = d b)
    (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal d * blockMat m j A = blockMat m j A * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, blockMat_apply]
  by_cases h : (j ≤ a.val ∧ a.val < j + 2) ∧ (j ≤ b.val ∧ b.val < j + 2)
  · rw [dite_eq_left h, hd a b h.1 h.2, mul_comm]
  · rw [dite_eq_right h]
    by_cases hab : a = b
    · subst hab
      simp [mul_comm]
    · simp [hab]

theorem sign_eq_of_block {a j : ℕ} (ha : a = 2 ∨ a = 4) (hj : j = 0 ∨ j = 2) (x y : Fin 5)
    (hx : j ≤ x.val ∧ x.val < j + 2) (hy : j ≤ y.val ∧ y.val < j + 2) :
    (if x.val < a then (-1 : K) else 1) = if y.val < a then (-1 : K) else 1 := by
  split_ifs <;> first | rfl | omega

theorem center_pow_five (k : SL(5, K)) (hk : k ∈ Subgroup.center SL(5, K)) : k ^ 5 = 1 := by
  obtain ⟨r, hr, hrk⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
  have hr5 : r ^ 5 = 1 := by simpa using hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrk, ← map_pow, hr5, map_one]
  rfl

theorem exists_commuting_longRoot_sl5 (h2 : (2 : K) ≠ 0) {z : SL(5, K)} (hz : z * z = 1)
    (hz1 : z ≠ 1) :
    ∃ (L₁ L₂ : Subgroup SL(5, K)) (i₁ i₂ : SL(5, K)), IsLongRootSL2 (by norm_num) L₁ i₁ ∧
      IsLongRootSL2 (by norm_num) L₂ i₂ ∧ L₁ ≤ Subgroup.centralizer ({z} : Set SL(5, K)) ∧
      L₂ ≤ Subgroup.centralizer ({z} : Set SL(5, K)) ∧ ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  have hI : (z : Matrix (Fin 5) (Fin 5) K) * z = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨a, ha, P, hP⟩ := ModelFacts.exists_sl_conj_diagonal h2 (by norm_num) hI
  set D : Matrix (Fin 5) (Fin 5) K :=
    Matrix.diagonal (fun j : Fin 5 => if j.val < a then (-1 : K) else 1) with hD
  have hdetD : D.det = 1 := by
    have := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul, z.2, P.2, one_mul, one_mul] at this
    exact this.symm
  let δ : SL(5, K) := ⟨D, hdetD⟩
  have hzδ : z = P * δ * P⁻¹ := by
    have h1 : z * P = P * δ := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact hP)
    rw [← h1]
    group
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hprod : ∏ j : Fin 5, (if j.val < a then (-1 : K) else 1) = 1 := by
    rw [← Matrix.det_diagonal]
    exact hdetD
  have ha24 : a = 2 ∨ a = 4 := by
    rw [Fin.prod_univ_five] at hprod
    interval_cases a
    · exfalso
      apply hz1
      have hδ : δ = 1 := Subtype.ext (by simp [δ, hD])
      rw [hzδ, hδ, mul_one, mul_inv_cancel]
    · norm_num at hprod
      exact (hne hprod).elim
    · exact Or.inl rfl
    · norm_num at hprod
      exact (hne hprod).elim
    · exact Or.inr rfl
    · norm_num at hprod
      exact (hne hprod).elim
  have hcent : ∀ (j : ℕ) (hj : j + 2 ≤ 5), (j = 0 ∨ j = 2) →
      (blockSL K 5 2 j hj).range.map (MulAut.conj P).toMonoidHom ≤
        Subgroup.centralizer ({z} : Set SL(5, K)) := by
    rintro j hj hj' _ ⟨_, ⟨A, rfl⟩, rfl⟩
    have hA : blockSL K 5 2 j hj A * δ = δ * blockSL K 5 2 j hj A := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL]
      exact (diagonal_mul_blockMat_comm_of_eq (sign_eq_of_block ha24 hj') _).symm)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hzδ]
    calc P * blockSL K 5 2 j hj A * P⁻¹ * (P * δ * P⁻¹)
        = P * (blockSL K 5 2 j hj A * δ) * P⁻¹ := by group
      _ = P * (δ * blockSL K 5 2 j hj A) * P⁻¹ := by rw [hA]
      _ = P * δ * P⁻¹ * (P * blockSL K 5 2 j hj A * P⁻¹) := by group
  refine ⟨_, _, _, _, (isLongRootSL2_range_blockSL h2 (by norm_num : 0 + 2 ≤ 5)).conj P,
    (isLongRootSL2_range_blockSL h2 (by norm_num : 2 + 2 ≤ 5)).conj P,
    hcent 0 _ (Or.inl rfl), hcent 2 _ (Or.inr rfl), ?_⟩
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hAB := blockSL_comm (K := K) (by norm_num : 0 + 2 ≤ 5) (by norm_num : 2 + 2 ≤ 5)
    (Or.inl le_rfl) A B
  calc P * blockSL K 5 2 0 _ A * P⁻¹ * (P * blockSL K 5 2 2 _ B * P⁻¹)
      = P * (blockSL K 5 2 0 _ A * blockSL K 5 2 2 _ B) * P⁻¹ := by group
    _ = P * (blockSL K 5 2 2 _ B * blockSL K 5 2 0 _ A) * P⁻¹ := by rw [hAB]
    _ = P * blockSL K 5 2 2 _ B * P⁻¹ * (P * blockSL K 5 2 0 _ A * P⁻¹) := by group

theorem exists_sl2_pair_of_psl5 [Finite K] (hodd : Odd (Nat.card K))
    (e : X ≃* StatedProj (StatedSL 5 K)) {t : X} (ht : orderOf t = 2) :
    ∃ H₁ H₂ : Subgroup X, H₁ ≤ Subgroup.centralizer ({t} : Set X) ∧
      H₂ ≤ Subgroup.centralizer ({t} : Set X) ∧ (∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) ∧
      Nonempty (H₁ ≃* SL(2, K)) ∧ Nonempty (H₂ ≃* SL(2, K)) := by
  let θ : SL(5, K) →* X := e.symm.toMonoidHom.comp
    ((projectiveSpecialLinearGroupEquivStatedProj 5 K).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center SL(5, K))))
  have hsurj : Function.Surjective θ :=
    e.symm.surjective.comp ((projectiveSpecialLinearGroupEquivStatedProj 5 K).surjective.comp
      (QuotientGroup.mk'_surjective _))
  have hker : θ.ker ≤ Subgroup.center SL(5, K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simpa [θ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] using hx
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨z, hz, rfl⟩ := exists_sq_eq_one_lift_of_pow_five θ hker center_pow_five
    (MonoidHom.mem_range.mpr (hsurj t)) ht2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨L₁, L₂, i₁, i₂, hL₁, hL₂, hC₁, hC₂, hcomm⟩ :=
    exists_commuting_longRoot_sl5 (two_ne_zero_of_odd_natCard hodd) hz hz1
  refine ⟨L₁.map θ, L₂.map θ, map_le_centralizer_of_le θ hC₁, map_le_centralizer_of_le θ hC₂,
    ?_, IsLongRootImage.nonempty_mulEquiv hodd (by norm_num) hker ⟨L₁, i₁, hL₁, rfl, rfl⟩,
    IsLongRootImage.nonempty_mulEquiv hodd (by norm_num) hker ⟨L₂, i₂, hL₂, rfl, rfl⟩⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, hcomm x hx y hy]

end CFSG.ClassicalInvolution.Q3.TA3
