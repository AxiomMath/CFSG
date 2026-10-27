module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIYComponent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityUnitary
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.ComponentClassification.RankTwoHypIILinear

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
  FourGroupEvenCanonical
open CFSG.ComponentClassification.OutcomeLocal (blockSwapIsometryEquivStatedSp oneRestrictEquiv
  nonempty_altIsometry_mulEquiv_statedSp dotForm_restrict_isAlt dotForm_restrict_nondegenerate
  finrank_dotForm_ker)
open CFSG.ComponentClassification.SymmetricLocal
  (small_standard_source_even_simple_symplectic_parameters_stated)

variable {K : Type} [Field K] {n : ℕ}

section Transposition

variable (K) in
@[expose] def transpMat (i j : Fin n) : Matrix (Fin n) (Fin n) K :=
  (Equiv.swap i j).permMatrix K

theorem transpMat_mul_self (i j : Fin n) : transpMat K i j * transpMat K i j = 1 := by
  rw [transpMat, ← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]

theorem transpMat_transpose (i j : Fin n) : (transpMat K i j)ᵀ = transpMat K i j := by
  rw [transpMat, Matrix.transpose_permMatrix, Equiv.swap_inv]

theorem transpMat_map (i j : Fin n) (φ : K →+* K) : (transpMat K i j).map φ = transpMat K i j := by
  ext a b
  simp only [transpMat, Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem transpMat_apply_self_left (i j : Fin n) : transpMat K i j i j = 1 := by
  simp [transpMat, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.swap_apply_left]

theorem det_transpMat [CharP K 2] {i j : Fin n} (hij : i ≠ j) : (transpMat K i j).det = 1 := by
  rw [transpMat, Matrix.det_permutation, Equiv.Perm.sign_swap hij]
  simp [CharTwo.neg_eq]

variable (K) in
@[expose] def transpGL (i j : Fin n) : GL (Fin n) K :=
  ⟨transpMat K i j, transpMat K i j, transpMat_mul_self i j, transpMat_mul_self i j⟩

theorem coe_transpGL (i j : Fin n) :
    (transpGL K i j : Matrix (Fin n) (Fin n) K) = transpMat K i j := rfl

theorem transpGL_mul_self (i j : Fin n) : transpGL K i j * transpGL K i j = 1 :=
  Units.ext (transpMat_mul_self i j)

theorem conjAut_transpGL_ne_one [Finite K] (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    conjAut n K (transpGL K i j) ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn _).mp h
  have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j) hc
  simp only [coe_transpGL, transpMat_apply_self_left, GeneralLinearGroup.coe_scalar] at this
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at this
  exact one_ne_zero this.symm

theorem conjAut_transpGL_sq (i j : Fin n) : conjAut n K (transpGL K i j) ^ 2 = 1 := by
  rw [sq, ← map_mul, transpGL_mul_self, map_one]

end Transposition

theorem isSimpleGroup_projectiveSL (k : Type*) [Field k] (hn : 3 ≤ n) :
    IsSimpleGroup (projectiveSL n k) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := k) (n := n) (by omega)
    (Or.inl hn)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).symm.isSimpleGroup

theorem center_projectiveSL_eq_bot (k : Type*) [Field k] (hn : 3 ≤ n) :
    center (projectiveSL n k) = ⊥ := by
  have := isSimpleGroup_projectiveSL k hn
  have hperf : Group.IsPerfect (projectiveSL n k) := by
    have := CFSG.LinearGroups.linear_projective_perfect (K := k) (n := n) (by omega) (Or.inl hn)
    exact Group.IsPerfect.ofSurjective
      (f := (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).toMonoidHom)
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (projectiveSL n k)) with h | h
  · exact h
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top (projectiveSL n k)).2 h
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_ne_bot h1

theorem rigidInvolution_fieldAut [Finite K] [CharP K 2] (hn : 3 ≤ n) (σ : K ≃+* K)
    (hX : fieldAut n K σ ∉
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (h2 : fieldAut n K σ ^ 2 = 1) :
    RigidInvolution (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
      (fieldAut n K σ) := by
  obtain ⟨-, ⟨e, -⟩, hinn, -, hcent, hnorm, hC⟩ :=
    linear_quadratic_field_full_centralizer_rigidity (n := n) σ hn
  have := isSimpleGroup_projectiveSL (n := n) (fixedField K σ) hn
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine RigidInvolution.of_isSimpleGroup_of_le_zpowers hX h2 hinn hcent
    ((normal_subgroupOf_iff_le_normalizer hcent).mp hnorm) e.symm.isSimpleGroup ?_ ?_
  · refine even_card_of_mem ?_ (conjAut_transpGL_ne_one hn h01) (conjAut_transpGL_sq _ _)
    rw [range_subfieldConj]
    refine ⟨transpGL K _ _, ⟨?_, ?_⟩, rfl⟩
    · exact Units.ext (by
        rw [GeneralLinearGroup.val_det_apply, coe_transpGL, det_transpMat h01]; rfl)
    · exact Units.ext (transpMat_map _ _ _)
  · rw [hC]
    exact inf_le_right

theorem rigidInvolution_graphField {e : ℕ} (h : UnitaryFieldData 2 e K) (hn : 4 ≤ n)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (hX : fieldAut n K σ * dualAut n K ∉
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (h2 : (fieldAut n K σ * dualAut n K) ^ 2 = 1) :
    RigidInvolution (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
      (fieldAut n K σ * dualAut n K) := by
  have := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ι, -⟩, hinn, -, hcent, hnorm, hC⟩ :=
    linear_graph_field_full_centralizer_rigidity h (n := n) (by omega) σ hσ
  have hq : (n, 2 ^ e) ≠ (3, 2) := by
    intro hq
    have := congrArg Prod.fst hq
    simp at this
    omega
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 e
    (by rw [h.card, ← pow_mul, mul_comm]) n (by omega) hq
  have hsimple := (ι.symm.trans
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega))).isSimpleGroup
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine RigidInvolution.of_isSimpleGroup_of_le_zpowers hX h2 hinn hcent
    ((normal_subgroupOf_iff_le_normalizer hcent).mp hnorm) hsimple ?_ ?_
  · refine even_card_of_mem (mem_map_of_mem _ ?_) (conjAut_transpGL_ne_one (by omega) h01)
      (conjAut_transpGL_sq _ _)
    rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h, coe_transpGL, det_transpMat h01,
      transpMat_map, transpMat_transpose, transpMat_mul_self]
    exact ⟨rfl, rfl⟩
  · rw [hC]
    exact inf_le_right

theorem even_card_statedSp [Finite K] {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hr : 1 ≤ r) : Even (Nat.card (StatedSp r K)) := by
  rw [SymplecticFlag.card_statedSp, hK]
  refine (even_iff_two_dvd.mpr ?_).mul_right _
  rw [← pow_mul]
  exact dvd_pow_self 2 (by positivity)

theorem rigidInvolution_symplecticGraph {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (C : GL (Fin n) K) {r : ℕ} (hr : 2 ≤ r) (hsmall : ¬ (r = 2 ∧ f = 1))
    (hCr : (n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) ∨
      ((C : Matrix (Fin n) (Fin n) K) = 1 ∧ n = 2 * r + 1))
    (hX : conjAut n K C * dualAut n K ∉
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range) :
    RigidInvolution (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
      (conjAut n K C * dualAut n K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hC : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r := by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Or.inr ⟨r, h1, h2⟩
    · exact Or.inl h1
  obtain ⟨hinj, hNinn, hβ2, -, hNC, hNnormal, hcan⟩ :=
    even_linear_canonical_graph_symplectic_centralizers hf hK hn C hC
  have hcent := (hcan (by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨r, h1, h2⟩
    · exact Or.inr ⟨h1, ⟨r, h2⟩⟩)).1
  have eN : (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) ≃*
      matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) :=
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])).trans
      (MonoidHom.ofInjective hinj).symm
  obtain ⟨eSp⟩ : Nonempty (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ≃* StatedSp r K) := by
    rcases hCr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨(MulEquiv.subgroupCongr (congrArg matrixIsometryGroup h2)).trans
        (blockSwapIsometryEquivStatedSp (by omega))⟩
    · have hC1 : (C : Matrix (Fin n) (Fin n) K) =
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1, Units.val_one]
      obtain ⟨e₂⟩ := nonempty_altIsometry_mulEquiv_statedSp _
        (dotForm_restrict_isAlt (k := K) (n := n)) (dotForm_restrict_nondegenerate h2)
        (finrank_dotForm_ker h2)
      exact ⟨((MulEquiv.subgroupCongr (congrArg matrixIsometryGroup hC1)).trans
        (oneRestrictEquiv h2)).trans e₂⟩
  have hcond : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
      (Nat.card K = 2 ∧ 3 ≤ r) := by
    by_cases hf1 : f = 1
    · right
      right
      refine ⟨by rw [hK, hf1]; norm_num, ?_⟩
      by_contra hr3
      exact hsmall ⟨by omega, hf1⟩
    · left
      right
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r (by omega) hcond
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ := small_standard_source_even_simple_symplectic_parameters_stated
    (X := StatedSp r K) hK (by omega) ⟨MulEquiv.refl _⟩
  have hsimple : IsSimpleGroup ((matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map
      (conjAut n K)) := ((eN.trans eSp).trans eProj.symm).isSimpleGroup
  have heven : Even (Nat.card ((matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map
      (conjAut n K))) := by
    rw [Nat.card_congr (eN.trans eSp).toEquiv]
    exact even_card_statedSp hf hK (by omega)
  exact RigidInvolution.of_isSimpleGroup_of_le_zpowers hX hβ2 hNinn hNC
    ((normal_subgroupOf_iff_le_normalizer hNC).mp hNnormal) hsimple heven hcent.le

theorem rigid_or_dualAut [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (hn : 4 ≤ n)
    (h4 : ¬ (n = 4 ∧ m = 1))
    (h5 : n = 5 → m = 1 → RigidInvolution
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range (dualAut n K))
    {t : MulAut (projectiveSL n K)}
    (htX : t ∉ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (ht2 : t ^ 2 = 1) :
    RigidInvolution (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range t ∨
      (Even n ∧ (∃ A : GL (Fin n) K, t = conjAut n K A * dualAut n K) ∧
        ∃ w : MulAut (projectiveSL n K), t = w * dualAut n K * w⁻¹) := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  set X := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range with hXdef
  have hXn : X.Normal := (autModel_mulAut (center_projectiveSL_eq_bot K (by omega))).normal
  have hconj : ∀ {t' w t₀ : MulAut (projectiveSL n K)}, t' ∉ X → t' ^ 2 = 1 →
      t' = w * t₀ * w⁻¹ → t₀ ∉ X ∧ t₀ ^ 2 = 1 := by
    intro t' w t₀ h1 h2 h
    subst h
    refine ⟨fun h0 => h1 (hXn.conj_mem t₀ h0 w), ?_⟩
    rwa [conj_pow, conj_eq_one_iff] at h2
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := n) (by omega)).2 t
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    left
    rw [pow_zero, mul_one] at htX ht2 ⊢
    by_cases hσ : σ = 1
    ·
      exfalso
      subst hσ
      rw [map_one, mul_one] at htX ht2
      by_cases h1 : conjAut n K A = 1
      · exact htX (h1 ▸ X.one_mem)
      · obtain ⟨s, -, hs⟩ := OutcomeLocal.exists_involution_eq_conjAut (by omega) A ht2 h1
        exact htX ⟨s, hs.symm⟩
    ·
      obtain ⟨-, -, H, hH⟩ :=
        even_linear_field_involution_descent (n := n) hm hK (by omega) A σ hσ ht2
      obtain ⟨h0X, h02⟩ := hconj htX ht2 hH
      rw [hH]
      exact (rigidInvolution_fieldAut (by omega) σ h0X h02).conj hXn _
  ·
    rw [pow_one] at htX ht2 ⊢
    by_cases hσ : σ = 1
    ·
      subst hσ
      rw [map_one, mul_one] at htX ht2 ⊢
      obtain ⟨-, ⟨H, C, -, hH, hC⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms (n := n) hm hK (by omega)
          A ht2
      obtain ⟨h0X, -⟩ := hconj htX ht2 hH
      rcases hC with ⟨hC1, -⟩ | ⟨r, hr, hCJ⟩
      · rcases Nat.even_or_odd n with hev | hodd
        ·
          right
          have hC : C = 1 := Units.ext hC1
          subst hC
          rw [map_one, one_mul] at hH
          exact ⟨hev, ⟨A, rfl⟩, ⟨conjAut n K H, hH⟩⟩
        ·
          left
          obtain ⟨r, hr⟩ := hodd
          rw [hH]
          by_cases h52 : r = 2 ∧ m = 1
          · have hC : C = 1 := Units.ext hC1
            subst hC
            rw [map_one, one_mul]
            exact (h5 (by omega) h52.2).conj hXn _
          · exact (rigidInvolution_symplecticGraph hm hK (by omega) C (r := r) (by omega)
              h52 (Or.inr ⟨hC1, hr⟩) h0X).conj hXn _
      ·
        left
        rw [hH]
        exact (rigidInvolution_symplecticGraph hm hK (by omega) C (r := r) (by omega)
          (fun h => h4 ⟨by omega, h.2⟩) (Or.inl ⟨hr, hCJ.1⟩) h0X).conj hXn _
    ·
      left
      obtain ⟨⟨e, he⟩, hσx, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hm hK (by omega)
          A σ hσ ht2
      have hud : UnitaryFieldData 2 e K := ⟨Nat.prime_two, by omega, by rw [hK, he, two_mul]⟩
      have hσbar : ∀ x, σ x = hud.bar x := fun x => by
        rw [hσx, UnitaryFieldData.bar_apply, show m / 2 = e by omega]
      obtain ⟨h0X, h02⟩ := hconj htX ht2 hH
      rw [hH]
      exact (rigidInvolution_graphField hud (by omega) σ hσbar h0X h02).conj hXn _

end CFSG.ComponentClassification.RankTwoHypIILinear
