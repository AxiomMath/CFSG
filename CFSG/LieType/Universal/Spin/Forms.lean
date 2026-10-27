module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LieType.Universal.Spin

open QuadraticMap CFSG.Assembly.LowTwoRank

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem nondegenerate_polarBilin_of_forall {Q : QuadraticForm K V}
    (h : ∀ v, (∀ w, polar Q v w = 0) → v = 0) : (polarBilin Q).Nondegenerate :=
  ⟨fun v hv => h v fun w => by simpa using hv w,
    fun w hw => h w fun v => by rw [polar_comm]; simpa using hw v⟩

theorem nondegenerate_of_nondegenerate_polarBilin {Q : QuadraticForm K V}
    (h : (polarBilin Q).Nondegenerate) : Q.Nondegenerate := by
  have hker : LinearMap.ker (polarBilin Q) = ⊥ :=
    LinearMap.separatingLeft_iff_ker_eq_bot.mp h.1
  refine ⟨eq_bot_iff.mpr ((radical_le_ker_polarBilin (Q := Q)).trans hker.le), ?_⟩
  rw [hker, rank_bot]
  exact zero_le_one

end General

variable (n : ℕ) (K : Type*) [Field K]

noncomputable def bilinOdd : LinearMap.BilinForm K (Fin n ⊕ Fin n ⊕ Unit → K) :=
  LinearMap.mk₂ K
    (fun v w => ∑ i, v (.inl i) * w (.inr (.inl i)) + v (.inr (.inr ())) * w (.inr (.inr ())))
    (fun v₁ v₂ w => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring)
    (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, mul_add])
    (fun v w₁ w₂ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring)
    (fun c v w => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_left_comm c])

noncomputable def quadOdd : QuadraticForm K (Fin n ⊕ Fin n ⊕ Unit → K) :=
  (bilinOdd n K).toQuadraticMap

theorem quadOdd_apply (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    quadOdd n K v = ∑ i, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr ())) ^ 2 := by
  simp [quadOdd, bilinOdd, _root_.sq]

theorem polar_quadOdd (v w : Fin n ⊕ Fin n ⊕ Unit → K) :
    polar (quadOdd n K) v w =
      ∑ i, (v (.inl i) * w (.inr (.inl i)) + w (.inl i) * v (.inr (.inl i))) +
        2 * (v (.inr (.inr ())) * w (.inr (.inr ()))) := by
  rw [quadOdd, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [bilinOdd, LinearMap.mk₂_apply, Finset.sum_add_distrib]
  ring

noncomputable def bilinPlus : LinearMap.BilinForm K (Fin n ⊕ Fin n → K) :=
  LinearMap.mk₂ K (fun v w => ∑ i, v (.inl i) * w (.inr i))
    (fun v₁ v₂ w => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (fun v w₁ w₂ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm c])

noncomputable def quadPlus : QuadraticForm K (Fin n ⊕ Fin n → K) :=
  (bilinPlus n K).toQuadraticMap

theorem quadPlus_apply (v : Fin n ⊕ Fin n → K) :
    quadPlus n K v = ∑ i, v (.inl i) * v (.inr i) := by
  simp [quadPlus, bilinPlus]

theorem polar_quadPlus (v w : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) v w = ∑ i, (v (.inl i) * w (.inr i) + w (.inl i) * v (.inr i)) := by
  rw [quadPlus, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [bilinPlus, LinearMap.mk₂_apply, Finset.sum_add_distrib]

noncomputable def bilinMinus (b c : K) :
    LinearMap.BilinForm K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :=
  LinearMap.mk₂ K
    (fun v w => ∑ i, v (.inl i) * w (.inr (.inl i)) + v (.inr (.inr 0)) * w (.inr (.inr 0)) +
      b * v (.inr (.inr 0)) * w (.inr (.inr 1)) + c * v (.inr (.inr 1)) * w (.inr (.inr 1)))
    (fun v₁ v₂ w => by simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]; ring)
    (fun c' v w => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, mul_add]; ring)
    (fun v w₁ w₂ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring)
    (fun c' v w => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_left_comm c'])

noncomputable def quadMinus (b c : K) : QuadraticForm K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :=
  (bilinMinus n K b c).toQuadraticMap

theorem quadMinus_apply (b c : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    quadMinus n K b c v = ∑ i, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr 0)) ^ 2 +
      b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 := by
  simp only [quadMinus, bilinMinus, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.mk₂_apply]
  ring

theorem polar_quadMinus (b c : K) (v w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    polar (quadMinus n K b c) v w =
      ∑ i, (v (.inl i) * w (.inr (.inl i)) + w (.inl i) * v (.inr (.inl i))) +
        2 * (v (.inr (.inr 0)) * w (.inr (.inr 0))) +
        b * (v (.inr (.inr 0)) * w (.inr (.inr 1)) + w (.inr (.inr 0)) * v (.inr (.inr 1))) +
        2 * c * (v (.inr (.inr 1)) * w (.inr (.inr 1))) := by
  rw [quadMinus, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [bilinMinus, LinearMap.mk₂_apply, Finset.sum_add_distrib]
  ring

section Stated

variable (K : Type) [Field K]

theorem coe_quadOdd : ⇑(quadOdd n K) = StatedQuadOdd n K :=
  funext fun v => quadOdd_apply n K v

theorem coe_quadPlus : ⇑(quadPlus n K) = StatedQuadPlus n K :=
  funext fun v => quadPlus_apply n K v

theorem coe_quadMinus (b c : K) : ⇑(quadMinus n K b c) = StatedQuadMinus n K b c :=
  funext fun v => quadMinus_apply n K b c v

end Stated

theorem polar_quadPlus_single_inl (v : Fin n ⊕ Fin n → K) (j : Fin n) :
    polar (quadPlus n K) v (Pi.single (.inl j) 1) = v (.inr j) := by
  rw [polar_quadPlus]
  simp [Pi.single_apply]

theorem polar_quadPlus_single_inr (v : Fin n ⊕ Fin n → K) (j : Fin n) :
    polar (quadPlus n K) v (Pi.single (.inr j) 1) = v (.inl j) := by
  rw [polar_quadPlus]
  simp [Pi.single_apply]

theorem polar_quadOdd_single_inl (v : Fin n ⊕ Fin n ⊕ Unit → K) (j : Fin n) :
    polar (quadOdd n K) v (Pi.single (.inl j) 1) = v (.inr (.inl j)) := by
  rw [polar_quadOdd]
  simp [Pi.single_apply]

theorem polar_quadOdd_single_inr_inl (v : Fin n ⊕ Fin n ⊕ Unit → K) (j : Fin n) :
    polar (quadOdd n K) v (Pi.single (.inr (.inl j)) 1) = v (.inl j) := by
  rw [polar_quadOdd]
  simp [Pi.single_apply]

theorem polar_quadOdd_single_inr_inr (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    polar (quadOdd n K) v (Pi.single (.inr (.inr ())) 1) = 2 * v (.inr (.inr ())) := by
  rw [polar_quadOdd]
  simp

theorem polar_quadMinus_single_inl (b c : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (j : Fin (n - 1)) :
    polar (quadMinus n K b c) v (Pi.single (.inl j) 1) = v (.inr (.inl j)) := by
  rw [polar_quadMinus]
  simp [Pi.single_apply]

theorem polar_quadMinus_single_inr_inl (b c : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
    (j : Fin (n - 1)) :
    polar (quadMinus n K b c) v (Pi.single (.inr (.inl j)) 1) = v (.inl j) := by
  rw [polar_quadMinus]
  simp [Pi.single_apply]

theorem polar_quadMinus_single_inr_inr_zero (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    polar (quadMinus n K b c) v (Pi.single (.inr (.inr 0)) 1) =
      2 * v (.inr (.inr 0)) + b * v (.inr (.inr 1)) := by
  rw [polar_quadMinus]
  simp

theorem polar_quadMinus_single_inr_inr_one (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    polar (quadMinus n K b c) v (Pi.single (.inr (.inr 1)) 1) =
      b * v (.inr (.inr 0)) + 2 * c * v (.inr (.inr 1)) := by
  rw [polar_quadMinus]
  simp

theorem nondegenerate_polarBilin_quadPlus : (polarBilin (quadPlus n K)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  ext x
  rcases x with j | j
  · rw [Pi.zero_apply, ← polar_quadPlus_single_inr n K v j]; exact hv _
  · rw [Pi.zero_apply, ← polar_quadPlus_single_inl n K v j]; exact hv _

theorem nondegenerate_quadPlus : (quadPlus n K).Nondegenerate :=
  nondegenerate_of_nondegenerate_polarBilin (nondegenerate_polarBilin_quadPlus n K)

theorem eq_smul_single_of_forall_polar_quadOdd {v : Fin n ⊕ Fin n ⊕ Unit → K}
    (hv : ∀ w, polar (quadOdd n K) v w = 0) :
    v = v (.inr (.inr ())) • Pi.single (.inr (.inr ())) 1 := by
  ext x
  rcases x with j | j | ⟨⟩
  · rw [← polar_quadOdd_single_inr_inl n K v j, hv]; simp
  · rw [← polar_quadOdd_single_inl n K v j, hv]; simp
  · simp

theorem nondegenerate_polarBilin_quadOdd (h2 : (2 : K) ≠ 0) :
    (polarBilin (quadOdd n K)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  have hz : v (.inr (.inr ())) = 0 := by
    have := hv (Pi.single (.inr (.inr ())) 1)
    rw [polar_quadOdd_single_inr_inr] at this
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [eq_smul_single_of_forall_polar_quadOdd n K hv, hz, zero_smul]

theorem nondegenerate_quadOdd : (quadOdd n K).Nondegenerate := by
  have hker : LinearMap.ker (polarBilin (quadOdd n K)) ≤
      K ∙ (Pi.single (.inr (.inr ())) 1 : Fin n ⊕ Fin n ⊕ Unit → K) := by
    intro v hv
    have hv' : ∀ w, polar (quadOdd n K) v w = 0 := fun w => by
      simpa using LinearMap.congr_fun (LinearMap.mem_ker.mp hv) w
    rw [eq_smul_single_of_forall_polar_quadOdd n K hv']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine ⟨eq_bot_iff.mpr fun v hv => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hv
    have hv' : ∀ w, polar (quadOdd n K) v w = 0 := fun w => by
      simpa using LinearMap.congr_fun h2 w
    have hz : v (.inr (.inr ())) = 0 := by
      have h := h1
      rw [eq_smul_single_of_forall_polar_quadOdd n K hv', QuadraticMap.map_smul,
        quadOdd_apply] at h
      simpa [Pi.single_apply] using h
    rw [Submodule.mem_bot, eq_smul_single_of_forall_polar_quadOdd n K hv', hz, zero_smul]
  · refine (Submodule.rank_mono hker).trans ((rank_span_le _).trans ?_)
    simp

theorem nondegenerate_polarBilin_quadMinus {b c : K} (hbc : b ^ 2 - 4 * c ≠ 0) :
    (polarBilin (quadMinus n K b c)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  have e0 := hv (Pi.single (.inr (.inr 0)) 1)
  have e1 := hv (Pi.single (.inr (.inr 1)) 1)
  rw [polar_quadMinus_single_inr_inr_zero] at e0
  rw [polar_quadMinus_single_inr_inr_one] at e1
  have hu : v (.inr (.inr 0)) = 0 := by
    have : (b ^ 2 - 4 * c) * v (.inr (.inr 0)) = 0 := by linear_combination b * e1 - 2 * c * e0
    exact (mul_eq_zero.mp this).resolve_left hbc
  have hw : v (.inr (.inr 1)) = 0 := by
    have : (b ^ 2 - 4 * c) * v (.inr (.inr 1)) = 0 := by linear_combination b * e0 - 2 * e1
    exact (mul_eq_zero.mp this).resolve_left hbc
  ext x
  rcases x with j | j | i
  · rw [Pi.zero_apply, ← polar_quadMinus_single_inr_inl n K b c v j]; exact hv _
  · rw [Pi.zero_apply, ← polar_quadMinus_single_inl n K b c v j]; exact hv _
  · fin_cases i
    · exact hu
    · exact hw

theorem nondegenerate_polarBilin_quadMinus_iff {b c : K} :
    (polarBilin (quadMinus n K b c)).Nondegenerate ↔ b ^ 2 - 4 * c ≠ 0 := by
  refine ⟨fun h hbc => ?_, nondegenerate_polarBilin_quadMinus n K⟩
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
      v ≠ 0 ∧ ∀ w, polar (quadMinus n K b c) v w = 0 := by
    by_cases h2 : b = 0 ∧ (2 : K) = 0
    · refine ⟨Pi.single (.inr (.inr 0)) 1, fun h0 => ?_, fun w => ?_⟩
      · simpa using congrFun h0 (.inr (.inr 0))
      · rw [polar_comm, polar_quadMinus_single_inr_inr_zero, h2.1, h2.2, zero_mul, zero_mul,
          add_zero]
    · refine ⟨Pi.single (.inr (.inr 0)) b - Pi.single (.inr (.inr 1)) 2, fun h0 => h2 ?_,
        fun w => ?_⟩
      · have e0 := congrFun h0 (.inr (.inr 0))
        have e1 := congrFun h0 (.inr (.inr 1))
        simp only [Pi.sub_apply, Pi.single_apply, Pi.zero_apply] at e0 e1
        simp only [Sum.inr.injEq, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, ite_true] at e0 e1
        norm_num at e0 e1
        exact ⟨e0, e1⟩
      · rw [polar_quadMinus]
        simp only [Pi.sub_apply, Pi.single_apply, Sum.inr.injEq, reduceCtorEq, ite_false,
          sub_zero, zero_mul, mul_zero, add_zero, Finset.sum_const_zero, zero_add]
        simp only [Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, ite_true]
        norm_num
        linear_combination w (.inr (.inr 1)) * hbc
  exact hv0 (h.1 v fun w => by simpa using hv w)

theorem nondegenerate_quadMinus {b c : K} (hbc : b ^ 2 - 4 * c ≠ 0) :
    (quadMinus n K b c).Nondegenerate :=
  nondegenerate_of_nondegenerate_polarBilin (nondegenerate_polarBilin_quadMinus n K hbc)

variable {K}

theorem discr_ne_zero_of_two_ne_zero (h2 : (2 : K) ≠ 0) {b c : K}
    (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ^ 2 - 4 * c ≠ 0 := by
  intro hbc
  have ht : 2 * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  apply h (-b * 2⁻¹)
  have key : 4 * ((-b * 2⁻¹) ^ 2 + b * (-b * 2⁻¹) + c) = 0 := by
    linear_combination (b ^ 2 * (2 * (2 : K)⁻¹ - 1)) * ht - hbc
  exact (mul_eq_zero.mp key).resolve_left h4

theorem discr_ne_zero_of_finite [Finite K] {b c : K} (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    b ^ 2 - 4 * c ≠ 0 := by
  by_cases h2 : (2 : K) = 0
  · have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    have h4 : (4 : K) = 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num, h2, zero_mul]
    intro hbc
    rw [h4, zero_mul, sub_zero, pow_eq_zero_iff two_ne_zero] at hbc
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' c
    apply h r
    rw [hbc, zero_mul, add_zero, hr, _root_.sq, ← two_mul, h2, zero_mul]
  · exact discr_ne_zero_of_two_ne_zero h2 h

variable (K)

theorem nondegenerate_polarBilin_quadMinus_of_finite [Finite K] {b c : K}
    (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : (polarBilin (quadMinus n K b c)).Nondegenerate :=
  nondegenerate_polarBilin_quadMinus n K (discr_ne_zero_of_finite h)

theorem nondegenerate_quadMinus_of_finite [Finite K] {b c : K}
    (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : (quadMinus n K b c).Nondegenerate :=
  nondegenerate_quadMinus n K (discr_ne_zero_of_finite h)

theorem nondegenerate_polarBilin_quadMinus_of_two_ne_zero (h2 : (2 : K) ≠ 0) {b c : K}
    (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : (polarBilin (quadMinus n K b c)).Nondegenerate :=
  nondegenerate_polarBilin_quadMinus n K (discr_ne_zero_of_two_ne_zero h2 h)

end CFSG.LieType.Universal.Spin
