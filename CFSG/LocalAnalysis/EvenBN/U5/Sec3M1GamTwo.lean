module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Gam

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem rootI₁_entries {u : hypSU h 2 1} (hu : u ∈ patSub h sI₁ isPattern_sI₁) :
    mat u ιf₂ ιf₁ = h.bar (mat u ιe₁ ιe₂) ∧
      (mat u ιe₁ ιe₁ = 1 ∧ mat u ιe₂ ιe₂ = 1 ∧ mat u ιz ιz = 1 ∧ mat u ιf₁ ιf₁ = 1 ∧
        mat u ιf₂ ιf₂ = 1) ∧
      (mat u ιe₂ ιe₁ = 0 ∧ mat u ιz ιe₁ = 0 ∧ mat u ιf₂ ιe₁ = 0 ∧ mat u ιf₁ ιe₁ = 0 ∧
        mat u ιz ιe₂ = 0 ∧ mat u ιf₂ ιe₂ = 0 ∧ mat u ιf₁ ιe₂ = 0 ∧ mat u ιf₂ ιz = 0 ∧
        mat u ιf₁ ιz = 0 ∧ mat u ιf₁ ιf₂ = 0) ∧
      (mat u ιe₁ ιz = 0 ∧ mat u ιz ιf₁ = 0 ∧ mat u ιe₂ ιz = 0 ∧ mat u ιz ιf₂ = 0 ∧
        mat u ιe₁ ιf₂ = 0 ∧ mat u ιe₂ ιf₁ = 0 ∧ mat u ιe₂ ιf₂ = 0 ∧ mat u ιe₁ ιf₁ = 0) := by
  obtain ⟨huU, a1⟩ := mem_patSub_sI₁.1 hu
  exact ⟨(U_rel huU).1, (U_entries huU).1, (U_entries huU).2, a1⟩

theorem lmat_structure_of_centralizes (hf : 2 ≤ f) {x : Gam h}
    (hI : ∀ i ∈ I₁sub h, ∃ s ∈ hypScalars h 2 1, actΓ h x i = s * i)
    (hU : ∀ u ∈ patSub h sI₁ isPattern_sI₁, actΓ h x u = u) :
    x.1.right = 1 ∧
      (∀ i : Fin 2, lmat x (.inl i) ιz = 0 ∧ lmat x (.inr (.inr i)) ιz = 0 ∧
        lmat x ιz (.inl i) = 0 ∧ lmat x ιz (.inr (.inr i)) = 0) ∧
      (∀ i j : Fin 2, lmat x (.inl i) (.inr (.inr j)) = 0 ∧
        lmat x (.inr (.inr i)) (.inl j) = 0) ∧
      lmat x ιe₂ ιe₁ = 0 ∧ lmat x ιf₁ ιf₂ = 0 ∧ lmat x ιe₁ ιe₁ = lmat x ιe₂ ιe₂ ∧
      lmat x ιe₁ ιe₁ ≠ 0 ∧ lmat x ιf₁ ιf₁ = lmat x ιf₂ ιf₂ := by
  obtain ⟨j, hj, β, -, hβ, hbar, e1, e2, e3, e4, e5⟩ := exists_I₁_fifth (h := h) hf
  obtain ⟨s, hs, hjs⟩ := hI j hj
  have hfix := act_pow_five_eq hs hjs
  have ht : j ^ 5 ∈ hypTorus h 2 1 := pow_mem (torusEq_le _ hj) 5
  obtain ⟨hz, hcase⟩ := lmat_blocks_of_fixed ht hfix hβ e1 e2 e3 e4 e5
  obtain ⟨r1, r2, r3, r21, r11, r12⟩ := root_relations hU
  have hEF : ∀ i j : Fin 2, lmat x (.inl i) (.inr (.inr j)) = 0 ∧
      lmat x (.inr (.inr i)) (.inl j) = 0 := by
    rcases hcase with h1 | ⟨hσβ, hEE⟩
    · exact h1.2
    exfalso
    have hf2 : lmat x ιf₂ ιe₁ ≠ 0 := by
      obtain ⟨a, ha⟩ := lmat_col_ne_zero x ιe₁
      rcases a with i | m | i
      · exact absurd (hEE i 0).1 ha
      · fin_cases m
        exact absurd (hz 0).2.2.1 ha
      · fin_cases i
        · exact absurd r11 ha
        · exact ha
    have k0 := r2 1
    rw [map_one, map_one, one_mul, one_mul] at k0
    have hσbar : ∀ c, x.1.right c = h.bar c := fun c => by
      have k1 := r2 c
      rw [← k0] at k1
      exact mul_right_cancel₀ hf2 k1
    rw [hσbar, hbar] at hσβ
    exact hβ hσβ
  have h11 : lmat x ιe₁ ιe₁ ≠ 0 := by
    obtain ⟨a, ha⟩ := lmat_col_ne_zero x ιe₁
    rcases a with i | m | i
    · fin_cases i
      · exact ha
      · exact absurd r21 ha
    · fin_cases m
      exact absurd (hz 0).2.2.1 ha
    · exact absurd (hEF i 0).2 ha
  have k0 := r1 1
  rw [map_one, one_mul, one_mul] at k0
  have hσ : x.1.right = 1 := RingEquiv.ext fun c => by
    have k1 := r1 c
    rw [← k0] at k1
    exact mul_right_cancel₀ h11 (k1.trans (mul_comm _ _).symm |>.trans (mul_comm _ _))
  have k3 := r3 1
  rw [map_one, map_one, one_mul, one_mul] at k3
  exact ⟨hσ, hz, hEF, r21, r12, k0, h11, k3.symm⟩

theorem Phi_eq_one_of_centralizes_I₁N₁ (hf : 2 ≤ f) {x : Gam h}
    (hI : ∀ i ∈ I₁sub h, ∃ s ∈ hypScalars h 2 1, actΓ h x i = s * i)
    (hU : ∀ u ∈ patSub h sI₁ isPattern_sI₁, actΓ h x u = u) (hr : actΓ h x (rSU h) = rSU h)
    {k : ℕ} (hk : Phi h x ^ 2 ^ k = 1) : Phi h x = 1 := by
  obtain ⟨hσ, hz, hEF, h21, h12f, -, h11, -⟩ := lmat_structure_of_centralizes hf hI hU
  set A := lmat x with hA
  have hAr : A * mat (rSU h) = mat (rSU h) * A := by
    have e := lmat_mul_map x (rSU h)
    rwa [map_mat_rSU, hr] at e
  have hsym := rSU_comm_core hAr
  have h12 : A ιe₁ ιe₂ = 0 := by
    have := hsym ιe₁ ιe₂
    rwa [show σr ιe₁ = ιe₂ by decide, show σr ιe₂ = ιe₁ by decide, h21] at this
  have h21f : A ιf₂ ιf₁ = 0 := by
    have := hsym ιf₂ ιf₁
    rwa [show σr ιf₂ = ιf₁ by decide, show σr ιf₁ = ιf₂ by decide, h12f] at this
  have hdiag : A = diagonal fun a => A a a :=
    eq_diagonal_of_block
      (forall_W ⟨h12, (hEF 0 1).2, h21, (hEF 1 0).1⟩ ⟨(hz 0).1, (hz 0).2.1, (hz 0).2.2.1,
        (hz 0).2.2.2⟩ ⟨(hEF 0 1).1, h12f, (hEF 1 0).2, h21f⟩)
      (hEF 0 0).1 (hEF 0 0).2 (hz 1).1 (hEF 1 1).1 (hz 1).2.2.1 (hz 1).2.2.2 (hEF 1 1).2
      (hz 1).2.1
  have hpow : ∀ n : ℕ, (x ^ n).1.right = 1 ∧ lmat (x ^ n) = A ^ n := by
    intro n
    induction n with
    | zero => exact ⟨by simp, by rw [pow_zero, pow_zero]; rfl⟩
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ', Subgroup.coe_mul, SemidirectProduct.mul_right, hσ, ih.1, mul_one]
      · rw [pow_succ', lmat_mul_of_right_one hσ, ih.2, ← pow_succ']
  obtain ⟨-, c, hc⟩ := Phi_eq_one_iff.1 (show Phi h (x ^ 2 ^ k) = 1 by rw [map_pow]; exact hk)
  have hAk : A ^ 2 ^ k = Matrix.scalar (HypIndex 2 1) (c : K) := by
    rw [← (hpow (2 ^ k)).2, lmat, hc, GeneralLinearGroup.coe_scalar]
  have hd : ∀ a, A a a ^ 2 ^ k = c := by
    intro a
    have e := congrFun (congrFun hAk a) a
    rw [hdiag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at e
    exact e
  have hAeq : ∀ a, A a a = A ιe₁ ιe₁ := fun a => by
    have := eq_one_of_pow_two_pow_eq_one h (c := A a a / A ιe₁ ιe₁) (k := k)
      (by rw [div_pow, hd, hd, div_self c.ne_zero])
    exact (div_eq_one_iff_eq h11).1 this
  refine Phi_eq_one_iff.2 ⟨hσ, Units.mk0 (A ιe₁ ιe₁) h11, ?_⟩
  apply Units.ext
  change A = _
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, hdiag, Matrix.scalar_apply]
  congr 1
  funext a
  exact hAeq a

theorem exists_eq_innM_of_centralizes (hf : 2 ≤ f) {x : Gam h}
    (hI : ∀ i ∈ I₁sub h, ∃ s ∈ hypScalars h 2 1, actΓ h x i = s * i)
    (hU : ∀ u ∈ patSub h sI₁ isPattern_sI₁, actΓ h x u = u) (hx : Phi h x ^ 2 = 1) :
    ∃ u ∈ patSub h sI₁ isPattern_sI₁, Phi h x = innM h u := by
  have := h.charP
  obtain ⟨hσ, hz, hEF, h21, h12f, h11e, h11, hff⟩ := lmat_structure_of_centralizes hf hI hU
  set A := lmat x with hA
  obtain ⟨-, c, hc⟩ := Phi_eq_one_iff.1 (show Phi h (x * x) = 1 by
    rw [map_mul]; exact (sq (Phi h x)).symm.trans hx)
  have hA2 : A * A = Matrix.scalar (HypIndex 2 1) (c : K) := by
    rw [← lmat_mul_of_right_one hσ, lmat, hc, GeneralLinearGroup.coe_scalar]
  have hsq : ∀ a, (A * A) a a = (c : K) := fun a => by
    rw [hA2, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  have q1 := hsq ιe₁
  have q3 := hsq ιz
  have q4 := hsq ιf₁
  simp only [Matrix.mul_apply, sum_hypIndex_two, h21, (hz 0).1, (hz 0).2.2.1, (hEF 0 0).1,
    (hEF 0 0).2, (hEF 0 1).1, (hEF 1 0).2, (hz 0).2.1, (hz 0).2.2.2, (hz 1).1, (hz 1).2.1,
    (hz 1).2.2.1, (hz 1).2.2.2, (hEF 0 1).2, (hEF 1 0).1, h12f, mul_zero, zero_mul, add_zero,
    zero_add] at q1 q3 q4
  have hroot : ∀ a b : K, a * a = b * b → a = b := fun a b e => by
    have : (a - b) * (a - b) = 0 := by
      linear_combination e + (b * (b - a)) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  set α := A ιe₁ ιe₁ with hα
  have hζ : A ιz ιz = α := hroot _ _ (q3.trans q1.symm)
  have hδ : A ιf₁ ιf₁ = α := hroot _ _ (q4.trans q1.symm)
  obtain ⟨μ, -, -, hsim⟩ := x.2
  have g := congrFun (congrFun hsim ιe₂) ιf₁
  change ((A.map h.bar)ᵀ * hypGram 2 1 K * A) ιe₂ ιf₁ = _ at g
  rw [Matrix.mul_apply] at g
  simp only [sum_hypIndex_two, mul_hypGram_apply, Matrix.transpose_apply, Matrix.map_apply,
    hypPartner_inl, hypPartner_inr_inl, hypPartner_inr_inr, Matrix.smul_apply,
    hypGram_inl_inr_inr, smul_eq_mul] at g
  rw [ite_eq_right_iff.2 (fun h1 => absurd h1 (by decide)), mul_zero, (hEF 0 1).2, (hEF 1 1).2, (hz 1).2.2.1, (hz 0).2.2.2,
    (hEF 0 0).1, (hEF 1 0).1, hδ, ← h11e] at g
  simp only [map_zero, mul_zero, zero_add] at g
  set ε := A ιe₁ ιe₂ / α with hε
  obtain ⟨u, hu, hue⟩ := exists_rootI₁ h ε
  obtain ⟨hubar, ⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
    ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩⟩ := rootI₁_entries hu
  have hbα : h.bar α ≠ 0 := (map_ne_zero h.bar).2 h11
  have hd : A ιf₂ ιf₁ = α * h.bar ε := by
    rw [hε, map_div₀, mul_div_assoc', eq_div_iff hbα]
    linear_combination g - (α * h.bar (A ιe₁ ιe₂)) * (CharTwo.two_eq_zero : (2 : K) = 0)
  have hAu : A = α • mat u := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul]
    rcases a with i | m | i <;> rcases b with j | l | j
    · fin_cases i <;> fin_cases j
      · show A ιe₁ ιe₁ = α * mat u ιe₁ ιe₁
        rw [d1, mul_one]
      · show A ιe₁ ιe₂ = α * mat u ιe₁ ιe₂
        rw [hue, hε]
        field_simp
      · show A ιe₂ ιe₁ = α * mat u ιe₂ ιe₁
        rw [l1, mul_zero, h21]
      · show A ιe₂ ιe₂ = α * mat u ιe₂ ιe₂
        rw [d2, mul_one, ← h11e]
    · fin_cases i <;> fin_cases l
      · show A ιe₁ ιz = α * mat u ιe₁ ιz
        rw [a1, mul_zero, (hz 0).1]
      · show A ιe₂ ιz = α * mat u ιe₂ ιz
        rw [a3, mul_zero, (hz 1).1]
    · fin_cases i <;> fin_cases j
      · show A ιe₁ ιf₁ = α * mat u ιe₁ ιf₁
        rw [a8, mul_zero, (hEF 0 0).1]
      · show A ιe₁ ιf₂ = α * mat u ιe₁ ιf₂
        rw [a5, mul_zero, (hEF 0 1).1]
      · show A ιe₂ ιf₁ = α * mat u ιe₂ ιf₁
        rw [a6, mul_zero, (hEF 1 0).1]
      · show A ιe₂ ιf₂ = α * mat u ιe₂ ιf₂
        rw [a7, mul_zero, (hEF 1 1).1]
    · fin_cases m
      fin_cases j
      · show A ιz ιe₁ = α * mat u ιz ιe₁
        rw [l2, mul_zero, (hz 0).2.2.1]
      · show A ιz ιe₂ = α * mat u ιz ιe₂
        rw [l5, mul_zero, (hz 1).2.2.1]
    · fin_cases m
      fin_cases l
      show A ιz ιz = α * mat u ιz ιz
      rw [d3, mul_one, hζ]
    · fin_cases m
      fin_cases j
      · show A ιz ιf₁ = α * mat u ιz ιf₁
        rw [a2, mul_zero, (hz 0).2.2.2]
      · show A ιz ιf₂ = α * mat u ιz ιf₂
        rw [a4, mul_zero, (hz 1).2.2.2]
    · fin_cases i <;> fin_cases j
      · show A ιf₁ ιe₁ = α * mat u ιf₁ ιe₁
        rw [l4, mul_zero, (hEF 0 0).2]
      · show A ιf₁ ιe₂ = α * mat u ιf₁ ιe₂
        rw [l7, mul_zero, (hEF 0 1).2]
      · show A ιf₂ ιe₁ = α * mat u ιf₂ ιe₁
        rw [l3, mul_zero, (hEF 1 0).2]
      · show A ιf₂ ιe₂ = α * mat u ιf₂ ιe₂
        rw [l6, mul_zero, (hEF 1 1).2]
    · fin_cases i <;> fin_cases l
      · show A ιf₁ ιz = α * mat u ιf₁ ιz
        rw [l9, mul_zero, (hz 0).2.1]
      · show A ιf₂ ιz = α * mat u ιf₂ ιz
        rw [l8, mul_zero, (hz 1).2.1]
    · fin_cases i <;> fin_cases j
      · show A ιf₁ ιf₁ = α * mat u ιf₁ ιf₁
        rw [d4, mul_one, hδ]
      · show A ιf₁ ιf₂ = α * mat u ιf₁ ιf₂
        rw [l10, mul_zero, h12f]
      · show A ιf₂ ιf₁ = α * mat u ιf₂ ιf₁
        rw [hubar, hue, hd]
      · show A ιf₂ ιf₂ = α * mat u ιf₂ ιf₂
        rw [d5, mul_one, ← hff, hδ]
  have hy : Phi h ((inlG u)⁻¹ * x) = 1 := by
    refine Phi_eq_one_iff.2 ⟨?_, Units.mk0 α h11, ?_⟩
    · simp [inlG, hσ]
    · have e : ((inlG u)⁻¹ * x).1.left = (u : GL (HypIndex 2 1) K)⁻¹ * x.1.left := by
        simp [inlG]
      rw [e]
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0]
      change (((u : GL (HypIndex 2 1) K)⁻¹ : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) * A = _
      rw [hAu, Matrix.mul_smul]
      change _ • (((u : GL (HypIndex 2 1) K)⁻¹ : GL (HypIndex 2 1) K) *
        (u : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
      rw [Units.inv_mul, Matrix.smul_one_eq_diagonal]
      rfl
  refine ⟨u, hu, ?_⟩
  calc Phi h x = Phi h (inlG u * ((inlG u)⁻¹ * x)) := by rw [mul_inv_cancel_left]
    _ = innM h u := by rw [map_mul, hy, mul_one, Phi_inlG]

end Model

end CFSG.LocalAnalysis.EvenBN.U5
