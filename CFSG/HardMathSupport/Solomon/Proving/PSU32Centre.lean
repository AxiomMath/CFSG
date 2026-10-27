module

public import CFSG.HardMathSupport.Solomon.Proving.MonomialCentralizer
public import CFSG.HardMathSupport.Solomon.Proving.SU32Diagonal
public import CFSG.HardMathSupport.Solomon.Proving.QuotientCentre
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open Matrix CFSG.Open

def permT : Fin 3 → Fin 3 := ![1, 0, 2]

def permR : Fin 3 → Fin 3 := ![0, 2, 1]

theorem permT_invol : ∀ x, permT (permT x) = x := by decide

theorem permR_invol : ∀ x, permR (permR x) = x := by decide

def swap01 (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

def swap12 (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem mul_swap01_apply {K : Type} [Field K] (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (M * swap01 K) i j = M i (permT j) := by
  fin_cases i <;> fin_cases j <;> simp [swap01, permT, Matrix.mul_apply, Fin.sum_univ_three]

theorem swap01_mul_apply {K : Type} [Field K] (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (swap01 K * M) i j = M (permT i) j := by
  fin_cases i <;> fin_cases j <;> simp [swap01, permT, Matrix.mul_apply, Fin.sum_univ_three]

theorem mul_swap12_apply {K : Type} [Field K] (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (M * swap12 K) i j = M i (permR j) := by
  fin_cases i <;> fin_cases j <;> simp [swap12, permR, Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12_mul_apply {K : Type} [Field K] (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (swap12 K * M) i j = M (permR i) j := by
  fin_cases i <;> fin_cases j <;> simp [swap12, permR, Matrix.mul_apply, Fin.sum_univ_three]

theorem eq_smul_one_of_relations {K : Type} [Field K] (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0) (d : Fin 3 → K) (hd : Function.Injective d) (μ : K)
    (hD : M * Matrix.diagonal d = μ • (Matrix.diagonal d * M))
    (ν : K) (hT : M * swap01 K = ν • (swap01 K * M))
    (ν' : K) (hR : M * swap12 K = ν' • (swap12 K * M)) :
    ∃ l : K, M = l • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have eT : ∀ i j, M i (permT j) = ν * M (permT i) j := by
    intro i j
    have e := congrFun (congrFun hT i) j
    rw [mul_swap01_apply, Matrix.smul_apply, swap01_mul_apply, smul_eq_mul] at e
    exact e
  have eR : ∀ i j, M i (permR j) = ν' * M (permR i) j := by
    intro i j
    have e := congrFun (congrFun hR i) j
    rw [mul_swap12_apply, Matrix.smul_apply, swap12_mul_apply, smul_eq_mul] at e
    exact e
  have hrow : ∀ i, ∃ j, M i j ≠ 0 := fun i => exists_entry_ne_zero_of_det_ne_zero M hM i
  choose σ hσ using hrow
  have huniq : ∀ i j, M i j ≠ 0 → j = σ i := fun i j hj =>
    eq_of_entry_ne_zero_of_diag_injective d hd μ M hD i j (σ i) hj (hσ i)
  have hcT : ∀ i, σ (permT i) = permT (σ i) := by
    intro i
    have hne : M (permT i) (permT (σ i)) ≠ 0 := by
      intro h0
      apply hσ i
      have e := eT i (permT (σ i))
      rw [permT_invol] at e
      rw [e, h0, mul_zero]
    exact (huniq _ _ hne).symm
  have hcR : ∀ i, σ (permR i) = permR (σ i) := by
    intro i
    have hne : M (permR i) (permR (σ i)) ≠ 0 := by
      intro h0
      apply hσ i
      have e := eR i (permR (σ i))
      rw [permR_invol] at e
      rw [e, h0, mul_zero]
    exact (huniq _ _ hne).symm
  have key : ∀ a b c : Fin 3, b = permT a → a = permT b → c = permT c →
      a = permR a → c = permR b → b = permR c → a = 0 ∧ b = 1 ∧ c = 2 := by
    intro a b c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  obtain ⟨ha, hb, hc⟩ := key (σ 0) (σ 1) (σ 2) (hcT 0) (hcT 1) (hcT 2) (hcR 0) (hcR 1) (hcR 2)
  have hid : ∀ i, σ i = i := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  have hdiag : ∀ i j, M i j ≠ 0 → i = j := fun i j h => by
    have := huniq i j h
    rw [hid i] at this
    exact this.symm
  have hdne : ∀ i, M i i ≠ 0 := fun i => by
    have := hσ i
    rwa [hid i] at this
  have hoff : ∀ i j, i ≠ j → M i j = 0 := fun i j hij => by
    by_contra h
    exact hij (hdiag i j h)
  have t01 : M 0 0 = ν * M 1 1 := by simpa [permT] using eT 0 1
  have t22 : M 2 2 = ν * M 2 2 := by simpa [permT] using eT 2 2
  have r00 : M 0 0 = ν' * M 0 0 := by simpa [permR] using eR 0 0
  have r21 : M 2 2 = ν' * M 1 1 := by simpa [permR] using eR 2 1
  have hν : ν = 1 := mul_right_cancel₀ (hdne 2) (by linear_combination -t22)
  have hν' : ν' = 1 := mul_right_cancel₀ (hdne 0) (by linear_combination -r00)
  have h01 : M 0 0 = M 1 1 := by rw [t01, hν, one_mul]
  have h12 : M 2 2 = M 1 1 := by rw [r21, hν', one_mul]
  refine ⟨M 0 0, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i
    · simp
    · simp [h01]
    · simp [h12, h01]
  · simp [Matrix.one_apply_ne hij, hoff i j hij]

theorem one_add_one_eq_zero_of_card_four (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    (1 : K) + 1 = 0 := by
  have := charP_two_of_card_four K hK
  rw [← CharP.cast_eq_zero K 2]
  norm_num

theorem exists_ne_zero_ne_one (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∃ x : K, x ≠ 0 ∧ x ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set K) ⊆ ({0, 1} : Set K) := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [h x hx]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({0, 1} : Set K).ncard ≤ 2 :=
    (Set.ncard_insert_le 0 {1}).trans (by simp)
  rw [Set.ncard_univ, hK] at h1
  omega

theorem exists_swap01_mem_StatedSU_three_two (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    ∃ A : GL (Fin 3) K, (A : Matrix (Fin 3) (Fin 3) K) = swap01 K ∧ A ∈ StatedSU 3 2 K := by
  have h11 := one_add_one_eq_zero_of_card_four K hK
  have hneg : (-1 : K) = 1 := by linear_combination -h11
  have hdet : (swap01 K).det = 1 := by
    simp [swap01, Matrix.det_fin_three, hneg]
  have hu : IsUnit (swap01 K) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact isUnit_one)
  refine ⟨hu.unit, hu.unit_spec, ?_⟩
  rw [mem_StatedSU_three_two_iff K hK, hu.unit_spec]
  refine ⟨hdet, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap01, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_swap12_mem_StatedSU_three_two (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    ∃ A : GL (Fin 3) K, (A : Matrix (Fin 3) (Fin 3) K) = swap12 K ∧ A ∈ StatedSU 3 2 K := by
  have h11 := one_add_one_eq_zero_of_card_four K hK
  have hneg : (-1 : K) = 1 := by linear_combination -h11
  have hdet : (swap12 K).det = 1 := by
    simp [swap12, Matrix.det_fin_three, hneg]
  have hu : IsUnit (swap12 K) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact isUnit_one)
  refine ⟨hu.unit, hu.unit_spec, ?_⟩
  rw [mem_StatedSU_three_two_iff K hK, hu.unit_spec]
  refine ⟨hdet, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap12, Matrix.mul_apply, Fin.sum_univ_three]

theorem mem_statedScalars_of_eq_smul_one {K : Type} [Field K] (g : GL (Fin 3) K) (l : K)
    (hl : l ≠ 0) (h : (g : Matrix (Fin 3) (Fin 3) K) = l • (1 : Matrix (Fin 3) (Fin 3) K)) :
    g ∈ StatedScalars (Fin 3) K := by
  refine ⟨Units.mk0 l hl, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
  rw [← Units.val_mk0 hl] at h
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [h]
  · simp [h, Matrix.one_apply_ne hij, hij]

theorem center_stated_proj_su_three_two_eq_bot (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    Subgroup.center (StatedProj (StatedSU 3 2 K)) = ⊥ := by
  obtain ⟨x, hx0, hx1⟩ := exists_ne_zero_ne_one K hK
  have h4 := pow_four_eq_self K hK
  have hq : x ^ 2 + x + 1 = 0 :=
    ((eq_zero_or_one_or_quad_of_card_four h4 x).resolve_left hx0).resolve_left hx1
  have hx3 : x ^ 3 = 1 := cube_eq_one_of_ne_zero h4 hx0
  have h11 := one_add_one_eq_zero_of_card_four K hK
  have h2x : x + x = 0 := by linear_combination x * h11
  obtain ⟨D, hDm, hD⟩ := exists_diag_mem_StatedSU_three_two K hK 1 x (x ^ 2) one_ne_zero hx0
    (pow_ne_zero 2 hx0) (by linear_combination hx3)
  obtain ⟨T1, hT1m, hT1⟩ := exists_swap01_mem_StatedSU_three_two K hK
  obtain ⟨T2, hT2m, hT2⟩ := exists_swap12_mem_StatedSU_three_two K hK
  have f1 : (1 : K) ≠ x := fun h => hx1 h.symm
  have f2 : (1 : K) ≠ x ^ 2 := fun h => hx0 (by linear_combination hq + h - h11)
  have f3 : x ≠ x ^ 2 := fun h => one_ne_zero (by linear_combination hq + h - h2x)
  have hinj : Function.Injective (![1, x, x ^ 2] : Fin 3 → K) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso; simp [f1, f2, f3, hx1, Ne.symm f2, Ne.symm f3] at hij)
  refine center_quotient_eq_bot_of_generators _ {⟨D, hD⟩, ⟨T1, hT1⟩, ⟨T2, hT2⟩} ?_
  intro g hg
  have hD' := hg ⟨D, hD⟩ (by simp)
  have hT1' := hg ⟨T1, hT1⟩ (by simp)
  have hT2' := hg ⟨T2, hT2⟩ (by simp)
  have c1 : (g : GL (Fin 3) K) * D * (g : GL (Fin 3) K)⁻¹ * D⁻¹ ∈ StatedScalars (Fin 3) K :=
    Subgroup.mem_subgroupOf.1 hD'
  have c2 : (g : GL (Fin 3) K) * T1 * (g : GL (Fin 3) K)⁻¹ * T1⁻¹ ∈ StatedScalars (Fin 3) K :=
    Subgroup.mem_subgroupOf.1 hT1'
  have c3 : (g : GL (Fin 3) K) * T2 * (g : GL (Fin 3) K)⁻¹ * T2⁻¹ ∈ StatedScalars (Fin 3) K :=
    Subgroup.mem_subgroupOf.1 hT2'
  obtain ⟨μ, hμ⟩ := exists_smul_mul_of_comm_mem_scalar (g : GL (Fin 3) K) D c1
  obtain ⟨ν, hν⟩ := exists_smul_mul_of_comm_mem_scalar (g : GL (Fin 3) K) T1 c2
  obtain ⟨ν', hν'⟩ := exists_smul_mul_of_comm_mem_scalar (g : GL (Fin 3) K) T2 c3
  rw [hDm] at hμ
  rw [hT1m] at hν
  rw [hT2m] at hν'
  have hdet : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    have hu : IsUnit ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := Units.isUnit _
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  obtain ⟨l, hl⟩ := eq_smul_one_of_relations ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) hdet
    _ hinj μ hμ ν hν ν' hν'
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hdet
    rw [hl, zero_smul]
    exact Matrix.det_zero
  exact Subgroup.mem_subgroupOf.2 (mem_statedScalars_of_eq_smul_one _ l hl0 hl)

theorem center_eq_bot_of_mulEquiv_center {Y G : Type} [Group Y] [Group G] (e : Y ≃* G)
    (hG : Subgroup.center G = ⊥) : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hc : e z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [Subgroup.mem_center_iff] at hz
    rw [← map_mul, ← map_mul, hz y]
  rw [hG, Subgroup.mem_bot] at hc
  rw [Subgroup.mem_bot]
  apply e.injective
  rw [hc, map_one]

theorem center_eq_bot_of_su_three_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4)
    (Y : Type) [Group Y] (e : Y ≃* StatedProj (StatedSU 3 2 K)) : Subgroup.center Y = ⊥ :=
  center_eq_bot_of_mulEquiv_center e (center_stated_proj_su_three_two_eq_bot K hK)

end CFSG.HardMathSupport.Solomon.Proving
