module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix

variable {n : ℕ} {K : Type} [Field K]

theorem mem_of_forall_dotProduct_eq_zero (W : Submodule K (Fin n → K)) {y : Fin n → K}
    (h : ∀ φ : Fin n → K, (∀ w ∈ W, φ ⬝ᵥ w = 0) → φ ⬝ᵥ y = 0) : y ∈ W := by
  by_contra hy
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hy inferInstance
  have hdot : ∀ x : Fin n → K, f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  apply hf
  rw [hdot]
  refine h _ fun w hw => ?_
  rw [← hdot]
  have : f w ∈ W.map f := ⟨w, hw, rfl⟩
  rwa [hfW, Submodule.mem_bot] at this

theorem exists_ne_zero_forall_dotProduct_eq_zero {W : Submodule K (Fin n → K)} (hW : W ≠ ⊤) :
    ∃ φ : Fin n → K, φ ≠ 0 ∧ ∀ w ∈ W, φ ⬝ᵥ w = 0 := by
  by_contra hcon
  push Not at hcon
  apply hW
  rw [eq_top_iff]
  intro y _
  refine mem_of_forall_dotProduct_eq_zero W fun φ hφ => ?_
  by_contra hne
  exact hne (by
    by_cases h0 : φ = 0
    · rw [h0, zero_dotProduct]
    · exact absurd hφ (hcon φ h0 |>.elim fun w hw => fun hall => hw.2 (hall w hw.1)))

theorem eq_one_of_one_add_vecMulVec (hn : 3 ≤ n) (a α v φ : Fin n → K) (c : K)
    (h : (1 : Matrix (Fin n) (Fin n) K) + vecMulVec a α = c • (1 + vecMulVec v φ)) :
    c = 1 ∧ vecMulVec a α = vecMulVec v φ := by
  let f : (Fin n → K) →ₗ[K] K × K :=
    { toFun := fun u => (φ ⬝ᵥ u, α ⬝ᵥ u)
      map_add' := fun x y => by simp [dotProduct_add]
      map_smul' := fun r x => by simp [dotProduct_smul] }
  have hker : LinearMap.ker f ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hφu : φ ⬝ᵥ u = 0 := (Prod.ext_iff.mp (LinearMap.mem_ker.mp hu)).1
  have hαu : α ⬝ᵥ u = 0 := (Prod.ext_iff.mp (LinearMap.mem_ker.mp hu)).2
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ u) h
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, hφu,
    hαu, MulOpposite.op_zero, zero_smul, add_zero] at h1
  have hc : c = 1 := by
    have h2 : (1 - c) • u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact (sub_eq_zero.mp h3).symm
    · exact absurd h3 hu0
  refine ⟨hc, ?_⟩
  rw [hc, one_smul] at h
  exact add_left_cancel h

theorem exists_smul_of_vecMulVec_eq {a α v φ : Fin n → K} (hv : v ≠ 0) (hφ : φ ≠ 0)
    (h : vecMulVec a α = vecMulVec v φ) : ∃ l : K, l ≠ 0 ∧ a = l • v ∧ φ = l • α := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hφ
  have hent : ∀ i j, a i * α j = v i * φ j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [vecMulVec_apply] using this
  have hv0 : v i₀ ≠ 0 := hi₀
  have hφ0 : φ j₀ ≠ 0 := hj₀
  have ha0 : a i₀ ≠ 0 := by
    intro h0
    have := hent i₀ j₀
    rw [h0, zero_mul] at this
    exact mul_ne_zero hv0 hφ0 this.symm
  refine ⟨a i₀ / v i₀, div_ne_zero ha0 hv0, ?_, ?_⟩
  · ext i
    have h1 := hent i j₀
    have h2 := hent i₀ j₀
    have hα0 : α j₀ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h2
      exact mul_ne_zero hv0 hφ0 h2.symm
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    have h3 : a i * α j₀ * v i₀ = v i * φ j₀ * v i₀ := by rw [h1]
    have h4 : φ j₀ * v i₀ = a i₀ * α j₀ := by rw [mul_comm, h2]
    calc a i * v i₀ = a i * v i₀ * α j₀ / α j₀ := by field_simp
      _ = a i₀ * v i := by
        rw [mul_assoc, mul_comm (v i₀) (α j₀), ← mul_assoc, h1]
        field_simp
        rw [mul_comm (v i) (φ j₀), mul_assoc, mul_comm (v i) (v i₀), ← mul_assoc, h4]
        ring
  · ext j
    have h1 := hent i₀ j
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    rw [h1, mul_comm]

theorem eq_of_vecMulVec_eq_right {x y α : Fin n → K} (hα : α ≠ 0)
    (h : vecMulVec x α = vecMulVec y α) : x = y := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hα
  ext i
  have := congrFun (congrFun h i) j
  simp only [vecMulVec_apply] at this
  exact mul_right_cancel₀ hj this

theorem eq_of_vecMulVec_eq_left {x α β : Fin n → K} (hx : x ≠ 0)
    (h : vecMulVec x α = vecMulVec x β) : α = β := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  ext j
  have := congrFun (congrFun h i) j
  simp only [vecMulVec_apply] at this
  exact mul_left_cancel₀ hi this

theorem vecMulVec_ne_zero {v φ : Fin n → K} (hv : v ≠ 0) (hφ : φ ≠ 0) :
    vecMulVec v φ ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hφ
  intro h
  have := congrFun (congrFun h i) j
  simp only [vecMulVec_apply] at this
  exact mul_ne_zero hi hj this

theorem e0_core (hn : 3 ≤ n) (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)
    (hA' : A' * A = 1) (W : Submodule K (Fin n → K)) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤)
    (hT : ∀ v ∈ W, ∀ φ : Fin n → K, (∀ w ∈ W, φ ⬝ᵥ w = 0) → ∃ c : K,
      (1 : Matrix (Fin n) (Fin n) K) +
          vecMulVec (A *ᵥ fun i => σ (v i)) ((fun i => σ (φ i)) ᵥ* A') =
        c • (1 + vecMulVec v φ)) :
    (∀ c, σ c = c) ∧ ∃ l : K, l ≠ 0 ∧ (∀ w ∈ W, A *ᵥ w = l • w) ∧
      ∀ x, A *ᵥ x - l • x ∈ W := by
  have hT1 : ∀ v ∈ W, ∀ φ : Fin n → K, (∀ w ∈ W, φ ⬝ᵥ w = 0) →
      vecMulVec (A *ᵥ fun i => σ (v i)) ((fun i => σ (φ i)) ᵥ* A') = vecMulVec v φ := by
    intro v hv φ hφ
    obtain ⟨c, hc⟩ := hT v hv φ hφ
    exact (eq_one_of_one_add_vecMulVec hn _ _ _ _ c hc).2
  obtain ⟨v₀, hv₀W, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨φ₀, hφ₀, hφ₀W⟩ := exists_ne_zero_forall_dotProduct_eq_zero hW1
  have hσ : ∀ c, σ c = c := by
    intro c
    have h1 := hT1 (c • v₀) (W.smul_mem c hv₀W) φ₀ hφ₀W
    have h2 := hT1 v₀ hv₀W φ₀ hφ₀W
    have e1 : (fun i => σ ((c • v₀) i)) = σ c • (fun i => σ (v₀ i)) := by
      ext i
      simp
    rw [e1, Matrix.mulVec_smul, smul_vecMulVec, h2, smul_vecMulVec] at h1
    have h3 : (σ c - c) • vecMulVec v₀ φ₀ = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (vecMulVec_ne_zero hv₀ hφ₀)
  have hσf : ∀ v : Fin n → K, (fun i => σ (v i)) = v := fun v => funext fun i => hσ _
  have hT2 : ∀ v ∈ W, ∀ φ : Fin n → K, (∀ w ∈ W, φ ⬝ᵥ w = 0) →
      vecMulVec (A *ᵥ v) (φ ᵥ* A') = vecMulVec v φ := by
    intro v hv φ hφ
    have := hT1 v hv φ hφ
    rwa [hσf v, hσf φ] at this
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : Fin n → K, α₀ = φ₀ ᵥ* A' := ⟨_, rfl⟩
  obtain ⟨l, hl0, hAv₀, hφ₀'⟩ : ∃ l : K, l ≠ 0 ∧ A *ᵥ v₀ = l • v₀ ∧ φ₀ = l • α₀ := by
    refine exists_smul_of_vecMulVec_eq hv₀ hφ₀ ?_
    rw [hα₀]
    exact hT2 v₀ hv₀W φ₀ hφ₀W
  have hα₀ne : α₀ ≠ 0 := by
    intro h0
    apply hφ₀
    rw [hφ₀', h0, smul_zero]
  have hAW : ∀ w ∈ W, A *ᵥ w = l • w := by
    intro w hw
    have h1 := hT2 w hw φ₀ hφ₀W
    rw [← hα₀] at h1
    have h2 : vecMulVec (A *ᵥ w) α₀ = vecMulVec (l • w) α₀ := by
      rw [h1, smul_vecMulVec]
      conv_lhs => rw [hφ₀']
      rw [vecMulVec_smul]
    exact eq_of_vecMulVec_eq_right hα₀ne h2
  have hφA : ∀ φ : Fin n → K, (∀ w ∈ W, φ ⬝ᵥ w = 0) → φ ᵥ* A = l • φ := by
    intro φ hφ
    have h1 := hT2 v₀ hv₀W φ hφ
    rw [hAv₀, smul_vecMulVec, ← vecMulVec_smul] at h1
    have h3 : l • (φ ᵥ* A') = φ := eq_of_vecMulVec_eq_left hv₀ h1
    have h4 : (l • (φ ᵥ* A')) ᵥ* A = φ ᵥ* A := by rw [h3]
    rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, hA', Matrix.vecMul_one] at h4
    exact h4.symm
  refine ⟨hσ, l, hl0, hAW, fun x => ?_⟩
  refine mem_of_forall_dotProduct_eq_zero W fun φ hφ => ?_
  rw [dotProduct_sub, dotProduct_smul, Matrix.dotProduct_mulVec, hφA φ hφ, smul_dotProduct,
    sub_self]

theorem e1_core (hn : 3 ≤ n) (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤)
    (hT : ∀ v ∈ W, ∀ φ : Fin n → K, (∀ w ∈ W, φ ⬝ᵥ w = 0) → ∃ c : K,
      (1 : Matrix (Fin n) (Fin n) K) +
          vecMulVec (-(A *ᵥ fun i => σ (φ i))) ((fun i => σ (v i)) ᵥ* A') =
        c • (1 + vecMulVec v φ)) : False := by
  have hT1 : ∀ v ∈ W, ∀ φ : Fin n → K, (∀ w ∈ W, φ ⬝ᵥ w = 0) →
      vecMulVec (-(A *ᵥ fun i => σ (φ i))) ((fun i => σ (v i)) ᵥ* A') = vecMulVec v φ := by
    intro v hv φ hφ
    obtain ⟨c, hc⟩ := hT v hv φ hφ
    exact (eq_one_of_one_add_vecMulVec hn _ _ _ _ c hc).2
  obtain ⟨v₀, hv₀W, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨φ₀, hφ₀, hφ₀W⟩ := exists_ne_zero_forall_dotProduct_eq_zero hW1
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin n → K, a₀ = A *ᵥ fun i => σ (φ₀ i) := ⟨_, rfl⟩
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : Fin n → K, α₀ = (fun i => σ (v₀ i)) ᵥ* A' := ⟨_, rfl⟩
  have hWa : ∀ v ∈ W, v ∈ Submodule.span K ({a₀} : Set (Fin n → K)) := by
    intro v hv
    by_cases h0 : v = 0
    · rw [h0]
      exact Submodule.zero_mem _
    obtain ⟨l, hl0, hl, -⟩ := exists_smul_of_vecMulVec_eq h0 hφ₀ (hT1 v hv φ₀ hφ₀W)
    rw [← ha₀] at hl
    rw [Submodule.mem_span_singleton]
    refine ⟨-l⁻¹, ?_⟩
    have h1 : a₀ = (-l) • v := by rw [neg_smul, ← hl, neg_neg]
    rw [h1, smul_smul]
    simp [hl0]
  have hφα : ∀ φ : Fin n → K, (∀ w ∈ W, φ ⬝ᵥ w = 0) → ∃ l : K, φ = l • α₀ := by
    intro φ hφ
    by_cases h0 : φ = 0
    · exact ⟨0, by rw [h0, zero_smul]⟩
    obtain ⟨l, -, -, hφl⟩ := exists_smul_of_vecMulVec_eq hv₀ h0 (hT1 v₀ hv₀W φ hφ)
    rw [← hα₀] at hφl
    exact ⟨l, hφl⟩
  let g : (Fin n → K) →ₗ[K] K :=
    { toFun := fun x => α₀ ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun r x => by simp [dotProduct_smul] }
  have hZW : LinearMap.ker g ≤ W := by
    intro x hx
    refine mem_of_forall_dotProduct_eq_zero W fun φ hφ => ?_
    obtain ⟨l, rfl⟩ := hφα φ hφ
    rw [smul_dotProduct]
    have h1 : α₀ ⬝ᵥ x = 0 := hx
    rw [h1, smul_zero]
  have h1 : Module.finrank K (LinearMap.ker g) ≤ 1 := by
    calc Module.finrank K (LinearMap.ker g)
        ≤ Module.finrank K (Submodule.span K ({a₀} : Set (Fin n → K))) :=
          Submodule.finrank_mono (hZW.trans (fun x hx => hWa x hx))
      _ ≤ 1 := by
        by_cases ha : a₀ = 0
        · rw [ha, Submodule.span_zero_singleton, finrank_bot]
          exact zero_le_one
        · exact (finrank_span_singleton ha).le
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  have h3 : Module.finrank K (LinearMap.range g) ≤ 1 := by
    calc Module.finrank K (LinearMap.range g) ≤ Module.finrank K K := Submodule.finrank_le _
      _ = 1 := Module.finrank_self K
  rw [Module.finrank_fin_fun] at h2
  omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
