module

public import CFSG.LieType.SeitzGeneration.UnitaryTwoStep

public section

namespace CFSG.LieType.SeitzGeneration.UnitaryTwo

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration.Centers

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] noncomputable def diagSU (σ : K ≃+* K) (d : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1)
    (hdet : ∏ i, d i = 1) : SUid σ n :=
  mkSU σ (Matrix.diagonal d) (by rw [Matrix.det_diagonal]; exact hdet) (fun x y => by
    simp only [herm, Matrix.mulVec_diagonal, map_mul]
    exact Finset.sum_congr rfl fun i _ => by linear_combination (σ (x i) * y i) * hd i)

theorem diagSU_smul (d : Fin n → K) (hd : ∀ i, σ (d i) * d i = 1) (hdet : ∏ i, d i = 1)
    (v : Fin n → K) (i : Fin n) : (diagSU σ d hd hdet • v) i = d i * v i := by
  simp [diagSU, Matrix.mulVec_diagonal]

@[expose] def omegaAt (ω : K) (a : Fin n) : Fin n → K := fun i => if i = a then ω else 1

theorem prod_omegaAt (ω : K) (a : Fin n) : ∏ i, omegaAt ω a i = ω := by
  simp [omegaAt, Finset.prod_ite_eq']

theorem norm_omegaAt {ω : K} (hω : σ ω * ω = 1) (a i : Fin n) :
    σ (omegaAt ω a i) * omegaAt ω a i = 1 := by
  unfold omegaAt
  split_ifs
  · exact hω
  · simp

@[expose] noncomputable def tripleSU (σ : K ≃+* K) {ω : K} (hω : σ ω * ω = 1) (hω3 : ω ^ 3 = 1)
    (a b c : Fin n) : SUid σ n :=
  diagSU σ (omegaAt ω a * omegaAt ω b * omegaAt ω c)
    (fun i => by
      simp only [Pi.mul_apply, map_mul]
      calc σ (omegaAt ω a i) * σ (omegaAt ω b i) * σ (omegaAt ω c i) *
            (omegaAt ω a i * omegaAt ω b i * omegaAt ω c i)
          = (σ (omegaAt ω a i) * omegaAt ω a i) * (σ (omegaAt ω b i) * omegaAt ω b i) *
            (σ (omegaAt ω c i) * omegaAt ω c i) := by ring
        _ = 1 := by rw [norm_omegaAt hω, norm_omegaAt hω, norm_omegaAt hω]; ring)
    (by
      simp only [Pi.mul_apply]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      simp only [prod_omegaAt]
      linear_combination hω3)

theorem tripleSU_smul {ω : K} (hω : σ ω * ω = 1) (hω3 : ω ^ 3 = 1) (a b c : Fin n)
    (v : Fin n → K) (i : Fin n) :
    (tripleSU σ hω hω3 a b c • v) i = omegaAt ω a i * omegaAt ω b i * omegaAt ω c i * v i := by
  simp only [tripleSU]
  rw [diagSU_smul]
  rfl

theorem frameSpan_apply_eq_zero {j : ℕ} {v : Fin n → K} (hv : v ∈ frameSpan K n j)
    (i : Fin n) (hi : j ≤ i.val) : v i = 0 := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, hk, rfl⟩ := hw
    have hik : i ≠ k := fun h => by
      subst h
      omega
    simp [hik]
  | zero => rfl
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

section Concrete

@[expose] noncomputable def x₁ (σ : K ≃+* K) {ω : K} (hω : σ ω * ω = 1) (hω3 : ω ^ 3 = 1)
    (hn : 5 ≤ n) : SUid σ n :=
  tripleSU σ hω hω3 ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨4, by omega⟩

@[expose] noncomputable def x₂ (σ : K ≃+* K) {ω : K} (hω : σ ω * ω = 1) (hω3 : ω ^ 3 = 1)
    (hn : 5 ≤ n) : SUid σ n :=
  tripleSU σ hω hω3 ⟨2, by omega⟩ ⟨3, by omega⟩ ⟨4, by omega⟩

variable {ω : K} (hω : σ ω * ω = 1) (hω3 : ω ^ 3 = 1) (hn : 5 ≤ n)

include hω hω3 hn

theorem x₁_smul_apply (v : Fin n → K) (i : Fin n) :
    (x₁ σ hω hω3 hn • v) i = (if i.val = 0 ∨ i.val = 1 ∨ i.val = 4 then ω else 1) * v i := by
  rw [x₁, tripleSU_smul]
  by_cases h0 : i.val = 0
  · simp [omegaAt, Fin.ext_iff, h0]
  by_cases h1 : i.val = 1
  · simp [omegaAt, Fin.ext_iff, h1]
  by_cases h4 : i.val = 4
  · simp [omegaAt, Fin.ext_iff, h4]
  simp [omegaAt, Fin.ext_iff, h0, h1, h4]

theorem x₂_smul_apply (v : Fin n → K) (i : Fin n) :
    (x₂ σ hω hω3 hn • v) i = (if i.val = 2 ∨ i.val = 3 ∨ i.val = 4 then ω else 1) * v i := by
  rw [x₂, tripleSU_smul]
  by_cases h2 : i.val = 2
  · simp [omegaAt, Fin.ext_iff, h2]
  by_cases h3 : i.val = 3
  · simp [omegaAt, Fin.ext_iff, h3]
  by_cases h4 : i.val = 4
  · simp [omegaAt, Fin.ext_iff, h4]
  simp [omegaAt, Fin.ext_iff, h2, h3, h4]

theorem x₁_mul_x₂_smul_apply (v : Fin n → K) (i : Fin n) :
    ((x₁ σ hω hω3 hn * x₂ σ hω hω3 hn) • v) i =
      (if i.val = 0 ∨ i.val = 1 ∨ i.val = 4 then ω else 1) *
        ((if i.val = 2 ∨ i.val = 3 ∨ i.val = 4 then ω else 1) * v i) := by
  rw [mul_smul, x₁_smul_apply hω hω3 hn, x₂_smul_apply hω hω3 hn]

theorem x₁_comm_x₂ : x₁ σ hω hω3 hn * x₂ σ hω hω3 hn = x₂ σ hω hω3 hn * x₁ σ hω hω3 hn := by
  apply ext_smul σ
  intro v
  funext i
  rw [x₁_mul_x₂_smul_apply hω hω3 hn, mul_smul, x₂_smul_apply hω hω3 hn,
    x₁_smul_apply hω hω3 hn]
  ring

theorem x₁_cube : x₁ σ hω hω3 hn ^ 3 = 1 := by
  apply ext_smul σ
  intro v
  funext i
  have h : ∀ w : Fin n → K, ∀ j, (x₁ σ hω hω3 hn • w) j =
      (if j.val = 0 ∨ j.val = 1 ∨ j.val = 4 then ω else 1) * w j := x₁_smul_apply hω hω3 hn
  rw [pow_three', mul_smul, mul_smul, h, h, h]
  by_cases hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 4
  · simp only [hi, ite_true, one_smul]
    linear_combination (v i) * hω3
  · simp [hi]

theorem x₂_cube : x₂ σ hω hω3 hn ^ 3 = 1 := by
  apply ext_smul σ
  intro v
  funext i
  have h : ∀ w : Fin n → K, ∀ j, (x₂ σ hω hω3 hn • w) j =
      (if j.val = 2 ∨ j.val = 3 ∨ j.val = 4 then ω else 1) * w j := x₂_smul_apply hω hω3 hn
  rw [pow_three', mul_smul, mul_smul, h, h, h]
  by_cases hi : i.val = 2 ∨ i.val = 3 ∨ i.val = 4
  · simp only [hi, ite_true, one_smul]
    linear_combination (v i) * hω3
  · simp [hi]

theorem x₁_mul_x₂_smul_of_mem {v : Fin n → K} (hv : v ∈ frameSpan K n 4) :
    (x₁ σ hω hω3 hn * x₂ σ hω hω3 hn) • v = ω • v := by
  funext i
  rw [x₁_mul_x₂_smul_apply hω hω3 hn, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i.val < 4
  · have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hcases with h | h | h | h <;> simp [h]
  · rw [frameSpan_apply_eq_zero hv i (by omega)]
    simp

theorem x₁_smul_pair :
    x₁ σ hω hω3 hn • ((Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨4, by omega⟩ 1 : Fin n → K)) =
      ω • (Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨4, by omega⟩ 1 : Fin n → K) := by
  funext i
  rw [x₁_smul_apply hω hω3 hn, Pi.smul_apply, smul_eq_mul]
  by_cases h0 : i.val = 0
  · simp [Fin.ext_iff, h0]
  by_cases h4 : i.val = 4
  · simp [Fin.ext_iff, h4]
  simp [Fin.ext_iff, h0, h4]

theorem x₁_smul_pair' (j : Fin n) (hj : 5 ≤ j.val) :
    x₁ σ hω hω3 hn • ((Pi.single ⟨2, by omega⟩ 1 + Pi.single j 1 : Fin n → K)) =
      (1 : K) • (Pi.single ⟨2, by omega⟩ 1 + Pi.single j 1 : Fin n → K) := by
  funext i
  rw [x₁_smul_apply hω hω3 hn, Pi.smul_apply, smul_eq_mul]
  by_cases h2 : i.val = 2
  · simp [h2]
  by_cases hij : i = j
  · subst hij
    simp [Fin.ext_iff, h2]
    omega
  simp [Fin.ext_iff, h2, hij]

end Concrete

section Generation

variable {ω : K} (hω : σ ω * ω = 1) (hω3 : ω ^ 3 = 1)

include hω hω3

theorem closure_cent_eq_top (hσ : IsUnitaryInvolution σ) (hq : ∀ c : K, c ≠ 0 → σ c * c = 1)
    (h2 : (1 : K) + 1 = 0) (hn : 5 ≤ n) :
    Subgroup.closure {g : SUid σ n | g * x₁ σ hω hω3 hn = x₁ σ hω hω3 hn * g ∨
      g * x₂ σ hω hω3 hn = x₂ σ hω hω3 hn * g ∨
      g * (x₁ σ hω hω3 hn * x₂ σ hω hω3 hn) = (x₁ σ hω hω3 hn * x₂ σ hω hω3 hn) * g} = ⊤ := by
  set H : Subgroup (SUid σ n) := Subgroup.closure {g : SUid σ n | g * x₁ σ hω hω3 hn =
      x₁ σ hω hω3 hn * g ∨ g * x₂ σ hω hω3 hn = x₂ σ hω hω3 hn * g ∨
      g * (x₁ σ hω hω3 hn * x₂ σ hω hω3 hn) = (x₁ σ hω hω3 hn * x₂ σ hω hω3 hn) * g} with hH
  have hc1 : ∀ g : SUid σ n, g * x₁ σ hω hω3 hn = x₁ σ hω hω3 hn * g → g ∈ H := fun g hg =>
    Subgroup.subset_closure (Or.inl hg)
  have hc12 : ∀ g : SUid σ n, g * (x₁ σ hω hω3 hn * x₂ σ hω hω3 hn) =
      (x₁ σ hω hω3 hn * x₂ σ hω hω3 hn) * g → g ∈ H := fun g hg =>
    Subgroup.subset_closure (Or.inr (Or.inr hg))
  refine eq_top_of_frame hσ hq h2 hn ?_ ?_ ?_
  · intro v hv hiso
    exact isCenter_of_eigen hσ.invol hc12 hiso hω (x₁_mul_x₂_smul_of_mem hω hω3 hn hv)
  · refine isCenter_of_eigen hσ.invol hc1 ?_ hω (x₁_smul_pair hω hω3 hn)
    simp [herm_add_left, herm_add_right, herm_std, Fin.ext_iff, h2]
  · intro j hj
    have hne : (⟨2, by omega⟩ : Fin n) ≠ j := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    refine isCenter_of_eigen hσ.invol hc1 ?_ (by simp : σ 1 * 1 = 1)
      (x₁_smul_pair' hω hω3 hn j hj)
    simp [herm_add_left, herm_add_right, herm_std, hne, hne.symm, h2]

end Generation


end CFSG.LieType.SeitzGeneration.UnitaryTwo
