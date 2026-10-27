module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpBasic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open Matrix

variable {F : Type} [Field F]

theorem exists_form_eq_one {n : ℕ} {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0) :
    ∃ w, form v w = 1 := by
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hc : v a * sgn F a ≠ 0 := mul_ne_zero ha (sgn_ne_zero a)
  refine ⟨(v a * sgn F a)⁻¹ • Pi.single (par a) 1, ?_⟩
  rw [form_smul_right, form_single_right, par_par, inv_mul_cancel₀ hc]

theorem form_neg_right {n : ℕ} (v a : Fin n ⊕ Fin n → F) : form v (-a) = -form v a := by
  simp [form, Matrix.mulVec_neg]

section Eigen

variable {n : ℕ} {x : StatedSp n F}

theorem mulVec_eig (hx : x * x = 1) {ε : F} (hε : ε * ε = 1) (t : Fin n ⊕ Fin n → F) :
    mat n F x *ᵥ (t + ε • (mat n F x *ᵥ t)) = ε • (t + ε • (mat n F x *ᵥ t)) := by
  have h1 : mat n F x *ᵥ (mat n F x *ᵥ t) = t := by
    rw [Matrix.mulVec_mulVec, ← map_mul, hx, map_one, Matrix.one_mulVec]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, h1, smul_add, smul_smul, hε, one_smul, add_comm]

theorem eig_ne_zero {ε : F} (hε : ε * ε = 1) {t : Fin n ⊕ Fin n → F}
    (ht : mat n F x *ᵥ t ≠ -(ε • t)) : t + ε • (mat n F x *ᵥ t) ≠ 0 := by
  intro h
  apply ht
  have h2 : ε • (t + ε • (mat n F x *ᵥ t)) = 0 := by rw [h, smul_zero]
  rw [smul_add, smul_smul, hε, one_smul] at h2
  exact eq_neg_of_add_eq_zero_right h2

end Eigen

section Pairs

variable {x : StatedSp 2 F}

theorem exists_eig_pair (h2 : (2 : F) ≠ 0) (hx : x * x = 1) {ε : F} (hε : ε * ε = 1)
    (ht : ∃ t, mat 2 F x *ᵥ t ≠ -(ε • t)) :
    ∃ u w, mat 2 F x *ᵥ u = ε • u ∧ mat 2 F x *ᵥ w = ε • w ∧ form u w = 1 := by
  obtain ⟨t, ht⟩ := ht
  have hu1 := mulVec_eig hx hε t
  have hu0 := eig_ne_zero (x := x) hε ht
  obtain ⟨w₀, hw₀⟩ := exists_form_eq_one hu0
  have hXX : mat 2 F x *ᵥ (mat 2 F x *ᵥ w₀) = w₀ := by
    rw [Matrix.mulVec_mulVec, ← map_mul, hx, map_one, Matrix.one_mulVec]
  refine ⟨_, (2 : F)⁻¹ • (w₀ + ε • (mat 2 F x *ᵥ w₀)), hu1, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, mulVec_eig hx hε w₀, smul_comm]
  · have hc : form (t + ε • (mat 2 F x *ᵥ t)) (mat 2 F x *ᵥ w₀) = ε := by
      calc form (t + ε • (mat 2 F x *ᵥ t)) (mat 2 F x *ᵥ w₀)
          = form (mat 2 F x *ᵥ (t + ε • (mat 2 F x *ᵥ t))) (mat 2 F x *ᵥ (mat 2 F x *ᵥ w₀)) :=
            (form_mulVec x _ _).symm
        _ = ε := by rw [hu1, hXX, form_smul_left, hw₀, mul_one]
    rw [form_smul_right, form_add_right, form_smul_right, hw₀, hc]
    have : (2 : F)⁻¹ * (1 + ε * ε) = 1 := by
      rw [hε]
      norm_num [h2]
    simpa using this

theorem form_eq_zero_of_eig (h2 : (2 : F) ≠ 0) {u w : Fin 2 ⊕ Fin 2 → F}
    (hu : mat 2 F x *ᵥ u = u) (hw : mat 2 F x *ᵥ w = -w) : form u w = 0 := by
  have h := form_mulVec x u w
  rw [hu, hw] at h
  have h' : (2 : F) * form u w = 0 := by
    rw [form_neg_right] at h
    linear_combination -h
  exact (mul_eq_zero.mp h').resolve_left h2

end Pairs

section NormalForm

theorem matrix_ext_mulVec_single {ι : Type*} [Fintype ι] [DecidableEq ι] {M N : Matrix ι ι F}
    (h : ∀ j, M *ᵥ Pi.single j 1 = N *ᵥ Pi.single j 1) : M = N :=
  Matrix.ext fun r c => by
    rw [← mulVec_single_one_apply M c r, ← mulVec_single_one_apply N c r, h c]

theorem mulVec_conj_basis {n : ℕ} (g y : StatedSp n F) (j : Fin n ⊕ Fin n)
    {v : Fin n ⊕ Fin n → F} (ε : F) (hg : mat n F g *ᵥ Pi.single j 1 = v)
    (hv : mat n F y *ᵥ v = ε • v) :
    mat n F (g⁻¹ * y * g) *ᵥ Pi.single j 1 = ε • Pi.single j 1 := by
  have hj : Pi.single j (1 : F) = mat n F g⁻¹ *ᵥ v := (mulVec_eq_iff g _ _).1 hg
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hv,
    Matrix.mulVec_smul, ← hj]

theorem exists_conj_longInv (h2 : (2 : F) ≠ 0) {x : StatedSp 2 F} (hx : x * x = 1) (h1 : x ≠ 1)
    (hn : x ≠ negOne) : ∃ g : StatedSp 2 F, g⁻¹ * x * g = longInv F 2 0 := by
  have hm : ∃ t, mat 2 F x *ᵥ t ≠ -((-1 : F) • t) := by
    by_contra hcon
    push Not at hcon
    apply h1
    refine mat_injective ?_
    rw [map_one]
    ext r c
    have := congrFun (hcon (Pi.single c 1)) r
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply, Matrix.one_apply] using this
  have hp : ∃ t, mat 2 F x *ᵥ t ≠ -((1 : F) • t) := by
    by_contra hcon
    push Not at hcon
    apply hn
    refine mat_injective ?_
    rw [mat_negOne]
    ext r c
    have := congrFun (hcon (Pi.single c 1)) r
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply, Matrix.one_apply] using this
  obtain ⟨u₁, w₁, hu₁, hw₁, h₁⟩ := exists_eig_pair h2 hx (ε := -1) (by norm_num) hm
  obtain ⟨u₂, w₂, hu₂, hw₂, h₂⟩ := exists_eig_pair h2 hx (ε := 1) (by norm_num) hp
  simp only [neg_smul, one_smul] at hu₁ hw₁ hu₂ hw₂
  have o₁ : form u₁ u₂ = 0 := by
    rw [form_antisymm, form_eq_zero_of_eig h2 hu₂ hu₁, neg_zero]
  have o₂ : form u₁ w₂ = 0 := by
    rw [form_antisymm, form_eq_zero_of_eig h2 hw₂ hu₁, neg_zero]
  have o₃ : form w₁ u₂ = 0 := by
    rw [form_antisymm, form_eq_zero_of_eig h2 hu₂ hw₁, neg_zero]
  have o₄ : form w₁ w₂ = 0 := by
    rw [form_antisymm, form_eq_zero_of_eig h2 hw₂ hw₁, neg_zero]
  obtain ⟨g, g1, g2, g3, g4⟩ := exists_sp_apply_eq_two (m := 0) u₁ w₁ u₂ w₂ h₁ h₂ o₁ o₂ o₃ o₄
  refine ⟨g, mat_injective (matrix_ext_mulVec_single fun j => ?_)⟩
  have hN : ∀ j : Fin 2 ⊕ Fin 2, mat 2 F (longInv F 2 0) *ᵥ Pi.single j 1 =
      (if j ∈ coords (0 : Fin 2) then (-1 : F) else 1) • Pi.single j 1 := by
    intro j
    rw [mat_longInv, mulVec_diagonal_eq]
    funext t
    by_cases ht : t = j
    · subst ht
      simp
    · simp [ht]
  rw [hN j]
  rcases j with j | j <;> fin_cases j
  · have := mulVec_conj_basis g x (Sum.inl 0) (-1) g1 (by rw [hu₁]; simp)
    simpa [coords] using this
  · have := mulVec_conj_basis g x (Sum.inl 1) 1 g3 (by rw [hu₂]; simp)
    simpa [coords] using this
  · have := mulVec_conj_basis g x (Sum.inr 0) (-1) g2 (by rw [hw₁]; simp)
    simpa [coords] using this
  · have := mulVec_conj_basis g x (Sum.inr 1) 1 g4 (by rw [hw₂]; simp)
    simpa [coords] using this

end NormalForm

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
