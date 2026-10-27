module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LInner

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K] {N : Matrix (Fin n) (Fin n) K}

theorem exists_rank_one (hN : N * N = 0) (hN0 : N ≠ 0)
    (hrk : ∀ f₁ f₂ : Fin n → K, ¬ LinearIndependent K ![N *ᵥ f₁, N *ᵥ f₂]) :
    ∃ (f₀ φ₀ : Fin n → K), N *ᵥ f₀ ≠ 0 ∧ N = vecMulVec (N *ᵥ f₀) φ₀ ∧
      φ₀ ⬝ᵥ (N *ᵥ f₀) = 0 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hN0 (Matrix.ext hc)
  set y := N *ᵥ Pi.single j 1 with hy
  have hy0 : y ≠ 0 := by
    intro h
    have := congrFun h i
    rw [hy, mulVec_single_one] at this
    exact hij this
  have hc : ∀ z, ∃ c : K, N *ᵥ z = c • y := by
    intro z
    have h := hrk z (Pi.single j 1)
    rw [LinearIndependent.pair_iff] at h
    push Not at h
    obtain ⟨s, t, hst, hne⟩ := h
    by_cases hs : s = 0
    · rw [hs, zero_smul, zero_add, smul_eq_zero] at hst
      exact absurd (hst.resolve_right hy0) (hne hs)
    · refine ⟨-(s⁻¹ * t), ?_⟩
      have h1 : s • (N *ᵥ z) = -(t • y) := eq_neg_of_add_eq_zero_left hst
      calc N *ᵥ z = s⁻¹ • (s • (N *ᵥ z)) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = -(s⁻¹ * t) • y := by rw [h1, smul_neg, smul_smul, neg_smul]
  choose φ₀ hφ₀ using fun k : Fin n => hc (Pi.single k 1)
  have hNy : N = vecMulVec y φ₀ := by
    ext a k
    rw [vecMulVec_apply, mul_comm]
    have := congrFun (hφ₀ k) a
    rw [mulVec_single_one, Pi.smul_apply, smul_eq_mul] at this
    exact this
  refine ⟨Pi.single j 1, φ₀, hy0, hNy, ?_⟩
  have h0 : N *ᵥ y = 0 := by rw [hy, mulVec_mulVec, hN, zero_mulVec]
  conv_lhs at h0 => rw [hNy]
  rw [vecMulVec_mulVec, op_smul_eq_smul, smul_eq_zero] at h0
  exact h0.resolve_right hy0

theorem exists_pair_ker (hn : 4 ≤ n) (φ ρ : Fin n → K) :
    ∃ x₁ x₂ : Fin n → K, φ ⬝ᵥ x₁ = 0 ∧ ρ ⬝ᵥ x₁ = 0 ∧ φ ⬝ᵥ x₂ = 0 ∧ ρ ⬝ᵥ x₂ = 0 ∧
      LinearIndependent K ![x₁, x₂] := by
  set W := LinearMap.ker (Matrix.of ![φ, ρ]).mulVecLin with hW
  have hmem : ∀ x : Fin n → K, x ∈ W ↔ φ ⬝ᵥ x = 0 ∧ ρ ⬝ᵥ x = 0 := by
    intro x
    rw [hW, LinearMap.mem_ker, mulVecLin_apply]
    constructor
    · intro h
      exact ⟨by simpa [mulVec, Matrix.of_apply] using congrFun h 0,
        by simpa [mulVec, Matrix.of_apply] using congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      ext i
      fin_cases i <;> simpa [mulVec, Matrix.of_apply]
  have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.of ![φ, ρ]).mulVecLin
  have hle : Module.finrank K (LinearMap.range (Matrix.of ![φ, ρ]).mulVecLin) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range (Matrix.of ![φ, ρ]).mulVecLin)
    simpa using this
  rw [Module.finrank_fin_fun, ← hW] at hrk
  have hW2 : 1 < Module.finrank K W := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank K W)
  obtain ⟨x', hxx'⟩ := exists_linearIndependent_pair_of_one_lt_finrank hW2 hx
  have hp := LinearIndependent.pair_iff.mp hxx'
  refine ⟨x, x', ((hmem x).mp x.2).1, ((hmem x).mp x.2).2, ((hmem x').mp x'.2).1,
    ((hmem x').mp x'.2).2, LinearIndependent.pair_iff.mpr fun s t hst => hp s t ?_⟩
  exact Subtype.ext (by simpa using hst)

theorem exists_dual_pair {x₁ x₂ y ρ : Fin n → K} (hρ1 : ρ ⬝ᵥ x₁ = 0) (hρ2 : ρ ⬝ᵥ x₂ = 0)
    (hρy : ρ ⬝ᵥ y = 1) (hp : ∀ s t : K, s • x₁ + t • x₂ = 0 → s = 0 ∧ t = 0) :
    ∃ χ : Fin n → K, χ ⬝ᵥ x₁ = 1 ∧ χ ⬝ᵥ x₂ = 0 ∧ χ ⬝ᵥ y = 0 := by
  have hx : x₁ ∉ Submodule.span K {x₂, y} := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
    have hb : b = 0 := by
      have := congrArg (ρ ⬝ᵥ ·) hab
      simp only [dotProduct_add, dotProduct_smul, hρ1, hρ2, hρy, smul_eq_mul, mul_zero,
        mul_one, zero_add] at this
      exact this
    rw [hb, zero_smul, add_zero] at hab
    have := hp 1 (-a) (by rw [← hab, one_smul, neg_smul, add_neg_cancel])
    exact one_ne_zero this.1
  obtain ⟨χ, h1, hW⟩ := exists_dotProduct_of_notMem hx
  exact ⟨χ, h1, hW _ (Submodule.subset_span (by simp)), hW _ (Submodule.subset_span (by simp))⟩

theorem hasWit_of_rank_one (h2 : (2 : K) = 0) (hn : 4 ≤ n) {A : GL (Fin n) K} {μ : K}
    (hNA : N = (A : Matrix (Fin n) (Fin n) K) + μ • 1) {f₀ φ₀ : Fin n → K}
    (hy0 : N *ᵥ f₀ ≠ 0) (hNy : N = vecMulVec (N *ᵥ f₀) φ₀) (hφy : φ₀ ⬝ᵥ (N *ᵥ f₀) = 0) :
    HasWit (conjAut n K A) := by
  obtain ⟨y, hy⟩ : ∃ y, y = N *ᵥ f₀ := ⟨_, rfl⟩
  rw [← hy] at hy0 hφy
  have hNy' : N = vecMulVec y φ₀ := by rw [hy]; exact hNy
  obtain ⟨ρ, hρy, -⟩ := exists_dotProduct_of_notMem (W := ⊥) (v := y)
    (by rwa [Submodule.mem_bot])
  obtain ⟨x₁, x₂, hφ1, hρ1, hφ2, hρ2, hind⟩ := exists_pair_ker hn φ₀ ρ
  have hp := LinearIndependent.pair_iff.mp hind
  obtain ⟨χ₁, h11, h12, h1y⟩ := exists_dual_pair hρ1 hρ2 hρy hp
  obtain ⟨χ₂, h22, h21, h2y⟩ := exists_dual_pair hρ2 hρ1 hρy
    (fun s t h => (hp t s (by rw [add_comm]; exact h)).symm)
  have hNx : ∀ x, φ₀ ⬝ᵥ x = 0 → N *ᵥ x = 0 := fun x hx => by
    rw [hNy', vecMulVec_mulVec, hx, MulOpposite.op_zero, zero_smul]
  have hχN : ∀ χ, χ ⬝ᵥ y = 0 → χ ᵥ* N = 0 := fun χ hχ => by
    rw [hNy', vecMul_vecMulVec, hχ, zero_smul]
  have hcommU : ∀ {x χ : Fin n → K}, φ₀ ⬝ᵥ x = 0 → χ ⬝ᵥ y = 0 →
      N * vecMulVec x χ = vecMulVec x χ * N := fun hx hχ => by
    rw [mul_vecMulVec, vecMulVec_mul, hNx _ hx, hχN _ hχ, zero_vecMulVec, vecMulVec_zero]
  set a := vecMulVec x₁ χ₂ with ha
  set b := vecMulVec x₂ χ₁ with hb
  have haa : a * a = 0 := by rw [ha, vecMulVec_mul_vecMulVec, h21, zero_smul, vecMulVec_zero]
  have hbb : b * b = 0 := by rw [hb, vecMulVec_mul_vecMulVec, h12, zero_smul, vecMulVec_zero]
  have hab : a * b = vecMulVec x₁ χ₁ := by rw [ha, hb, vecMulVec_mul_vecMulVec, h22, one_smul]
  have hba : b * a = vecMulVec x₂ χ₂ := by rw [ha, hb, vecMulVec_mul_vecMulVec, h11, one_smul]
  have haba : a * b * a = a := by rw [hab, ha, vecMulVec_mul_vecMulVec, h11, one_smul]
  have hbab : b * a * b = b := by rw [hba, hb, vecMulVec_mul_vecMulVec, h22, one_smul]
  set h := unipOf h2 a haa * unipOf h2 b hbb with hh
  have hH : (h : Matrix (Fin n) (Fin n) K) = (1 + a) * (1 + b) := by
    rw [hh, Matrix.SpecialLinearGroup.coe_mul, coe_unipOf, coe_unipOf]
  have h3 : h ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hH,
      pow_three_of_rel (add_self_eq_zero_of_two h2) haa hbb haba hbab]
    rfl
  have hcomm : (h : Matrix (Fin n) (Fin n) K) * N = N * h := by
    rw [hH, mul_assoc, ← one_add_comm (hcommU hφ2 h1y), ← mul_assoc,
      ← one_add_comm (hcommU hφ1 h2y), mul_assoc]
  have hψN : χ₁ ᵥ* N = 0 := hχN χ₁ h1y
  set E := vecMulVec (N *ᵥ f₀) χ₁ with hE
  have hEy : E = vecMulVec y χ₁ := by rw [hE, hy]
  have hEE : E * E = 0 := by
    rw [hEy, vecMulVec_mul_vecMulVec, h1y, zero_smul, vecMulVec_zero]
  have hEcomm : (1 + E) * N = N * (1 + E) := by
    rw [mul_add, add_mul, mul_one, one_mul, hEy, vecMulVec_mul, hψN, vecMulVec_zero,
      mul_vecMulVec, hNx y hφy, zero_vecMulVec]
  have hNA' : ∀ g : SpecialLinearGroup (Fin n) K, (g : Matrix (Fin n) (Fin n) K) * N = N * g →
      conjAut n K A (proj n K g) = proj n K g := fun g hg =>
    conjAut_proj_eq_of_comm (by rw [← hNA]; exact hg)
  have hmv : ∀ (x : Fin n → K) (χ v : Fin n → K), vecMulVec x χ *ᵥ v = (χ ⬝ᵥ v) • x :=
    fun x χ v => by rw [vecMulVec_mulVec, op_smul_eq_smul]
  have hby : (1 + b) *ᵥ y = y := by
    rw [add_mulVec, one_mulVec, hb, hmv, h1y, zero_smul, add_zero]
  have hay : (1 + a) *ᵥ y = y := by
    rw [add_mulVec, one_mulVec, ha, hmv, h2y, zero_smul, add_zero]
  have hHy : (h : Matrix (Fin n) (Fin n) K) *ᵥ y = y := by
    rw [hH, ← mulVec_mulVec, hby, hay]
  have hbx : (1 + b) *ᵥ x₁ = x₁ + x₂ := by
    rw [add_mulVec, one_mulVec, hb, hmv, h11, one_smul]
  have hax : (1 + a) *ᵥ (x₁ + x₂) = x₂ := by
    rw [add_mulVec, one_mulVec, ha, hmv, dotProduct_add, h21, h22, zero_add, one_smul,
      show x₁ + x₂ + x₁ = x₂ + (x₁ + x₁) by abel, vec_add_self h2, add_zero]
  have hHx : (h : Matrix (Fin n) (Fin n) K) *ᵥ x₁ = x₂ := by
    rw [hH, ← mulVec_mulVec, hbx, hax]
  have hne : (h : Matrix (Fin n) (Fin n) K) * E ≠ E * h := by
    intro heq
    have := congrArg (· *ᵥ x₁) heq
    simp only [← mulVec_mulVec, hEy, hmv, h11, one_smul, hHy, hHx, h12, zero_smul] at this
    exact hy0 this
  refine hasWit_of_sl h2 h (m := 3) ⟨1, rfl⟩ h3 hEE
    (vecMulVec_mul_mul_eq_zero hcomm hψN) (vecMulVec_mul_mul_eq_zero (inv_comm_of_comm hcomm) hψN)
    hne (hNA' h hcomm) (hNA' _ ?_)
  rw [coe_unipOf]
  exact hEcomm

end CFSG.ComponentClassification.HarrisLit.L33.C2
