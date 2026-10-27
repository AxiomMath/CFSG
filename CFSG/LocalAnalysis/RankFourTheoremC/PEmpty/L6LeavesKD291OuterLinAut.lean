module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterTorus
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterDiag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinearLang
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)

theorem linear_outer_form {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (α : MulAut (projectiveSL n K)) (hα : α ^ p = 1)
    (hnot : ¬ ∃ B : GL (Fin n) K, conjAut n K B = α) :
    ∃ (H : GL (Fin n) K) (σ : K ≃+* K), σ ^ p = 1 ∧ σ ≠ 1 ∧
      α = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
  classical
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  have hε0 : ε = 0 := by
    by_contra hne
    have hε1 : ε = 1 := by omega
    subst hε1
    rw [pow_one] at hαeq
    set e : MulAut (projectiveSL n K) := conjAut n K A * fieldAut n K σ with he
    have heE : e ∈ semilinearAutGroup n K := mem_semilinearAutGroup_iff.2 ⟨A, σ, rfl⟩
    have hδe : dualAut n K * e * dualAut n K ∈ semilinearAutGroup n K :=
      dualAut_mul_mul_dualAut_mem heE
    have hsq : α ^ 2 ∈ semilinearAutGroup n K := by
      have h2 : α ^ 2 = e * (dualAut n K * e * dualAut n K) := by
        rw [sq, hαeq]
        simp only [mul_assoc]
      rw [h2]
      exact mul_mem heE hδe
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    have h1 : (α ^ 2) ^ m * α = 1 := by
      rw [← pow_mul, ← pow_succ, show 2 * m + 1 = p by omega]
      exact hα
    have hαE : α ∈ semilinearAutGroup n K := by
      have h3 : α = ((α ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]
      exact inv_mem (pow_mem hsq m)
    apply dualAut_not_mem_semilinearAutGroup hn (K := K)
    have h4 : dualAut n K = e⁻¹ * α := by
      rw [hαeq]
      group
    rw [h4]
    exact mul_mem (inv_mem heE) hαE
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hnot ⟨A, by rw [hαeq, map_one, mul_one]⟩
  have hαp : (conjAut n K A * fieldAut n K σ) ^ p = 1 := by
    rw [← hαeq]
    exact hα
  obtain ⟨hord, H, hH⟩ := CFSG.StandardType.RecipeFieldLang.lang_field_linear (by omega)
    (Or.inl hn) hp A σ hσ1 hαp
  have hσp : σ ^ p = 1 := by
    have h1 : fieldAut n K (σ ^ p) = 1 := by
      rw [map_pow]
      have := pow_orderOf_eq_one (fieldAut n K σ)
      rwa [hord] at this
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 (σ ^ p)
      (by rw [map_one, one_mul]; exact h1)).1
  exact ⟨H, σ, hσp, hσ1, by rw [hαeq, hH]⟩

theorem linear_lift {K : Type} [Field K] {n : ℕ} (H : GL (Fin n) K) (σ : K ≃+* K) :
    ∃ Ã : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K,
      (∀ s, proj n K (Ã s) =
        (conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹) (proj n K s)) ∧
      ∀ g, slFieldAut (Fin n) K σ g = g → Ã (slConjugation n K H g) = slConjugation n K H g := by
  refine ⟨((slConjugation n K H * slFieldAut (Fin n) K σ * (slConjugation n K H)⁻¹ :
    MulAut (SpecialLinearGroup (Fin n) K)) : SpecialLinearGroup (Fin n) K →*
      SpecialLinearGroup (Fin n) K), fun s => ?_, fun g hg => ?_⟩
  · have h : descendAut n K (slConjugation n K H * slFieldAut (Fin n) K σ *
        (slConjugation n K H)⁻¹) = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [← h, descendAut_proj]
    rfl
  · change (slConjugation n K H * slFieldAut (Fin n) K σ * (slConjugation n K H)⁻¹)
      (slConjugation n K H g) = slConjugation n K H g
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply]
    simp [hg]

theorem exists_linear_torus {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime) (hn : 5 ≤ n)
    (hpK : p ∣ Nat.card K - 1) {σ : K ≃+* K} (hσ : σ ^ p = 1) :
    ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* SpecialLinearGroup (Fin n) K,
      Function.Injective ((proj n K).comp F) ∧ ∀ x, slFieldAut (Fin n) K σ (F x) = F x := by
  obtain ⟨κ, hκp, hκdet, hκinj⟩ := exists_diag_torus (K := K) hp hn hpK
  refine ⟨diagSLHom κ hκdet, ?_, fun x => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hx)
    refine hκinj x c fun j => Units.ext ?_
    have h1 := congrFun (congrFun hc j) j
    rw [coe_diagSLHom, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at h1
    exact h1
  · apply Subtype.ext
    ext i j
    change σ ((diagSLHom κ hκdet x : Matrix (Fin n) (Fin n) K) i j) =
      (diagSLHom κ hκdet x : Matrix (Fin n) (Fin n) K) i j
    rw [coe_diagSLHom]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      exact fixed_of_pow_eq_one hp hσ (hκp x i)
    · rw [diagonal_apply_ne _ hij, map_zero]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out
