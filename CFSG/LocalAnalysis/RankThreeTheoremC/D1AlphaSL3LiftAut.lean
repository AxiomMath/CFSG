module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3OutCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

section Lift

variable {k : Type} [Field k] [Finite k]

private theorem mem_semilinearAutGroup_of_pow_three {α : MulAut (projectiveSL 3 k)}
    (h : α ^ 3 = 1) : α ∈ semilinearAutGroup 3 k := by
  obtain ⟨hR, -⟩ := automorphism_generation (K := k) (n := 3) le_rfl
  obtain ⟨-, -, -, hEnorm, -, -, -, hindex, -, -⟩ :=
    standard_outer_quotients (n := 3) (K := k)
  rw [hR] at hEnorm hindex
  have hEn : (semilinearAutGroup 3 k).Normal :=
    ⟨fun d hd g => hEnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨g, Subgroup.mem_top g⟩⟩
  have hindex' : (semilinearAutGroup 3 k).index ≤ 2 := by
    rwa [← Subgroup.relIndex_top_right]
  have hcop : Nat.Coprime 3 (semilinearAutGroup 3 k).index := by
    have hpos : (semilinearAutGroup 3 k).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : (semilinearAutGroup 3 k).index = 1 ∨
        (semilinearAutGroup 3 k).index = 2) with hi | hi <;> rw [hi]
    · exact Nat.coprime_one_right _
    · norm_num
  exact mem_of_pow_mem_of_coprime_index hcop (by rw [h]; exact one_mem _)

omit [Finite k] in
private theorem exists_pow_three_eq (A : GL (Fin 3) k) (σ : k ≃+* k) :
    ∃ B : GL (Fin 3) k,
      (conjAut 3 k A * fieldAut 3 k σ) ^ 3 = conjAut 3 k B * fieldAut 3 k (σ ^ 3) := by
  refine ⟨A * GeneralLinearGroup.map (σ : k →+* k)
    (A * GeneralLinearGroup.map (σ : k →+* k) A), ?_⟩
  rw [pow_three, conjAut_mul_fieldAut_mul A A σ σ, conjAut_mul_fieldAut_mul A _ σ (σ * σ),
    ← pow_three]

end Lift

theorem exists_conj_of_pow_three_eq_one {k : Type} [Field k] [Finite k]
    (hσ : ∀ σ : k ≃+* k, σ ^ 3 = 1 → σ = 1)
    (θ : MulAut (SpecialLinearGroup (Fin 3) k)) (hθ : θ ^ 3 = 1) :
    ∃ g : GL (Fin 3) k, ∀ s : SpecialLinearGroup (Fin 3) k,
      ((θ s : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
          ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  have hα : descendAut 3 k θ ^ 3 = 1 := by rw [← map_pow, hθ, map_one]
  obtain ⟨A, τ, hAτ⟩ := mem_semilinearAutGroup_iff.1 (mem_semilinearAutGroup_of_pow_three hα)
  obtain ⟨B, hB⟩ := exists_pow_three_eq A τ
  rw [hAτ, hB] at hα
  have hτ : τ = 1 :=
    hσ τ (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) B (τ ^ 3) hα).1
  have hθA : θ = CatalogueBHigherLinearAction.slConjugation 3 k A := by
    refine CFSG.RankThree.PartOne.AUTSL.descendAut_injective (n := 3) (K := k) le_rfl ?_
    rw [hAτ, hτ, map_one, mul_one]
    rfl
  exact ⟨A, fun s => by rw [hθA]; exact CatalogueBHigherLinearAction.slConjugation_matrix 3 k A s⟩

theorem no_ringAut_order_three {p e : ℕ} [Fact p.Prime] {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = p ^ e) (he : ¬ 3 ∣ e) : ∀ σ : k ≃+* k, σ ^ 3 = 1 → σ = 1 := by
  intro σ hσ
  have he1 : 1 ≤ e := Nat.pos_of_ne_zero (by rintro rfl; exact he (dvd_zero 3))
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (Fact.out : p.Prime) he1 hk
  have h3 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ
  have he' : orderOf σ ∣ e := hcard ▸ orderOf_dvd_natCard σ
  have hcop : Nat.Coprime 3 e := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 he
  have h1 : orderOf σ = 1 := Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 he')
  exact orderOf_eq_one_iff.1 h1

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
