module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL5Graph
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87BadSL3
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem isSimpleGroup_projectiveSL3 (F : Type) [Field F] : IsSimpleGroup (projectiveSL 3 F) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega) (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup

theorem isPerfect_projectiveSL3 (F : Type) [Field F] : Group.IsPerfect (projectiveSL 3 F) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (scalars 3 F))

theorem linear5_involution_cases {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (hfodd : Odd f) (hK2 : ringChar F ≠ 2)
    (α : MulAut (projectiveSL 5 F)) (hα : α ^ 2 = 1) :
    (∃ ρ : SpecialLinearGroup (Fin 3) F →* projectiveSL 5 F, Function.Injective ρ ∧ ∀ g, α (ρ g) = ρ g) ∨
    ((∀ x : projectiveSL 5 F, α ≠ MulAut.conj x) ∧
      ∃ E : Subgroup (projectiveSL 5 F), (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) ∧ (∀ e ∈ E, e * e = 1) ∧
        2 ^ 4 ≤ Nat.card ↥E ∧ ∀ e ∈ E, α e = e) := by
  classical
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := 5) (by norm_num)).2 α
  rw [hαeq] at hα ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 5 F), mul_one] at hα ⊢
      obtain ⟨ρ, hρ, hfix⟩ := exists_fixed_sl3_block hK2 A hα
      exact Or.inl ⟨ρ, hρ, hfix⟩
    · exact absurd hfodd (Nat.not_odd_iff_even.2
        (linear_field_involution_descent hp hf hcard (by norm_num) A σ hσ hα).1)
  · rw [pow_one] at hα ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 5 F), mul_one] at hα ⊢
      rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hα with hA | hA
      · refine Or.inr ⟨?_, exists_elemAbelian_fixed_graph hK2 A hA⟩
        intro x hx
        obtain ⟨g, rfl⟩ : ∃ g : SpecialLinearGroup (Fin 5) F, proj 5 F g = x := QuotientGroup.mk_surjective x
        have h1 : conjAut 5 F A * dualAut 5 F = conjAut 5 F (SpecialLinearGroup.toGL g) := by
          rw [hx, conjAut_toGL]
        have h2 : dualAut 5 F = conjAut 5 F (A⁻¹ * SpecialLinearGroup.toGL g) := by
          rw [map_mul, map_inv, ← h1]
          group
        exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.dualAut_not_mem_semilinearAutGroup
          (n := 5) (K := F) (by norm_num)
          (h2 ▸ linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
      · exfalso
        have hdet := congrArg Matrix.det hA
        rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hdet
        have hu : IsUnit (A : Matrix (Fin 5) (Fin 5) F).det := Matrix.isUnits_det_units A
        have h2 : (2 : F) * (A : Matrix (Fin 5) (Fin 5) F).det = 0 := by
          have : (A : Matrix (Fin 5) (Fin 5) F).det = -(A : Matrix (Fin 5) (Fin 5) F).det := by
            have h5 : ((-1 : F) ^ 5) = -1 := by norm_num
            rw [h5] at hdet
            simpa using hdet
          linear_combination this
        rcases mul_eq_zero.1 h2 with h | h
        · exact Ring.two_ne_zero hK2 h
        · exact hu.ne_zero h
    · exact absurd hfodd (Nat.not_odd_iff_even.2
        (odd_linear_graph_field_involution_conjugacy hp hf hcard (by norm_num) A σ hσ hα).1)

theorem cell87_FL5 : Cell87 FL5 := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hF
  exfalso
  have hd := CellData.of_ctx hctx hsig hyp
  obtain ⟨p0, f, hp0, hf, hq4, hL⟩ := hF
  obtain ⟨F, hFfield, hFfin, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have := Nat.even_iff.mp this
    omega
  have hfodd : Odd f := by
    by_contra hnot
    obtain ⟨m, rfl⟩ := Nat.not_odd_iff_even.mp hnot
    have hsq : p0 ^ (m + m) = (p0 ^ m) ^ 2 := by ring
    rw [hsq] at hq4
    have h4 : ∀ a : ℕ, a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
      intro a
      have := Nat.mod_lt a (by norm_num : 4 > 0)
      interval_cases h : a % 4 <;> simp [Nat.pow_mod, h]
    rcases h4 (p0 ^ m) with h | h <;> omega
  have : Fact p0.Prime := ⟨hp0⟩
  have : CharP F p0 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hK2 : ringChar F ≠ 2 := by rwa [ringChar.eq F p0]
  have hFodd : Odd (Nat.card F) := by rw [hcard, Nat.odd_iff]; omega
  have h3 : 3 ≤ Nat.card F := by rw [hcard]; omega
  obtain ⟨π, α, hπ, hker, hcomm, hαα⟩ :=
    exists_induced (layerAut (zSec z H₀ hz H₁)) (layerAut_layerAut hd.z2) e
  have hα2 : α ^ 2 = 1 := by
    ext s
    rw [sq, MulAut.mul_apply]
    exact hαα s
  rcases linear5_involution_cases hp0 hf hcard hfodd hK2 α hα2 with
    ⟨ρ, hρ, hfix⟩ | ⟨hnotinn, E, hEc, hE2, hEcard, hEfix⟩
  ·
    have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    let c : ↥ρ.range →* projectiveSL 3 F :=
      (QuotientGroup.mk' (scalars 3 F)).comp (MonoidHom.ofInjective hρ).symm.toMonoidHom
    have hc : Function.Surjective c :=
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.ofInjective hρ).symm.surjective
    have hQ : ∀ s ∈ ρ.range, α s = s := by
      rintro _ ⟨g, rfl⟩
      exact hfix g
    have hCS := centSection_of_fixed_perfect hπ hker.le hcomm ρ.range hQ c hc
    have := isSimpleGroup_projectiveSL3 F
    have := isPerfect_projectiveSL3 F
    have : Nontrivial (projectiveSL 3 F) := IsSimpleGroup.toNontrivial
    have hns : ¬ Group.IsSolvable (projectiveSL 3 F) := Group.IsPerfect.not_isSolvable _
    have hKF := kindFactor_of_section_sec hctx hsig hns hCS.isSection
    exact not_kindFactor hp02 (involved_qdSL_projectiveSL3 (p := p0))
      (not_card_dvd_factorial_projectiveSL3 hFodd h3) hKF
  ·
    have hzK : zSec z H₀ hz H₁ ∉ layer (Sec H₀ H₁) := by
      intro hzb
      apply hnotinn (π ⟨zSec z H₀ hz H₁, hzb⟩)
      ext s
      obtain ⟨x, rfl⟩ := hπ s
      rw [← hcomm, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [coe_layerAut]
      simp
    exact gen4_kill (gen4_sec hctx.std.gen4 H₀ H₁) hd.z2 hzK hπ hker hcomm E hEc hE2 hEcard hEfix

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
