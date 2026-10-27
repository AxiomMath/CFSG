module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Field

theorem isSimpleGroup_projectiveSL3_fl3 (F : Type) [Field F] : IsSimpleGroup (projectiveSL 3 F) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by omega) (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup

theorem isPerfect_projectiveSL3_fl3 (F : Type) [Field F] : Group.IsPerfect (projectiveSL 3 F) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (scalars 3 F))

theorem exists_subfield_embedding (F : Type) [Field F] (σ : F ≃+* F) :
    ∃ (F0 : Subfield F) (ρ : projectiveSL 3 ↥F0 →* projectiveSL 3 F), Function.Injective ρ ∧
      ∀ x, fieldAut 3 F σ (ρ x) = ρ x := by
  set F0 : Subfield F := (σ : F →+* F).eqLocusField (RingHom.id F) with hF0
  have hmem : ∀ x : F, x ∈ F0 → σ x = x := fun x hx => hx
  let ρ0 : SpecialLinearGroup (Fin 3) ↥F0 →* projectiveSL 3 F :=
    (proj 3 F).comp (SpecialLinearGroup.map F0.subtype)
  have hker : scalars 3 ↥F0 ≤ ρ0.ker := by
    intro s hs
    obtain ⟨c, hc3, hcm⟩ := mem_scalars.1 hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff]
    refine mem_scalars.2 ⟨Units.map F0.subtype.toMonoidHom c, ?_, ?_⟩
    · rw [← map_pow, hc3, map_one]
    · ext i j
      have := congrFun (congrFun hcm i) j
      rw [SpecialLinearGroup.map_apply_coe]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [this]
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, hij]
  let ρ1 : projectiveSL 3 ↥F0 →* projectiveSL 3 F := QuotientGroup.lift (scalars 3 ↥F0) ρ0 hker
  have hρ1 : ∀ g, ρ1 (proj 3 ↥F0 g) = proj 3 F (SpecialLinearGroup.map F0.subtype g) := fun g => rfl
  refine ⟨F0, ρ1, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective 3 ↥F0 x
    rw [hρ1, proj_eq_one_iff] at hx
    obtain ⟨c, hc3, hcm⟩ := mem_scalars.1 hx
    rw [proj_eq_one_iff]
    have hentry : ∀ i j, F0.subtype ((g : Matrix (Fin 3) (Fin 3) ↥F0) i j) =
        (scalar (Fin 3) (c : F)) i j := by
      intro i j
      have := congrFun (congrFun hcm i) j
      rw [SpecialLinearGroup.map_apply_coe] at this
      simpa using this
    have ha : F0.subtype ((g : Matrix (Fin 3) (Fin 3) ↥F0) 0 0) = (c : F) := by
      simpa using hentry 0 0
    have ha0 : (g : Matrix (Fin 3) (Fin 3) ↥F0) 0 0 ≠ 0 := by
      intro h
      rw [h, map_zero] at ha
      exact c.ne_zero ha.symm
    refine mem_scalars.2 ⟨Units.mk0 _ ha0, ?_, ?_⟩
    · apply Units.ext
      apply F0.subtype.injective
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, ha]
      have := congrArg Units.val hc3
      simpa using this
    · ext i j
      change F0.subtype ((g : Matrix (Fin 3) (Fin 3) ↥F0) i j) =
        F0.subtype ((scalar (Fin 3) ((Units.mk0 _ ha0 : (↥F0)ˣ) : ↥F0)) i j)
      rw [hentry i j]
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply, ha]
      · simp [Matrix.scalar_apply, hij]
  · intro x
    obtain ⟨g, rfl⟩ := proj_surjective 3 ↥F0 x
    rw [hρ1, fieldAut_proj]
    congr 1
    ext i j
    exact hmem _ (g i j).2

theorem fl3_field_section {F : Type} [Field F] [Finite F] {p0 f : ℕ} (hp0 : p0.Prime) (hp02 : p0 ≠ 2)
    (hf : 1 ≤ f) (hcard : Nat.card F = p0 ^ f) (α : MulAut (projectiveSL 3 F)) (hα : α * α = 1)
    (A : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1) (hαeq : α = conjAut 3 F A * fieldAut 3 F σ) :
    ∃ (F0 : Type) (_ : Field F0) (_ : Finite F0) (_ : CharP F0 p0), Odd (Nat.card F0) ∧
      3 ≤ Nat.card F0 ∧ ∃ Q : Subgroup (projectiveSL 3 F), Group.IsPerfect Q ∧
        (∀ s ∈ Q, α s = s) ∧ ∃ c : ↥Q →* projectiveSL 3 F0, Function.Surjective c := by
  classical
  have : Fact p0.Prime := ⟨hp0⟩
  have hsq : (conjAut 3 F A * fieldAut 3 F σ) ^ 2 = 1 := by rw [← hαeq, sq]; exact hα
  obtain ⟨-, -, H, hH⟩ := linear_field_involution_descent hp0 hf hcard (le_refl 3) A σ hσ hsq
  obtain ⟨F0, ρ, hρ, hfix⟩ := exists_subfield_embedding F σ
  have : CharP F p0 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have : CharP ↥F0 p0 := inferInstance
  have hF0card : ∃ n : ℕ+, Nat.card ↥F0 = p0 ^ (n : ℕ) := by
    have := Fintype.ofFinite ↥F0
    obtain ⟨n, -, hn⟩ := FiniteField.card ↥F0 p0
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨n, hn⟩ := hF0card
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  refine ⟨↥F0, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · rw [hn]
    exact (hp0.odd_of_ne_two hp02).pow
  · rw [hn]
    calc 3 ≤ p0 := by have := hp0.two_le; omega
      _ ≤ p0 ^ (n : ℕ) := Nat.le_self_pow (by omega) p0
  · let γ : projectiveSL 3 F ≃* projectiveSL 3 F := conjAut 3 F H
    have := isPerfect_projectiveSL3_fl3 ↥F0
    have hperf0 : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    refine ⟨ρ.range.map γ.toMonoidHom, Group.IsPerfect.map γ.toMonoidHom, ?_, ?_⟩
    · rintro _ ⟨q, ⟨x, rfl⟩, rfl⟩
      rw [hαeq, hH, MulAut.mul_apply, MulAut.mul_apply]
      change γ (fieldAut 3 F σ (γ.symm (γ (ρ x)))) = γ (ρ x)
      rw [MulEquiv.symm_apply_apply, hfix x]
    · let e2 : projectiveSL 3 ↥F0 ≃* ↥ρ.range := MonoidHom.ofInjective hρ
      let e1 : ↥ρ.range ≃* ↥(ρ.range.map γ.toMonoidHom) :=
        ρ.range.equivMapOfInjective γ.toMonoidHom γ.injective
      exact ⟨(e2.trans e1).symm.toMonoidHom, (e2.trans e1).symm.surjective⟩

end Field

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
