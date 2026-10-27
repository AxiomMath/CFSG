module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem exists_semilinear_of_odd_pow [Finite F] {β : MulAut (projectiveSL 3 F)} {m : ℕ}
    (hm : Odd m) (hβ : β ^ m = 1) :
    ∃ (A : GL (Fin 3) F) (σ : F ≃+* F), β = conjAut 3 F A * fieldAut 3 F σ := by
  classical
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hβ'⟩ := hform β
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · exact ⟨A, σ, by rw [hβ', pow_zero, mul_one]⟩
  · exfalso
    rw [pow_one] at hβ'
    have htrans := standard_automorphism_transport (K := F) (n := 3)
    have hδδ : dualAut 3 F * dualAut 3 F = 1 := htrans.2.2.2.1
    set δ := dualAut 3 F with hδ
    set e : MulAut (projectiveSL 3 F) := conjAut 3 F A * fieldAut 3 F σ with he
    have heE : e ∈ semilinearAutGroup 3 F := mem_semilinearAutGroup_iff.mpr ⟨A, σ, rfl⟩
    have hδeδ : δ * e * δ ∈ semilinearAutGroup 3 F := by
      have h1 : δ * e * δ = (δ * conjAut 3 F A * δ) * (δ * fieldAut 3 F σ * δ) := by
        rw [he]
        calc δ * (conjAut 3 F A * fieldAut 3 F σ) * δ
            = δ * conjAut 3 F A * (δ * δ) * fieldAut 3 F σ * δ := by rw [hδδ]; group
          _ = _ := by group
      rw [h1, htrans.2.2.2.2.1, htrans.2.2.2.2.2.1]
      exact mem_semilinearAutGroup_iff.mpr ⟨_, σ, rfl⟩
    have hsq : β * β ∈ semilinearAutGroup 3 F := by
      have : β * β = e * (δ * e * δ) := by rw [hβ']; group
      rw [this]
      exact Subgroup.mul_mem _ heE hδeδ
    obtain ⟨k, rfl⟩ := hm
    have hβE : β ∈ semilinearAutGroup 3 F := by
      have h2 : β ^ (2 * k + 1) = β * (β * β) ^ k := by
        rw [pow_succ', pow_mul, pow_two]
      rw [h2] at hβ
      have : β = ((β * β) ^ k)⁻¹ := eq_inv_iff_mul_eq_one.2 hβ
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hsq k)
    have hδE : δ ∈ semilinearAutGroup 3 F := by
      have : δ = e⁻¹ * β := by rw [hβ']; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ heE) hβE
    exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.dualAut_not_mem_semilinearAutGroup
      (by norm_num) hδE

theorem fl3g_commutator_self_of_perfect {G : Type*} [Group G] {Ω : Subgroup G}
    (h : Group.IsPerfect Ω) : ⁅Ω, Ω⁆ = Ω := by
  rw [← Subgroup.map_subtype_commutator, h.commutator_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

@[expose] noncomputable def semiSL (A : GL (Fin 3) F) (σ : F ≃+* F) : SL(3, F) →* SL(3, F) :=
  (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A).toMonoidHom.comp
    (SpecialLinearGroup.map σ.toRingHom)

theorem coe_semiSL (A : GL (Fin 3) F) (σ : F ≃+* F) (g : SL(3, F)) :
    ((semiSL A σ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F).map σ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  change ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
    (SpecialLinearGroup.map σ.toRingHom g) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_slConjugation]
  rfl

theorem beta_proj (A : GL (Fin 3) F) (σ : F ≃+* F) (g : SL(3, F)) :
    (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F g) = proj 3 F (semiSL A σ g) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  rfl

theorem fl3g_commutator_mul_central {G : Type*} [Group G] {a b c d : G} (hc : ∀ x, c * x = x * c)
    (hd : ∀ x, d * x = x * d) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have h1 : c * (b * d) = (b * d) * c := hc _
  have h2 : d * a⁻¹ = a⁻¹ * d := hd _
  calc ⁅a * c, b * d⁆ = a * (c * (b * d)) * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * ((b * d) * c) * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [h1]
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [h2]
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def]; group

theorem semiSL_fix_of_perfect (A : GL (Fin 3) F) (σ : F ≃+* F) {Ω : Subgroup SL(3, F)}
    (hperf : Group.IsPerfect Ω) (hfix : ∀ g ∈ Ω, proj 3 F (semiSL A σ g) = proj 3 F g) :
    ∀ g ∈ Ω, semiSL A σ g = g := by
  have hz : ∀ g ∈ Ω, (g⁻¹ * semiSL A σ g) ∈ scalars 3 F := fun g hg =>
    proj_eq_proj_iff.1 (hfix g hg).symm
  have hcen : ∀ g ∈ Ω, ∀ x : SL(3, F), (g⁻¹ * semiSL A σ g) * x = x * (g⁻¹ * semiSL A σ g) :=
    fun g hg x => (mem_center_iff.1 (scalars_le_center 3 F (hz g hg)) x).symm
  have hle : ⁅Ω, Ω⁆ ≤ (MonoidHom.eqLocus (semiSL A σ) (MonoidHom.id _)) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have ha' : semiSL A σ a = a * (a⁻¹ * semiSL A σ a) := by group
    have hb' : semiSL A σ b = b * (b⁻¹ * semiSL A σ b) := by group
    show semiSL A σ ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, ha', hb']
    exact fl3g_commutator_mul_central (hcen a ha) (hcen b hb)
  intro g hg
  exact hle (by rw [fl3g_commutator_self_of_perfect hperf]; exact hg)

theorem trace_semiSL (A : GL (Fin 3) F) (σ : F ≃+* F) (g : SL(3, F)) :
    Matrix.trace ((semiSL A σ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      σ (Matrix.trace (g : Matrix (Fin 3) (Fin 3) F)) := by
  rw [coe_semiSL, Matrix.trace_mul_cycle]
  have h : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h, Matrix.one_mul]
  simp [Matrix.trace, map_sum]

theorem aut_fixing_trivial' [Finite F] {Ω : Subgroup SL(3, F)}
    (hlift : ∀ (A : GL (Fin 3) F) (σ : F ≃+* F),
      (∀ g ∈ Ω, proj 3 F (semiSL A σ g) = proj 3 F g) → ∀ g ∈ Ω, semiSL A σ g = g)
    (hcomm : ∀ T : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ Ω, T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) →
        ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (htr : ∀ σ : F ≃+* F, (∀ g ∈ Ω, σ (Matrix.trace (g : Matrix (Fin 3) (Fin 3) F)) =
      Matrix.trace (g : Matrix (Fin 3) (Fin 3) F)) → σ = 1)
    {β : MulAut (projectiveSL 3 F)} {m : ℕ} (hm : Odd m) (hβ : β ^ m = 1)
    (hfix : ∀ g ∈ Ω, β (proj 3 F g) = proj 3 F g) : β = 1 := by
  obtain ⟨A, σ, rfl⟩ := exists_semilinear_of_odd_pow hm hβ
  have hf1 : ∀ g ∈ Ω, semiSL A σ g = g :=
    hlift A σ fun g hg => by rw [← beta_proj]; exact hfix g hg
  have hσ : σ = 1 := by
    refine htr σ fun g hg => ?_
    rw [← trace_semiSL A σ g, hf1 g hg]
  subst hσ
  have hAcomm : ∀ g ∈ Ω, (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * A := by
    intro g hg
    have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) (hf1 g hg)
    simp only [coe_semiSL] at h1
    have h2 : (g : Matrix (Fin 3) (Fin 3) F).map ⇑(1 : F ≃+* F) = (g : Matrix (Fin 3) (Fin 3) F) := by
      ext i j; rfl
    rw [h2] at h1
    have h3 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)
        = (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) *
            ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.mul_assoc _ _ (A : Matrix (Fin 3) (Fin 3) F), h3, Matrix.mul_one]
      _ = (g : Matrix (Fin 3) (Fin 3) F) * A := by rw [h1]
  obtain ⟨c, hc⟩ := hcomm _ hAcomm
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) A.mul_inv
    simp [hc] at this
  have hA : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) = A := by
    apply Units.ext
    rw [hc, smul_one_eq_diagonal]
    rfl
  rw [← hA, conjAut_scalar, map_one, mul_one]

theorem semiSL_fix_of_center_bot (A : GL (Fin 3) F) (σ : F ≃+* F) {Ω : Subgroup SL(3, F)}
    (hZ : scalars 3 F = ⊥) (hfix : ∀ g ∈ Ω, proj 3 F (semiSL A σ g) = proj 3 F g) :
    ∀ g ∈ Ω, semiSL A σ g = g := by
  intro g hg
  have h := proj_eq_proj_iff.1 (hfix g hg).symm
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h.symm

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
