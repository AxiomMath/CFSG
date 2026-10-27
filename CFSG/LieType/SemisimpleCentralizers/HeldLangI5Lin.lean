module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5LinInn
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Torus
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Aux
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.LieType.SemisimpleCentralizers.HeldLangUnitFix

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open scoped commutatorElement
open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification CFSG.HardMathSupport.Foote.ModuleExclusions
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

variable {n : ℕ} {K : Type} [Field K]

theorem conjAut_fieldAut_pow (A : GL (Fin n) K) (σ : K ≃+* K) (k : ℕ) :
    (conjAut n K A * fieldAut n K σ) ^ k = conjAut n K (normProd σ A k) * fieldAut n K (σ ^ k) := by
  induction k with
  | zero => simp [normProd]
  | succ k ih =>
    rw [pow_succ', ih]
    have h := fieldAut_mul_conjAut σ (normProd σ A k)
    calc conjAut n K A * fieldAut n K σ * (conjAut n K (normProd σ A k) * fieldAut n K (σ ^ k))
        = conjAut n K A * (fieldAut n K σ * conjAut n K (normProd σ A k)) * fieldAut n K (σ ^ k) := by
          group
      _ = conjAut n K A * (conjAut n K (glMap σ (normProd σ A k)) * fieldAut n K σ) *
            fieldAut n K (σ ^ k) := by rw [h]
      _ = conjAut n K (A * glMap σ (normProd σ A k)) * (fieldAut n K σ * fieldAut n K (σ ^ k)) := by
          rw [map_mul]; group
      _ = conjAut n K (normProd σ A (k + 1)) * fieldAut n K (σ ^ (k + 1)) := by
          rw [← map_mul, ← pow_succ']
          rfl

theorem exists_sigma_of_outer_three [Finite K] {N : ℕ} (hN : 3 ≤ N)
    (β' : MulAut (projectiveSL N K)) (hβ'3 : β' ^ 3 = 1)
    (hout : β' ∉ innAutDerived (projectiveSL N K)) :
    ∃ (A : GL (Fin N) K) (σ : K ≃+* K), β' = conjAut N K A * fieldAut N K σ ∧ orderOf σ = 3 ∧
      ∃ c : Kˣ, normProd σ A 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) hN
  obtain ⟨A, σ, ε, hε, hβ'eq⟩ := hgen β'
  have hε0 : ε = 0 := by
    by_contra hne
    have hε1 : ε = 1 := by omega
    subst hε1
    rw [pow_one] at hβ'eq
    set X := conjAut N K A * fieldAut N K σ * dualAut N K with hX
    have hX3 : X ^ 3 = 1 := by rw [← hβ'eq]; exact hβ'3
    have hX2 := sq_conjAut_fieldAut_dualAut A σ
    have hXinv : X = (X ^ 2)⁻¹ := by
      have : X ^ 2 * X = 1 := by rw [← pow_succ]; exact hX3
      exact (inv_eq_of_mul_eq_one_right this).symm
    have hcf : ∀ (C : GL (Fin N) K) (τ : K ≃+* K), conjAut N K C * fieldAut N K τ ∈ semilinearAutGroup N K :=
      fun C τ => mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup C))
        (fieldAut_mem_semilinearAutGroup τ)
    have hXmem : X ∈ semilinearAutGroup N K := by
      rw [hXinv, hX2]
      exact inv_mem (hcf _ _)
    have hδ : dualAut N K ∈ semilinearAutGroup N K := by
      have : dualAut N K = (conjAut N K A * fieldAut N K σ)⁻¹ * X := by rw [hX]; group
      rw [this]
      exact mul_mem (inv_mem (hcf _ _)) hXmem
    exact dualAut_not_mem_semilinearAutGroup hN hδ
  have hβ'eq' : β' = conjAut N K A * fieldAut N K σ := by rw [hβ'eq, hε0, pow_zero, mul_one]
  have hcube : conjAut N K (normProd σ A 3) * fieldAut N K (σ ^ 3) = 1 := by
    rw [← conjAut_fieldAut_pow, ← hβ'eq']
    exact hβ'3
  have hσ3 : σ ^ 3 = 1 := by
    have h2 : conjAut N K (normProd σ A 3) * fieldAut N K (σ ^ 3) * dualAut N K ^ 0 =
        conjAut N K 1 * fieldAut N K 1 * dualAut N K ^ 0 := by
      rw [hcube]
      simp
    exact (standard_form_unique hN (Nat.zero_le 1) (Nat.zero_le 1) h2).1
  have hcN : conjAut N K (normProd σ A 3) = 1 := by
    rw [hσ3, map_one, mul_one] at hcube
    exact hcube
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hN _).1 hcN
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hout
    have : β' = conjAut N K A := by rw [hβ'eq', h1, map_one, mul_one]
    rw [this]
    exact conjAut_mem_innAutDerived A (by rw [← this]; exact hβ'3)
  exact ⟨A, σ, hβ'eq', orderOf_eq_prime hσ3 hσ1, c, hc⟩

theorem kd264I5_SL [Finite K] {N : ℕ} (hN : 3 ≤ N) (h3q : 3 ∣ Nat.card K - 1)
    (β : MulAut (Matrix.SpecialLinearGroup (Fin N) K)) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived
      (Matrix.SpecialLinearGroup (Fin N) K ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin N) K))) :
    ∃ E : Subgroup (Matrix.SpecialLinearGroup (Fin N) K),
      E ≤ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id _) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (N - 1) := by
  haveI : NeZero N := ⟨by omega⟩
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin N) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hN
  haveI := hperf
  let e₀ : Matrix.SpecialLinearGroup (Fin N) K ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin N) K) ≃*
      projectiveSL N K := QuotientGroup.quotientMulEquivOfEq (scalars_eq_center N K).symm
  let β' : MulAut (projectiveSL N K) := descendAut N K β
  have hβ'proj : ∀ g, β' (proj N K g) = proj N K (β g) := fun g => descendAut_proj N K β g
  have hβ'3 : β' ^ 3 = 1 := by
    rw [← map_pow, hβ3, map_one]
  have hocq : onCenterQuotient β = MulAut.congr e₀.symm β' := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    show _ = e₀.symm (β' (e₀ (QuotientGroup.mk g)))
    have h1 : e₀ (QuotientGroup.mk g) = proj N K g :=
      QuotientGroup.quotientMulEquivOfEq_mk (scalars_eq_center N K).symm g
    have h2 : onCenterQuotient β (QuotientGroup.mk g) = QuotientGroup.mk (β g) :=
      onCenterQuotient_apply_mk β g
    rw [h1, hβ'proj, h2]
    exact (QuotientGroup.quotientMulEquivOfEq_mk (scalars_eq_center N K) (β g)).symm
  have hout' : β' ∉ innAutDerived (projectiveSL N K) := by
    intro hmem
    apply hout
    rw [hocq]
    exact (mem_innAutDerived_congr e₀.symm).2 hmem
  obtain ⟨A, σ, hβ'eq', hσord, c, hc⟩ := exists_sigma_of_outer_three hN β' hβ'3 hout'
  let lift : Matrix.SpecialLinearGroup (Fin N) K →* Matrix.SpecialLinearGroup (Fin N) K :=
    (CatalogueBHigherLinearAction.slConjugation N K A).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.map (σ : K →+* K))
  have hlift_proj : ∀ g, proj N K (lift g) = β' (proj N K g) := fun g => by
    rw [hβ'eq', MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  have hβlift : β.toMonoidHom = lift := by
    refine eq_of_central_displacement β.toMonoidHom lift fun g => ?_
    rw [← scalars_eq_center N K]
    exact proj_eq_proj_iff.1 (by rw [hlift_proj, hβ'proj]; rfl)
  have hβ_gl : ∀ g : Matrix.SpecialLinearGroup (Fin N) K,
      Matrix.SpecialLinearGroup.toGL (β g) =
        A * glMap σ (Matrix.SpecialLinearGroup.toGL g) * A⁻¹ := fun g => by
    have h1 : β g = lift g := congrArg (fun m : _ →* _ => m g) hβlift
    rw [h1]
    show Matrix.SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation N K A
      (Matrix.SpecialLinearGroup.map (σ : K →+* K) g)) = _
    rw [CatalogueBHigherLinearAction.toGL_slConjugation]
    have : Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (σ : K →+* K) g) =
        glMap σ (Matrix.SpecialLinearGroup.toGL g) := Units.ext rfl
    rw [this]
  have hcs : Ai σ (A : Matrix (Fin N) (Fin N) K) (orderOf σ) = ((c : Kˣ) : K) • (1 : Matrix (Fin N) (Fin N) K) := by
    rw [hσord, ← coe_normProd]
    have : normProd σ A 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c := hc
    rw [this, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  obtain ⟨y, hy⟩ := exists_twist_eq_conj σ A ((c : Kˣ) : K) hcs
  have hfix : ∀ g : Matrix.SpecialLinearGroup (Fin N) K, β g = g ↔
      y * Matrix.SpecialLinearGroup.toGL g * y⁻¹ ∈ glFix σ := fun g => by
    have h1 : β g = g ↔ Matrix.SpecialLinearGroup.toGL (β g) = Matrix.SpecialLinearGroup.toGL g :=
      ⟨fun h => by rw [h], fun h => Matrix.SpecialLinearGroup.toGL_injective h⟩
    rw [h1, hβ_gl, hy, mem_glFix]
    constructor
    · intro h
      have : glMap σ (y * Matrix.SpecialLinearGroup.toGL g * y⁻¹) =
          y * (y⁻¹ * glMap σ (y * Matrix.SpecialLinearGroup.toGL g * y⁻¹) * y) * y⁻¹ := by group
      rw [this, h]
    · intro h
      rw [h]
      group
  haveI := Fintype.ofFinite K
  obtain ⟨p, hpc⟩ := CharP.exists K
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨e, hp, hKe⟩ := FiniteField.card K p
  have hKe' : Nat.card K = p ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, hKe]
  have he1 : 1 ≤ (e : ℕ) := e.pos
  have hdvd := orderOf_dvd_of_card hp he1 hKe' σ
  have hF0 := card_fixField hp he1 hKe' σ
  rw [hσord] at hdvd hF0
  haveI : Finite (fixField σ) := CFSG.Semidihedral.FixedFieldData.finite_of_prime_power_card _ hp hF0
  have h3F : 3 ∣ Nat.card (fixField σ) - 1 := by
    obtain ⟨m, hm⟩ := hdvd
    have hKx : Nat.card K = (p ^ m) ^ 3 := by rw [hKe', hm, mul_comm, pow_mul]
    have hem : (e : ℕ) / 3 = m := by omega
    rw [hF0, hem]
    rw [hKx] at h3q
    have hx : (p ^ m) ^ 3 % 3 = (p ^ m) % 3 := by
      have := Nat.mod_lt (p ^ m) (by norm_num : 3 > 0)
      interval_cases hm3 : (p ^ m) % 3 <;> simp [Nat.pow_mod, hm3]
    have hpos : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp.pos
    have hpos3 : 1 ≤ (p ^ m) ^ 3 := Nat.one_le_pow _ _ hpos
    omega
  obtain ⟨D, hD, hDcard⟩ := exists_torus3_sl h3F (by omega : 1 ≤ N)
  have hdetΦ : ∀ x₀ : slGL (Fin N) (fixField σ),
      (y⁻¹ * glFixEmb σ (x₀ : GL (Fin N) (fixField σ)) * y : GL (Fin N) K).val.det = 1 := by
    intro x₀
    have h1 : glFixEmb σ (x₀ : GL (Fin N) (fixField σ)) ∈ slGL (Fin N) K :=
      (Subgroup.mem_inf.1 ((mem_slGL_inf_glFix_iff σ).2 ⟨x₀, rfl⟩)).1
    have h2 := conj_mem_slGL y⁻¹ h1
    rw [inv_inv] at h2
    exact mem_slGL.1 h2
  let Φ : slGL (Fin N) (fixField σ) →* Matrix.SpecialLinearGroup (Fin N) K :=
    { toFun := fun x₀ => ⟨(y⁻¹ * glFixEmb σ (x₀ : GL (Fin N) (fixField σ)) * y : GL (Fin N) K).val, hdetΦ x₀⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have h : y⁻¹ * glFixEmb σ ((a * b : slGL (Fin N) (fixField σ)) : GL (Fin N) (fixField σ)) * y =
            (y⁻¹ * glFixEmb σ (a : GL (Fin N) (fixField σ)) * y) *
              (y⁻¹ * glFixEmb σ (b : GL (Fin N) (fixField σ)) * y) := by
          rw [Subgroup.coe_mul, map_mul]
          group
        show (y⁻¹ * glFixEmb σ ((a * b : slGL (Fin N) (fixField σ)) : GL (Fin N) (fixField σ)) * y :
          GL (Fin N) K).val = _
        rw [h, Units.val_mul]
        rfl) }
  have hΦgl : ∀ x₀ : slGL (Fin N) (fixField σ), Matrix.SpecialLinearGroup.toGL (Φ x₀) =
      y⁻¹ * glFixEmb σ (x₀ : GL (Fin N) (fixField σ)) * y := fun x₀ => Units.ext rfl
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h1 := congrArg Matrix.SpecialLinearGroup.toGL hab
    rw [hΦgl, hΦgl] at h1
    have h2 : glFixEmb σ (a : GL (Fin N) (fixField σ)) = glFixEmb σ (b : GL (Fin N) (fixField σ)) := by
      simpa using h1
    exact Subtype.ext (glFixEmb_injective σ h2)
  refine ⟨D.map Φ, ?_, isElemAbelian_map_of_injective Φ hD, ?_⟩
  · rintro _ ⟨x₀, hx₀, rfl⟩
    show β (Φ x₀) = Φ x₀
    rw [hfix, hΦgl]
    have : y * (y⁻¹ * glFixEmb σ (x₀ : GL (Fin N) (fixField σ)) * y) * y⁻¹ =
        glFixEmb σ (x₀ : GL (Fin N) (fixField σ)) := by group
    rw [this]
    exact glFixEmb_mem σ _
  · rw [Subgroup.card_map_of_injective hΦinj, hDcard]

end CFSG.LieType.SemisimpleCentralizers.HeldLang
