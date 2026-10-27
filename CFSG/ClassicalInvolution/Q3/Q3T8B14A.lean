module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3NMDiag

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.E4G3

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement Matrix

local notation "𝔽₃" => GaloisField 3 1

section Ring

theorem sq_comm_of_inv {R : Type*} [Ring R] {M Mi X : R} (hMiM : Mi * M = 1)
    (h3 : X = M * (M * X * Mi) * Mi) : M * M * X = X * (M * M) := by
  symm
  calc X * (M * M) = (M * (M * X * Mi) * Mi) * (M * M) := by rw [← h3]
    _ = M * M * X * (Mi * (Mi * M) * M) := by simp only [mul_assoc]
    _ = M * M * X := by rw [hMiM, mul_one, hMiM, mul_one]

theorem conj_comm_of_comm {R : Type*} [Ring R] {g gi D N : R} (hgi : gi * g = 1)
    (h : D * N = N * D) : (g * D * gi) * (g * N * gi) = (g * N * gi) * (g * D * gi) := by
  have e1 : (g * D * gi) * (g * N * gi) = g * (D * N) * gi := by
    calc (g * D * gi) * (g * N * gi) = g * D * (gi * g) * N * gi := by simp only [mul_assoc]
      _ = g * D * N * gi := by rw [hgi, mul_one]
      _ = g * (D * N) * gi := by simp only [mul_assoc]
  have e2 : (g * N * gi) * (g * D * gi) = g * (N * D) * gi := by
    calc (g * N * gi) * (g * D * gi) = g * N * (gi * g) * D * gi := by simp only [mul_assoc]
      _ = g * N * D * gi := by rw [hgi, mul_one]
      _ = g * (N * D) * gi := by simp only [mul_assoc]
  rw [e1, e2, h]

end Ring

section SL4

open CFSG.ClassicalInvolution.Asc77.T8W (negTwo coe_negTwo sl4_graph_case twin_std_y'
  shape_block0_zero sq_scalar_of_commute mapMatrix_refl')
open CFSG.ClassicalInvolution.Models (longRootSet)

theorem fin3_sq_eq_one {a : 𝔽₃} (ha : a ≠ 0) : a * a = 1 := by
  have hcard : Nat.card 𝔽₃ = 3 := by simpa using GaloisField.card 3 1 one_ne_zero
  have : Fintype 𝔽₃ := Fintype.ofFinite _
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.card_eq_fintype_card, hcard] at h
  simpa [pow_two] using h

theorem conjSLAut_toGL (g : SL(4, 𝔽₃)) :
    Q3NM.conjSLAut (Matrix.SpecialLinearGroup.toGL g) = MulAut.conj g :=
  MulEquiv.ext fun _ => Subtype.ext rfl


theorem sl4_class_std3 {Y : Type} [Group Y] (ψ : SL(4, 𝔽₃) →* Y)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center SL(4, 𝔽₃))
    (hk3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 → z = 1) (hSperf : Group.IsPerfect SL(4, 𝔽₃))
    (σ : MulAut Y) (hσ2 : ∀ x, σ (σ x) = x)
    (h0 : ∀ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 0 (by norm_num)).range, σ (ψ r) = ψ r)
    (hnt : ∃ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 2 (by norm_num)).range, σ (ψ r) ≠ ψ r) :
    ∃ D : GL (Fin 4) 𝔽₃, D * D = 1 ∧ (∀ x, σ (ψ x) = ψ (Q3NM.conjSLAut D x)) ∧
      (D : Matrix (Fin 4) (Fin 4) 𝔽₃) * (negTwo 𝔽₃ : Matrix (Fin 4) (Fin 4) 𝔽₃) =
        (negTwo 𝔽₃ : Matrix (Fin 4) (Fin 4) 𝔽₃) * D := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  obtain ⟨α, g, φ, ε, hlift, hmat⟩ :=
    Q3W.linearAutClassification3 (n := 4) (by norm_num) Y ψ hψ hker σ
  have hα0 : ∀ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 0 (by norm_num)).range, α r = r := by
    refine fix_of_gen3 ψ hker hk3 α ?_ (fun r hr => by rw [hlift, h0 r hr])
    have := (ModelFacts.gen3_top_sl2 (F := 𝔽₃)).map (WeakCT.blockSL 𝔽₃ 4 2 0 (by norm_num))
    rwa [← MonoidHom.range_eq_map] at this
  have hα2 : ∀ x, α (α x) = x := by
    have := CFSG.ClassicalInvolution.Asc77.T8V.eq_of_central_ratio (α.comp α) (P := ⊤)
      (CFSG.ClassicalInvolution.Asc77.T8V.top_le_commutator_of_perfect hSperf) (fun x _ =>
        hker (by
          rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply, hlift, hlift, hσ2,
            mul_inv_cancel]))
    intro x
    simpa using this x (Subgroup.mem_top x)
  have hblock2 : (∀ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 2 (by norm_num)).range, α r = r) → False := by
    intro h
    obtain ⟨r, hr, hne⟩ := hnt
    exact hne (by rw [← hlift, h r hr])
  have hGGi : (g : Matrix (Fin 4) (Fin 4) 𝔽₃) *
      ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) *
      (g : Matrix (Fin 4) (Fin 4) 𝔽₃) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : (g : Matrix (Fin 4) (Fin 4) 𝔽₃).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  cases ε
  · have hmat' : ∀ x : SL(4, 𝔽₃),
        ((α x : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) =
          (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4) 𝔽₃) *
            ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) := fun x => by
      simpa using hmat x
    have key : ∀ x : SL(4, 𝔽₃), α x = x →
        (x : Matrix (Fin 4) (Fin 4) 𝔽₃) * (g : Matrix (Fin 4) (Fin 4) 𝔽₃) =
          (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4) 𝔽₃) := by
      intro x hx
      have h := hmat' x
      rw [hx] at h
      calc (x : Matrix (Fin 4) (Fin 4) 𝔽₃) * (g : Matrix (Fin 4) (Fin 4) 𝔽₃)
          = ((g : Matrix (Fin 4) (Fin 4) 𝔽₃) * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4) 𝔽₃) *
              ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃)) *
                (g : Matrix (Fin 4) (Fin 4) 𝔽₃) := by rw [← h]
        _ = (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4) 𝔽₃) := by
            rw [Matrix.mul_assoc, hGiG, Matrix.mul_one]
    have hr01 : ∀ t : 𝔽₃, E01 t * (g : Matrix (Fin 4) (Fin 4) 𝔽₃) =
        (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * E01 (φ t) := fun t => by
      have := key (u01 t) (hα0 _ (u01_mem t))
      simpa [RingEquiv.mapMatrix_apply, map_E01, u01] using this
    have hr10 : ∀ t : 𝔽₃, E10 t * (g : Matrix (Fin 4) (Fin 4) 𝔽₃) =
        (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * E10 (φ t) := fun t => by
      have := key (u10 t) (hα0 _ (u10_mem t))
      simpa [RingEquiv.mapMatrix_apply, map_E10, u10] using this
    obtain ⟨hφ, a, ha, hG⟩ := shape_block0_zero φ (g : Matrix (Fin 4) (Fin 4) 𝔽₃) hdet hr01 hr10
    subst hφ
    have hsq : ∀ x : SL(4, 𝔽₃),
        ((g : Matrix (Fin 4) (Fin 4) 𝔽₃) * (g : Matrix (Fin 4) (Fin 4) 𝔽₃)) *
        (x : Matrix (Fin 4) (Fin 4) 𝔽₃) =
          (x : Matrix (Fin 4) (Fin 4) 𝔽₃) *
            ((g : Matrix (Fin 4) (Fin 4) 𝔽₃) * (g : Matrix (Fin 4) (Fin 4) 𝔽₃)) := by
      intro x
      have h1 := hmat' (α x)
      have h2' := hmat' x
      have h3 : ((α (α x) : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) =
          (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * ((g : Matrix (Fin 4) (Fin 4) 𝔽₃) *
            (x : Matrix (Fin 4) (Fin 4) 𝔽₃) *
              ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃)) *
                ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) := by
        rw [h1, h2', mapMatrix_refl', mapMatrix_refl']
      rw [hα2 x] at h3
      exact sq_comm_of_inv hGiG h3
    obtain ⟨c, hc⟩ := sq_scalar_of_commute ((g : Matrix (Fin 4) (Fin 4) 𝔽₃) *
      (g : Matrix (Fin 4) (Fin 4) 𝔽₃)) (fun x => hsq x)
    have hca : c = a * a := by
      have h : (Matrix.scalar (Fin 4) c) 0 0 =
          ((g : Matrix (Fin 4) (Fin 4) 𝔽₃) * (g : Matrix (Fin 4) (Fin 4) 𝔽₃)) 0 0 := by
        rw [hc]
      have h' : ((g : Matrix (Fin 4) (Fin 4) 𝔽₃) * (g : Matrix (Fin 4) (Fin 4) 𝔽₃)) 0 0 =
          a * a := by
        rw [Matrix.mul_apply, Fin.sum_univ_four, hG]
        simp
      rw [h'] at h
      simpa using h
    have hGG : (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * (g : Matrix (Fin 4) (Fin 4) 𝔽₃) = 1 := by
      rw [← hc, hca, fin3_sq_eq_one ha]
      simp
    refine ⟨g, Units.ext (by rw [Units.val_mul, hGG, Units.val_one]), fun x => ?_, ?_⟩
    · rw [← hlift]
      congr 1
      apply Subtype.ext
      rw [hmat' x, mapMatrix_refl']
      rfl
    · rw [hG, coe_negTwo]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · have hmat' : ∀ x : SL(4, 𝔽₃),
        ((α x : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) =
          (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * φ.mapMatrix
            (((x⁻¹ : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃))ᵀ *
              ((g⁻¹ : GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) := fun x => by
      simpa using hmat x
    exact absurd (sl4_graph_case h2 α _ _ hGGi hGiG hdet φ hmat' hα2 hα0) hblock2

theorem sl4_class_of_pair3 {Y : Type} [Group Y] (ψ : SL(4, 𝔽₃) →* Y)
    {R R' : Subgroup SL(4, 𝔽₃)} {y y' : SL(4, 𝔽₃)} (hP : E4Pair3 ψ R R' y y')
    (hR : R ∈ longRootSet (K := 𝔽₃) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := 𝔽₃) (show 2 ≤ 4 by norm_num))
    (σ : MulAut Y) (hσ2 : ∀ x, σ (σ x) = x) (hσR : ∀ r ∈ R, σ (ψ r) = ψ r)
    (hσnt : ∃ r ∈ R', σ (ψ r) ≠ ψ r) :
    ∃ D : GL (Fin 4) 𝔽₃, D * D = 1 ∧ (∀ x, σ (ψ x) = ψ (Q3NM.conjSLAut D x)) ∧
      (D : Matrix (Fin 4) (Fin 4) 𝔽₃) * (y' : Matrix (Fin 4) (Fin 4) 𝔽₃) =
        (y' : Matrix (Fin 4) (Fin 4) 𝔽₃) * D := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hc : y' * y⁻¹ ∈ Subgroup.center SL(4, 𝔽₃) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, hRg, hR'g, hy'g⟩ := twin_std_y' h2 hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2
    hP.hy'1 hc
  set ψ₀ : SL(4, 𝔽₃) →* Y := ψ.comp (MulAut.conj g).toMonoidHom with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := hP.surj.comp (MulAut.conj g).surjective
  have hker₀ : ψ₀.ker ≤ Subgroup.center SL(4, 𝔽₃) := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ Subgroup.center SL(4, 𝔽₃) := hP.ker hx
    have h2' := (Subgroup.center SL(4, 𝔽₃)).normal_of_characteristic.conj_mem
      (g * x * g⁻¹) h1 g⁻¹
    simpa [mul_assoc] using h2'
  have hk3₀ : ∀ z ∈ ψ₀.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    have h1 : g * z * g⁻¹ ∈ ψ.ker := hz
    have h2' : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hz3]
      group
    have h3 := hP.ker3 _ h1 h2'
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  have h0 : ∀ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 0 (by norm_num)).range, σ (ψ₀ r) = ψ₀ r := by
    intro r hr
    apply hσR
    rw [hRg]
    exact ⟨r, hr, rfl⟩
  have hnt : ∃ r ∈ (WeakCT.blockSL 𝔽₃ 4 2 2 (by norm_num)).range, σ (ψ₀ r) ≠ ψ₀ r := by
    obtain ⟨r', hr', hne⟩ := hσnt
    rw [hR'g] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    exact ⟨r, hr, hne⟩
  obtain ⟨D₀, hD₀2, hD₀σ, hD₀c⟩ := sl4_class_std3 ψ₀ hψ₀s hker₀ hk3₀ hP.perf σ hσ2 h0 hnt
  refine ⟨Matrix.SpecialLinearGroup.toGL g * D₀ * (Matrix.SpecialLinearGroup.toGL g)⁻¹,
    ?_, fun x => ?_, ?_⟩
  · calc Matrix.SpecialLinearGroup.toGL g * D₀ * (Matrix.SpecialLinearGroup.toGL g)⁻¹ *
          (Matrix.SpecialLinearGroup.toGL g * D₀ * (Matrix.SpecialLinearGroup.toGL g)⁻¹)
        = Matrix.SpecialLinearGroup.toGL g * (D₀ * D₀) * (Matrix.SpecialLinearGroup.toGL g)⁻¹ := by
          group
      _ = 1 := by rw [hD₀2]; group
  · have hx : ψ₀ (g⁻¹ * x * g) = ψ x := by
      simp only [hψ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      congr 1
      group
    rw [← hx, hD₀σ]
    simp only [hψ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    congr 1
    rw [Q3NM.conjSLAut_mul, Q3NM.conjSLAut_mul, Q3NM.conjSLAut_inv, conjSLAut_toGL]
    simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_symm_apply, mul_assoc]
  · have hgi : ((g⁻¹ : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) *
        (g : Matrix (Fin 4) (Fin 4) 𝔽₃) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hy'm : (y' : Matrix (Fin 4) (Fin 4) 𝔽₃) =
        (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * (negTwo 𝔽₃ : Matrix (Fin 4) (Fin 4) 𝔽₃) *
          ((g⁻¹ : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) := by
      rw [hy'g, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have hDm : ((Matrix.SpecialLinearGroup.toGL g * D₀ * (Matrix.SpecialLinearGroup.toGL g)⁻¹ :
        GL (Fin 4) 𝔽₃) : Matrix (Fin 4) (Fin 4) 𝔽₃) =
        (g : Matrix (Fin 4) (Fin 4) 𝔽₃) * (D₀ : Matrix (Fin 4) (Fin 4) 𝔽₃) *
          ((g⁻¹ : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) := rfl
    rw [hDm, hy'm]
    exact conj_comm_of_comm hgi hD₀c

end SL4

section SL4Tag

open CFSG.ClassicalInvolution.Models (longRootSet)


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e4_class_sl43 (hΦ : HypOmegaModU (.sl2 3 1) Φ) (M : Ih8Model 3 1 Φ .PSL 4 1)
    {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) {x x' : X}
    (hxA : IsUniqueInvolution A x) (hxB : IsUniqueInvolution B x')
    (hcen : x * x' ∈ Subgroup.center X) (σ : MulAut X) (hσ2 : σ * σ = 1)
    (hσA : ∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A)
    (hσnt : ¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) :
    ∃ (D : GL (Fin 4) 𝔽₃) (y' : SL(4, 𝔽₃)), M.ψ y' = x' ∧ y' * y' = 1 ∧ D * D = 1 ∧
      (∀ g, σ (M.ψ g) = M.ψ (Q3NM.conjSLAut D g)) ∧
      (D : Matrix (Fin 4) (Fin 4) 𝔽₃) * (y' : Matrix (Fin 4) (Fin 4) 𝔽₃) =
        (y' : Matrix (Fin 4) (Fin 4) 𝔽₃) * D := by
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSL 4 3 1 Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSL 4 3 1 Fact.out trivial M.admissible).1.1
  have hex := exactMembers_of_ih8Model M hΦ hG2 hD4
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hA hB hxA hxB hcen
  have hA0 : oddCoreOf A = ⊥ := oddCoreOf_eq_bot_of_exact hex hA
  have hB0 : oddCoreOf B = ⊥ := oddCoreOf_eq_bot_of_exact hex hB.1
  have hRl := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR)
  have hRl' := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR')
  have hσ2' : ∀ z, σ (σ z) = z := fun z => by
    have := congrArg (fun τ : MulAut X => τ z) hσ2
    simpa using this
  have hσR : ∀ r ∈ R, σ (M.ψ r) = M.ψ r := by
    intro r hr
    have h := hσA (M.ψ r) (by rw [hAR]; exact Subgroup.mem_map_of_mem _ hr)
    rw [hA0, Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  have hσnt' : ∃ r ∈ R', σ (M.ψ r) ≠ M.ψ r := by
    by_contra hcon
    push Not at hcon
    apply hσnt
    intro k hk
    rw [hBR] at hk
    obtain ⟨r, hr, rfl⟩ := hk
    rw [hB0, Subgroup.mem_bot, mul_inv_eq_one]
    exact hcon r hr
  obtain ⟨D, hD2, hDσ, hDc⟩ := sl4_class_of_pair3 M.ψ hP hRl hRl' σ hσ2' hσR hσnt'
  exact ⟨D, y', hy', hP.hy'2, hD2, hDσ, hDc⟩

end SL4Tag

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.E4G3
