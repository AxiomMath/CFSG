module

public import CFSG.GH74.Generic.S45.LSymGraph
public import CFSG.GH74.Generic.S45.LPsl2Lin
public import CFSG.GH74.Generic.S45.LOddG
public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)
open scoped MatrixGroups Matrix

section G0

variable (F : Type*) [Field F]

@[expose] def g0SL : SL(3, F) := ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def d0SL : SL(3, F) := ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

variable {F}

@[simp] theorem g0SL_coe : ((g0SL F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    !![0, -1, 0; 1, 0, 0; 0, 0, 1] := rfl

@[simp] theorem d0SL_coe : ((d0SL F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := rfl

theorem g0SL_mul_self : g0SL F * g0SL F = d0SL F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, g0SL_coe, d0SL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem d0SL_mul_self : d0SL F * d0SL F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, d0SL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem d0SL_comm_g0SL : d0SL F * g0SL F = g0SL F * d0SL F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, g0SL_coe, d0SL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem g0SL_pow_four : g0SL F ^ 4 = 1 := by
  have : g0SL F ^ 4 = (g0SL F * g0SL F) * (g0SL F * g0SL F) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [this, g0SL_mul_self, d0SL_mul_self]

theorem d0SL_ne_one (h2 : (2 : F) ≠ 0) : d0SL F ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp at this
  exact h2 (by linear_combination -this)

theorem g0SL_transpose_mul : (g0SL F).transpose * g0SL F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
    Matrix.SpecialLinearGroup.coe_transpose, g0SL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem map_g0SL (σ : F ≃+* F) : Matrix.SpecialLinearGroup.map σ.toRingHom (g0SL F) = g0SL F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem graphAut_g0SL : (g0SL F)⁻¹.transpose = g0SL F := by
  have h : (g0SL F)⁻¹ = (g0SL F).transpose := inv_eq_of_mul_eq_one_left g0SL_transpose_mul
  rw [h]
  apply Subtype.ext
  simp

theorem orderOf_proj_g0SL (h2 : (2 : F) ≠ 0) :
    orderOf (LinearFlag.proj 3 F (g0SL F)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := LinearFlag.proj 3 F (g0SL F))
    (by
      rw [pow_one, ← map_pow, LinearFlag.proj_eq_one_iff, pow_two, g0SL_mul_self]
      rintro ⟨l, -, hl⟩
      have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hl
      have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 2 2) hl
      simp [Matrix.scalar_apply] at h00 h22
      exact h2 (by linear_combination h22 - h00))
    (by rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow, g0SL_pow_four, map_one])
  rw [h]
  norm_num

end G0

theorem exists_projective_rep {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {r f m : ℕ} (hr2 : r ≠ 2) (hm : 3 ≤ m)
    (hmodel : StatedClassicalModel S .PSL m r f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = r ^ f ∧ r.Prime ∧ 1 ≤ f ∧
      ringChar F ≠ 2 ∧ ∃ (ψ : S ≃* LinearFlag.projectiveSL m F)
        (ρ : MulAut S →* MulAut (LinearFlag.projectiveSL m F)), Function.Injective ρ ∧
          ∀ (ya : MulAut S) (s : S), ψ (ya s) = ρ ya (ψ s) := by
  classical
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hS hnab
  have hι : Function.Injective (MulAut.conj : S →* MulAut S) := by
    intro g g' h
    have hc : g'⁻¹ * g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
      have hx := congrArg (fun φ : MulAut S => φ x) h
      simp only [MulAut.conj_apply] at hx
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
        _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  let e : S ≃* ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner S) :=
    MonoidHom.ofInjective hι
  have hconj : ∀ (α : MulAut S) (s : S), α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := fun α s => by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hCW : Subgroup.centralizer
      ((CFSG.ComponentClassification.OuterAutomorphisms.inner S : Subgroup (MulAut S)) :
        Set (MulAut S)) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    ext s
    have h1 : MulAut.conj s * α = α * MulAut.conj s :=
      Subgroup.mem_centralizer_iff.1 hα (MulAut.conj s) ⟨s, rfl⟩
    have h2 : MulAut.conj (α s) = MulAut.conj s := by
      rw [← hconj α s, ← h1]
      group
    simpa using hι h2
  obtain ⟨⟨hr, hf, -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hr.ne_zero)
  have hk2 : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hr hr2 hF
  let ψ : S ≃* LinearFlag.projectiveSL m F :=
    e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj m F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL m F))
  let φ : ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner S) ≃*
      LinearFlag.projectiveSL m F := e.symm.trans ψ
  have hZP := center_projectiveSL_eq_bot (k := F) hm
  obtain ⟨ρ, hinj, -, -, hρφ⟩ :=
    socle_extension (W := CFSG.ComponentClassification.OuterAutomorphisms.inner S) hCW φ hZP
  refine ⟨F, inferInstance, inferInstance, hF, hr, hf, hk2, ψ, ρ, hinj, fun ya s => ?_⟩
  have h1 := hρφ ya (e s)
  have h2 : MulAut.conjNormal ya (e s) = e (ya s) := Subtype.ext (hconj ya s)
  rw [h2] at h1
  have h3 : ∀ t, φ (e t) = ψ t := fun t => by simp [φ]
  rw [h3, h3] at h1
  exact h1.symm


theorem psl_three_fixed_inner {F : Type} [Field F] [Finite F] (hk2 : ringChar F ≠ 2)
    {B : Matrix.GeneralLinearGroup (Fin 3) F} (hB2 : LinearFlag.conjAut 3 F B ^ 2 = 1)
    (hB1 : LinearFlag.conjAut 3 F B ≠ 1) :
    ∃ p : LinearFlag.projectiveSL 3 F, LinearFlag.conjAut 3 F B p = p ∧ orderOf p = 4 := by
  classical
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  have hm3 : 3 ≤ 3 := le_refl 3
  have h2' : LinearFlag.conjAut 3 F (B ^ 2) = 1 := by rw [map_pow]; exact hB2
  obtain ⟨μ, hμ⟩ := (conjAut_eq_one_iff hm3 _).mp h2'
  have hBB : (B : Matrix (Fin 3) (Fin 3) F) * B = (μ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 3) F =>
      (A : Matrix (Fin 3) (Fin 3) F)) hμ
    simp only [pow_two, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [← this, Matrix.smul_one_eq_diagonal]
    rfl
  have hdet : ((B : Matrix (Fin 3) (Fin 3) F).det) * (B : Matrix (Fin 3) (Fin 3) F).det =
      (μ : F) ^ 3 := by
    have := congrArg Matrix.det hBB
    rwa [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
  set s : F := (B : Matrix (Fin 3) (Fin 3) F).det / (μ : F) with hs
  have hs0 : s ≠ 0 := by
    intro h
    have : (B : Matrix (Fin 3) (Fin 3) F).det = 0 := by
      rw [hs, div_eq_zero_iff] at h
      exact h.resolve_right hμ0
    exact (Matrix.isUnit_iff_isUnit_det _ |>.1 B.isUnit).ne_zero this
  have hss : s * s = μ := by
    rw [hs]
    field_simp
    linear_combination hdet
  have hdetB : (B : Matrix (Fin 3) (Fin 3) F).det = s * μ := by
    rw [hs]
    field_simp
  let Bm : Matrix (Fin 3) (Fin 3) F := s⁻¹ • (B : Matrix (Fin 3) (Fin 3) F)
  have hBm2 : Bm * Bm = 1 := by
    simp only [Bm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hBB]
    have : s⁻¹ * (s⁻¹ * μ) = 1 := by
      rw [← hss]
      field_simp
    rw [this, one_smul]
  have hBmdet : Bm.det = 1 := by
    simp only [Bm, Matrix.det_smul, Fintype.card_fin, hdetB]
    rw [← hss]
    field_simp
  let B'' : SL(3, F) := ⟨Bm, hBmdet⟩
  have hB''2 : B'' * B'' = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact hBm2)
  have hBc : (B : GL (Fin 3) F) = Matrix.SpecialLinearGroup.toGL B'' *
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s hs0) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    show (B : Matrix (Fin 3) (Fin 3) F) = Bm * Matrix.scalar (Fin 3) s
    simp only [Bm, Matrix.smul_mul, Matrix.scalar_apply]
    ext i j
    simp [Matrix.smul_apply]
    field_simp
  have hconj : LinearFlag.conjAut 3 F B = LinearFlag.conjAut 3 F (Matrix.SpecialLinearGroup.toGL B'') := by
    rw [(conjAut_eq_conjAut_iff hm3 _ _).2 ⟨Units.mk0 s hs0, hBc⟩]
  have hB''1 : B'' ≠ 1 := by
    intro h
    apply hB1
    rw [hconj, h, map_one, map_one]
  obtain ⟨g, hg⟩ := (CFSG.GH74.Generic.S3.singleInv_sl3 htwo) B'' (d0SL F) hB''2 hB''1
    d0SL_mul_self (d0SL_ne_one htwo)
  have hB''eq : B'' = g⁻¹ * d0SL F * g := by rw [← hg]; group
  have hsl : ∀ h : SL(3, F), CatalogueBHigherLinearAction.slConjugation 3 F
      (Matrix.SpecialLinearGroup.toGL B'') h = B'' * h * B''⁻¹ := by
    intro h
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CatalogueBHigherLinearAction.toGL_slConjugation]
    simp [map_mul, map_inv]
  have hc : d0SL F * g0SL F * (d0SL F)⁻¹ = g0SL F := by
    rw [mul_inv_eq_iff_eq_mul]
    exact d0SL_comm_g0SL
  refine ⟨LinearFlag.proj 3 F (g⁻¹ * g0SL F * g), ?_, ?_⟩
  · rw [hconj, LinearFlag.conjAut_proj, hsl]
    congr 1
    rw [hB''eq]
    calc g⁻¹ * d0SL F * g * (g⁻¹ * g0SL F * g) * (g⁻¹ * d0SL F * g)⁻¹
        = g⁻¹ * (d0SL F * g0SL F * (d0SL F)⁻¹) * g := by group
      _ = g⁻¹ * g0SL F * g := by rw [hc]
  · have : LinearFlag.proj 3 F (g⁻¹ * g0SL F * g) =
        (MulAut.conj (LinearFlag.proj 3 F g)⁻¹) (LinearFlag.proj 3 F (g0SL F)) := by
      simp [map_mul, map_inv]
    rw [this, MulEquiv.orderOf_eq]
    exact orderOf_proj_g0SL htwo


theorem psl_three_fixed {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel S .PSL 3 r f) {ya : MulAut S} (hsq : ya * ya = 1)
    (hne : ya ≠ 1) : ∃ x : S, ya x = x ∧ 4 ∣ orderOf x := by
  classical
  obtain ⟨F, _, _, hF, hr, hf, hk2, ψ, ρ, hinj, hψ⟩ :=
    exists_projective_rep hS hnab hr2 (le_refl 3) hmodel
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  have ha : orderOf ya = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  have hm3 : 3 ≤ 3 := le_refl 3
  have hρ1 : ρ ya ≠ 1 := fun h => hne (hinj (by rw [h, map_one]))
  have hρ2 : (ρ ya) ^ 2 = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have key : ∀ p : LinearFlag.projectiveSL 3 F, ρ ya p = p → orderOf p = 4 →
      ∃ x : S, ya x = x ∧ 4 ∣ orderOf x := by
    intro p hp h4
    refine ⟨ψ.symm p, ?_, ?_⟩
    · apply ψ.injective
      rw [hψ, MulEquiv.apply_symm_apply, hp]
    · rw [MulEquiv.orderOf_eq, h4]
  obtain ⟨-, hform⟩ := LinearFlag.automorphism_generation (K := F) hm3
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ ya)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hρa
      obtain ⟨p, hp, hord⟩ := psl_three_fixed_inner hk2 (B := B) (by rw [← hρa]; exact hρ2)
        (by rw [← hρa]; exact hρ1)
      exact key p (by rw [hρa]; exact hp) hord
    ·
      have hα2 : (LinearFlag.conjAut 3 F B * LinearFlag.fieldAut 3 F τ) ^ 2 = 1 := by
        rw [← hρa]; exact hρ2
      obtain ⟨-, -, H, hH⟩ := LinearFlag.linear_field_involution_descent hr hf hF hm3 B τ hτ hα2
      refine key (LinearFlag.conjAut 3 F H (LinearFlag.proj 3 F (g0SL F))) ?_ ?_
      · rw [hρa, hH]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self, LinearFlag.fieldAut_proj, map_g0SL]
      · rw [MulEquiv.orderOf_eq]
        exact orderOf_proj_g0SL htwo
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    ·
      subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (LinearFlag.conjAut 3 F B * LinearFlag.dualAut 3 F) ^ 2 = 1 := by
        rw [← hρa]; exact hρ2
      rcases transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
      · obtain ⟨p, hp, hord⟩ := exists_symmetric_graph_fixed_proj hk2 hm3 B hB
        exact key p (by rw [hρa]; exact hp) hord
      · exfalso
        have hdet : (B : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
          ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
        have h1 := congrArg Matrix.det hB
        rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at h1
        apply hdet
        have h2' : (2 : F) * (B : Matrix (Fin 3) (Fin 3) F).det = 0 := by
          linear_combination h1
        exact (mul_eq_zero.1 h2').resolve_left htwo
    ·
      have hα2 : (LinearFlag.conjAut 3 F B * LinearFlag.fieldAut 3 F τ * LinearFlag.dualAut 3 F) ^ 2
          = 1 := by
        rw [← hρa]; exact hρ2
      obtain ⟨-, -, H, hH⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent hr hf hF hm3 B τ hτ hα2
      refine key (LinearFlag.conjAut 3 F H (LinearFlag.proj 3 F (g0SL F))) ?_ ?_
      · rw [hρa, hH]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self, LinearFlag.dualAut_proj,
          graphAut_g0SL, LinearFlag.fieldAut_proj, map_g0SL]
      · rw [MulEquiv.orderOf_eq]
        exact orderOf_proj_g0SL htwo


theorem Hyp1310.center_eq_bot_psl3 {K : Type} [Group K] [Finite K] {y : MulAut K}
    {L : Subgroup K} (hyp : Hyp1310 K y L) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ center K) .PSL 3 r f) : Subgroup.center K = ⊥ := by
  obtain ⟨hKp, hZ2, -⟩ := hyp.data
  have hQ : LieModel (K ⧸ center K) .PSL 3 r f := Or.inl ⟨by simp [classicalTags], hmodel⟩
  have hker : (QuotientGroup.mk' (center K)).ker = Subgroup.center K := QuotientGroup.ker_mk' _
  obtain ⟨-, hdvd⟩ := CFSG.LieType.Steinberg.odd_field_higher_linear_perfect_central_two_kernel_cyclic
    (p := r) (f := f) (n := 3) hr2 hKp (η := QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) hker.le (by rw [hker]; exact hZ2) hQ
  rw [hker] at hdvd
  have h3 : Nat.card (Subgroup.center K) ∣ 3 := hdvd.trans (Nat.gcd_dvd_left 3 _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZ2
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
    have := h2.trans h3
    omega
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.1 hk

theorem oddRow_psl3 {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (hyp : Hyp1310 K y L) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel (K ⧸ center K) .PSL 3 r f) : False := by
  have hZ := hyp.center_eq_bot_psl3 hr2 hmodel
  obtain ⟨yb, Lb, q, hyb, hQ, -⟩ := hyp.quot_data
  obtain ⟨x, hx, h4⟩ := psl_three_fixed hyp.1.1.2.1 hyp.1.1.2.2 hr2 hmodel (ya := yb) hQ.sq hQ.ne
  exact hyp.false_of_fixed_order_four_of_center_bot hZ hyb hx h4

theorem oddRowG_PSL3 : OddRowG_PSL3 :=
  fun _ _ _ _ _ hypg _ _ hr2 hmodel => oddRow_psl3 hypg.2 hr2 hmodel

end CFSG.GH74.Generic.S45
