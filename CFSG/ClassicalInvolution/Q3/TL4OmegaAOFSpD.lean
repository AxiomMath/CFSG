module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpC
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpAut

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SpL

open Matrix CFSG CFSG.Blueprint CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Q3.TL4.Gauss
open CFSG.LocalAnalysis.ComponentInitial (SymplecticTorusWeyl.mem_statedSp_iff)
open scoped MatrixGroups

section Theta

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)]
  [Module (GaussField F) (Fin 2 ⊕ Fin 2 → F)]
  [IsScalarTower F (GaussField F) (Fin 2 ⊕ Fin 2 → F)] {A : GL (Fin 2 ⊕ Fin 2) F}
  (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = glLin A v)
  (hωa : ∀ u v, omega F 2 (glLin A u) (glLin A v) = -omega F 2 u v)
  {e f : Fin 2 ⊕ Fin 2 → F} (hef : spBilin (omega F 2) hω hωa e f = 1)

include hef in
theorem theta_mem (X : SL(2, GaussField F)) : theta hω hωa hef X ∈ StatedSp 2 F := by
  apply mem_statedSp_of_omega
  intro u v
  obtain ⟨x, rfl⟩ := (phiEquiv hω hωa hef).surjective u
  obtain ⟨y, rfl⟩ := (phiEquiv hω hωa hef).surjective v
  rw [theta_mulVec, theta_mulVec, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  show (spBilin (omega F 2) hω hωa _ _).re = (spBilin (omega F 2) hω hωa _ _).re
  rw [beta_phiEquiv, beta_phiEquiv, det_mul_std, Matrix.SpecialLinearGroup.det_coe, one_mul]

include hef in
theorem theta_mul_comm (X : SL(2, GaussField F)) :
    theta hω hωa hef X * A = A * theta hω hωa hef X := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  have h1 : (((theta hω hωa hef X : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) *ᵥ v =
      ((theta hω hωa hef X : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ glLin A v := by
    rw [← mulVec_mulVec, glLin_apply]
  have h2 : ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * ((theta hω hωa hef X :
      GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) *ᵥ v =
      glLin A (((theta hω hωa hef X : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v) := by
    rw [← mulVec_mulVec, glLin_apply]
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mul, Units.val_mul, h1, h2, ← hω, ← hω,
    theta_mulVec, theta_mulVec, map_smul, mulVec_smul, map_smul]

include hef in
theorem theta_injective : Function.Injective (theta hω hωa hef) := by
  intro X Y h
  have h1 : ∀ x : Fin 2 → GaussField F, (X : Matrix (Fin 2) (Fin 2) (GaussField F)) *ᵥ x =
      (Y : Matrix (Fin 2) (Fin 2) (GaussField F)) *ᵥ x := by
    intro x
    have h2 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) F =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ phiEquiv hω hωa hef x) h
    simp only [theta_mulVec, LinearEquiv.symm_apply_apply] at h2
    exact (phiEquiv hω hωa hef).injective h2
  apply Subtype.ext
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun x => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h1]

include hef in
theorem exists_theta_of_comm {b : GL (Fin 2 ⊕ Fin 2) F} (hb : b ∈ StatedSp 2 F)
    (hbA : b * A = A * b) : ∃ X : SL(2, GaussField F), theta hω hωa hef X = b := by
  classical
  set φ := phiEquiv hω hωa hef with hφ
  have hc : ∀ v, glEquiv F _ b (glLin A v) = glLin A (glEquiv F _ b v) := fun v => by
    rw [glEquiv_apply, glEquiv_apply, glLin_apply, glLin_apply, mulVec_mulVec, mulVec_mulVec,
      ← Units.val_mul, ← Units.val_mul, hbA]
  set ν' := ofCommute hω (glEquiv F _ b) hc with hν'
  set Y : (Fin 2 → GaussField F) →ₗ[GaussField F] (Fin 2 → GaussField F) :=
    φ.symm.toLinearMap ∘ₗ ν'.toLinearMap ∘ₗ φ.toLinearMap with hY
  set M := LinearMap.toMatrix' Y with hM
  have hMv : ∀ x, M *ᵥ x = Y x := fun x => LinearMap.toMatrix'_mulVec Y x
  have hνφ : ∀ x, glEquiv F _ b (φ x) = φ (M *ᵥ x) := fun x => by
    rw [hMv, hY]
    simp [hν', ofCommute_apply]
  have hβ := (spBilin_map_iff hω hωa (ν := glEquiv F _ b) hc).mp (fun u v => by
    rw [glEquiv_apply, glEquiv_apply]
    exact omega_of_mem_statedSp hb u v)
  have hdet : M.det = 1 := by
    have h1 := hβ (φ ![1, 0]) (φ ![0, 1])
    rw [hνφ, hνφ, beta_phiEquiv, beta_phiEquiv, det_mul_std] at h1
    simpa using h1
  let X : SL(2, GaussField F) := ⟨M, hdet⟩
  refine ⟨X, Units.ext ?_⟩
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := φ.surjective v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, theta_mulVec, ← hφ, LinearEquiv.symm_apply_apply,
    ← glEquiv_apply, hνφ]

end Theta

section Block

variable {F : Type} [Field F] [Finite F]

theorem isQuasisimple_SL2_gauss [Fact (Nat.card F = 3)] :
    CFSG.Open.IsQuasisimple SL(2, GaussField F) := by
  have h4 : ∃ s : Finset (GaussField F), s.card = 4 := by
    have : Fintype (GaussField F) := Fintype.ofFinite _
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (GaussField F)))
      (n := 4) (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_gaussField_eq_nine Fact.out]
        norm_num)
    exact ⟨t, ht⟩
  exact ⟨(CFSG.LinearGroups.special_linear_isPerfect (K := GaussField F) (n := 2) le_rfl
    (Or.inr h4)).commutator_eq_top,
    (CFSG.LinearGroups.linear_projective_simple (K := GaussField F) (n := 2) le_rfl
      (Or.inr h4)).2.1⟩

theorem oddCoreIn_fixed_conjSp_of_gauss [Fact (Nat.card F = 3)]
    [Module (GaussField F) (Fin 2 ⊕ Fin 2 → F)]
    [IsScalarTower F (GaussField F) (Fin 2 ⊕ Fin 2 → F)] (A : gsp 2 F)
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      formJ 2 F * (A : GL (Fin 2 ⊕ Fin 2) F) = (-1 : F) • formJ 2 F)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = glLin (A : GL (Fin 2 ⊕ Fin 2) F) v) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (StatedSp 2 F) (conjSp 2 F A))) = ⊥ := by
  classical
  have hF : Nat.card F = 3 := Fact.out
  have hωa := omega_glLin hA
  obtain ⟨e, f, hef⟩ := exists_beta_eq_one hω hωa
  have hZ2 := isPGroup_center_statedSp (n := 2) hF
  have hSL := isQuasisimple_SL2_gauss (F := F)
  have hSLZ : IsPGroup 2 (Subgroup.center SL(2, GaussField F)) :=
    isPGroup_center_specialLinear_of_card (k := 3)
      (by rw [card_gaussField_eq_nine hF]; norm_num) (by norm_num)
  let Θ : SL(2, GaussField F) →* StatedSp 2 F :=
    (theta hω hωa hef).codRestrict _ (theta_mem hω hωa hef)
  have hΘ : ∀ X, ((Θ X : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) = theta hω hωa hef X :=
    fun X => rfl
  have hΘinj : Function.Injective Θ := fun X Y h =>
    theta_injective hω hωa hef (congrArg Subtype.val h)
  have hker : ((QuotientGroup.mk' (Subgroup.center (StatedSp 2 F))).comp Θ).ker ≤
      Subgroup.center SL(2, GaussField F) := by
    intro X hX
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hX
    rw [Subgroup.mem_center_iff]
    intro Y
    apply hΘinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hX (Θ Y)
  have hno : oddCoreIn (Θ.range.map (QuotientGroup.mk' (Subgroup.center (StatedSp 2 F)))) = ⊥ := by
    have h := CFSG.ClassicalInvolution.Q3.oddCoreIn_range_eq_bot_of_isQuasisimple
      ((QuotientGroup.mk' (Subgroup.center (StatedSp 2 F))).comp Θ) hSL hSLZ hker
    rwa [MonoidHom.range_comp] at h
  refine oddCoreIn_fixed_eq_bot_of_blocks hZ2 _ (ι := Unit) (fun _ => Θ.range) ?_ ?_
    (fun _ => hno) ?_
  · intro _ x hx
    obtain ⟨X, rfl⟩ := hx
    rw [mem_fixedSubgroup_conjSp, hΘ]
    exact theta_mul_comm hω hωa hef X
  · intro _ b hb x hx
    obtain ⟨X, rfl⟩ := hx
    obtain ⟨Y, hY⟩ := exists_theta_of_comm hω hωa hef b.2 ((mem_fixedSubgroup_conjSp A b).mp hb)
    have hbY : b = Θ Y := Subtype.ext hY.symm
    refine ⟨Y * X * Y⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hbY]
  · intro ν hν hcomm
    obtain ⟨Y, hY⟩ := exists_theta_of_comm hω hωa hef ν.2 ((mem_fixedSubgroup_conjSp A ν).mp hν)
    have hνY : ν = Θ Y := Subtype.ext hY.symm
    have hYc : Y ∈ Subgroup.center SL(2, GaussField F) := by
      rw [Subgroup.mem_center_iff]
      intro X
      apply hΘinj
      rw [map_mul, map_mul, ← hνY]
      exact (hcomm () (Θ X) ⟨X, rfl⟩).symm
    obtain ⟨k, hk⟩ := hSLZ ⟨Y, hYc⟩
    refine ⟨k, ?_⟩
    rw [hνY, ← map_pow]
    have hk' : Y ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [hk', map_one]

theorem spCplxStatement_proved (hF : Nat.card F = 3) : SpCplxStatement F := by
  intro A hA hAA
  have : Fact (Nat.card F = 3) := ⟨hF⟩
  have ha : ∀ v, glLin (A : GL (Fin 2 ⊕ Fin 2) F) (glLin (A : GL (Fin 2 ⊕ Fin 2) F) v) = -v :=
    fun v => by rw [glLin_apply, glLin_apply, mulVec_mulVec, hAA, neg_mulVec, one_mulVec]
  let _ : Module (GaussField F) (Fin 2 ⊕ Fin 2 → F) := gaussModule (glLin _) ha
  have : IsScalarTower F (GaussField F) (Fin 2 ⊕ Fin 2 → F) := ⟨fun c z v => by
    show (c • z).re • v + (c • z).im • glLin (A : GL (Fin 2 ⊕ Fin 2) F) v =
      c • (z.re • v + z.im • glLin (A : GL (Fin 2 ⊕ Fin 2) F) v)
    rw [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_add, smul_eq_mul, smul_eq_mul,
      mul_smul, mul_smul]⟩
  have hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v =
      glLin (A : GL (Fin 2 ⊕ Fin 2) F) v := fun v => by
    show (QuadraticAlgebra.omega : GaussField F).re • v +
      (QuadraticAlgebra.omega : GaussField F).im • glLin (A : GL (Fin 2 ⊕ Fin 2) F) v = _
    rw [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_smul, one_smul, zero_add]
  exact oddCoreIn_fixed_conjSp_of_gauss A hA hω

end Block

section Model


theorem outerFixedOddFree_psp : OuterFixedOddFree .PSp 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact outerFixedOddFree_psp_of
    (spCplxStatement_proved (by simpa using GaloisField.card 3 1 one_ne_zero))

end Model

end CFSG.ClassicalInvolution.Q3.TL4.SpL
