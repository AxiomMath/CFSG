module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryScalarCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace FourUnitary

open Module Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Aut

variable {F : Type*} [Field F] (hF : UnitaryFieldData 2 1 F)

theorem ringEquiv_eq_refl_or_bar (σ : F ≃+* F) :
    σ = RingEquiv.refl F ∨ ∀ a, σ a = hF.bar a := by
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hF
  have hσω0 : σ ω ≠ 0 := (map_ne_zero σ).2 hω0
  have hσω1 : σ ω ≠ 1 := fun h => hω1 (σ.injective (by rw [h, map_one]))
  rcases eq_zero_or_one_or_of_ne hF hω0 hω1 (σ ω) with h | h | h | h
  · exact absurd h hσω0
  · exact absurd h hσω1
  · left
    refine RingEquiv.ext fun a => ?_
    rcases eq_zero_or_one_or_of_ne hF hω0 hω1 a with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact h
    · rw [map_pow, h]
      rfl
  · right
    intro a
    rw [bar_eq_sq]
    rcases eq_zero_or_one_or_of_ne hF hω0 hω1 a with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact h
    · rw [map_pow, h]

@[expose] def barEquiv : F ≃+* F :=
  RingEquiv.ofBijective hF.bar (Function.Involutive.bijective hF.bar_bar)

theorem barEquiv_apply (a : F) : barEquiv hF a = hF.bar a :=
  rfl

end Aut

section Groups

variable {F : Type} [Field F] (hF : UnitaryFieldData 2 1 F) (d : ℕ)

abbrev unitaryU : Subgroup (GL (Fin d) F) :=
  primeFormUnitary hF ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)

theorem mem_unitaryU {A : GL (Fin d) F} :
    A ∈ unitaryU hF d ↔ ((A : Matrix (Fin d) (Fin d) F).map hF.bar)ᵀ * A = 1 := by
  rw [unitaryU, mem_primeFormUnitary, Units.val_one, Matrix.mul_one]

theorem mem_unitarySU_iff_unitaryU {A : GL (Fin d) F} :
    A ∈ unitarySU 2 1 F d ↔ A ∈ unitaryU hF d ∧ (A : Matrix (Fin d) (Fin d) F).det = 1 := by
  rw [mem_unitarySU_iff hF, mem_unitaryU, and_comm]

theorem scalar_mem_unitaryU (s : Fˣ) : GeneralLinearGroup.scalar (Fin d) s ∈ unitaryU hF d := by
  rw [mem_unitaryU, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map
    (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply, bar_mul_self hF s.ne_zero]

@[expose] def scalarU : Fˣ →* unitaryU hF d :=
  (GeneralLinearGroup.scalar (Fin d)).codRestrict _ (scalar_mem_unitaryU hF d)

theorem coe_scalarU (s : Fˣ) :
    ((scalarU hF d s : unitaryU hF d) : GL (Fin d) F) = GeneralLinearGroup.scalar (Fin d) s :=
  rfl

theorem isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin d) F) := by
  refine ⟨by rw [Units.val_one, Matrix.transpose_one], fun i j => ?_⟩
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

abbrev gammaD : Type :=
  unitaryU hF d ⋊[primeFormFieldU hF (isPrimeFormGram_one d)] (F ≃+* F)

theorem coe_gammaD_action (σ : F ≃+* F) (A : unitaryU hF d) :
    (((primeFormFieldU hF (isPrimeFormGram_one d) σ A : unitaryU hF d) : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = ((A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map σ :=
  rfl

@[expose] def scalarsGamma : Subgroup (gammaD hF d) :=
  (SemidirectProduct.inl.comp (scalarU hF d)).range

theorem gammaD_conj_inl (x : gammaD hF d) (n : unitaryU hF d) :
    x * SemidirectProduct.inl n * x⁻¹ =
      SemidirectProduct.inl (x.left * primeFormFieldU hF (isPrimeFormGram_one d) x.right n *
        x.left⁻¹) := by
  simp only [map_mul, map_inv, SemidirectProduct.inl_aut]
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  group

theorem fieldU_scalarU (σ : F ≃+* F) (s : Fˣ) :
    primeFormFieldU hF (isPrimeFormGram_one d) σ (scalarU hF d s) =
      scalarU hF d (Units.map (σ : F →+* F).toMonoidHom s) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_gammaD_action, coe_scalarU, coe_scalarU, GeneralLinearGroup.coe_scalar,
    GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

instance scalarsGamma_normal : (scalarsGamma hF d).Normal := by
  refine ⟨fun n hn x => ?_⟩
  obtain ⟨s, rfl⟩ := hn
  rw [MonoidHom.comp_apply, gammaD_conj_inl, fieldU_scalarU]
  set t := Units.map (x.right : F →+* F).toMonoidHom s
  refine ⟨t, ?_⟩
  rw [MonoidHom.comp_apply]
  congr 1
  have hc : x.left * scalarU hF d t = scalarU hF d t * x.left :=
    Subtype.ext (commute_scalar t (x.left : GL (Fin d) F)).eq
  rw [hc, mul_inv_cancel_right]

end Groups

theorem perm_apply_inv_self {α : Type*} (g : Equiv.Perm α) (x : α) : g (g⁻¹ x) = x :=
  g.apply_symm_apply x

section SemiUnitary

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W]

variable (B : W →ₛₗ[hF.bar] W →ₗ[F] F) in
@[expose] def semiUnitaryGroup : Subgroup (Equiv.Perm W) where
  carrier := {g | (∀ x y, g (x + y) = g x + g y) ∧ ∃ σ : F ≃+* F,
    (∀ (a : F) (x : W), g (a • x) = σ a • g x) ∧ ∀ x y, B (g x) (g y) = σ (B x y)}
  one_mem' := ⟨fun _ _ => rfl, RingEquiv.refl F, fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' {g g'} := by
    rintro ⟨hadd, σ, hσ, hσB⟩ ⟨hadd', σ', hσ', hσ'B⟩
    refine ⟨fun x y => ?_, σ'.trans σ, fun a x => ?_, fun x y => ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hadd', hadd]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ', hσ]
      rfl
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσB, hσ'B]
      rfl
  inv_mem' {g} := by
    rintro ⟨hadd, σ, hσ, hσB⟩
    refine ⟨fun x y => g.injective ?_, σ.symm, fun a x => g.injective ?_, fun x y => ?_⟩
    · rw [hadd, perm_apply_inv_self, perm_apply_inv_self, perm_apply_inv_self]
    · rw [hσ, perm_apply_inv_self, perm_apply_inv_self, RingEquiv.apply_symm_apply]
    · have h := hσB (g⁻¹ x) (g⁻¹ y)
      rw [perm_apply_inv_self, perm_apply_inv_self] at h
      rw [h, RingEquiv.symm_apply_apply]

theorem mem_semiUnitaryGroup {B : W →ₛₗ[hF.bar] W →ₗ[F] F} {g : Equiv.Perm W} :
    g ∈ semiUnitaryGroup B ↔ (∀ x y, g (x + y) = g x + g y) ∧ ∃ σ : F ≃+* F,
      (∀ (a : F) (x : W), g (a • x) = σ a • g x) ∧ ∀ x y, B (g x) (g y) = σ (B x y) :=
  Iff.rfl

variable (F W) in
@[expose] def semiScalars : Subgroup (Equiv.Perm W) :=
  (MulAction.toPermHom Fˣ W).range

instance semiScalars_normal (B : W →ₛₗ[hF.bar] W →ₗ[F] F) :
    ((semiScalars F W).subgroupOf (semiUnitaryGroup B)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨s, hs⟩ := hn
  obtain ⟨-, σ, hσ, -⟩ := g.2
  refine ⟨Units.map (σ : F →+* F).toMonoidHom s, Equiv.ext fun x => ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, ← hs]
  change (Units.map (σ : F →+* F).toMonoidHom s : F) • x =
    (g : Equiv.Perm W) ((s : F) • (g : Equiv.Perm W)⁻¹ x)
  rw [hσ, perm_apply_inv_self, Units.coe_map]
  rfl

end SemiUnitary

section Coordinates

variable {F : Type} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {d : ℕ} (e : Basis (Fin d) F W)

theorem equivFun_basis (i : Fin d) : e.equivFun (e i) = Pi.single i 1 := by
  funext j
  rw [Basis.equivFun_self, Pi.single_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]

theorem form_eq_stdHermForm {B : W →ₛₗ[hF.bar] W →ₗ[F] F}
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) (x y : W) :
    B x y = stdHermForm hF d (e.equivFun x) (e.equivFun y) := by
  have key : B = ((stdHermForm hF d).comp (e.equivFun : W →ₗ[F] Fin d → F)).compl₂
      (e.equivFun : W →ₗ[F] Fin d → F) := by
    refine LinearMap.ext_basis e e fun i j => ?_
    change B (e i) (e j) = stdHermForm hF d (e.equivFun (e i)) (e.equivFun (e j))
    rw [he, equivFun_basis, equivFun_basis, stdHermForm_eq_gramForm, gramForm_single,
      Matrix.one_apply]
  rw [key]
  rfl

@[expose] def glEquiv : LinearMap.GeneralLinearGroup F W ≃* GL (Fin d) F :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv e).toMulEquiv

theorem coe_glEquiv (g : LinearMap.GeneralLinearGroup F W) :
    ((glEquiv e g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      LinearMap.toMatrix e e (g : W →ₗ[F] W) :=
  rfl

theorem equivFun_apply_eq_mulVec (g : LinearMap.GeneralLinearGroup F W) (x : W) :
    e.equivFun ((g : W →ₗ[F] W) x) =
      ((glEquiv e g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ e.equivFun x := by
  rw [coe_glEquiv, Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

theorem mem_sesqUnitaryGroup_iff_glEquiv {B : W →ₛₗ[hF.bar] W →ₗ[F] F}
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) (g : LinearMap.GeneralLinearGroup F W) :
    g ∈ sesqUnitaryGroup B ↔ glEquiv e g ∈ unitaryU hF d := by
  rw [mem_sesqUnitaryGroup, mem_unitaryU]
  set M := ((glEquiv e g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) with hM
  rw [show (M.map hF.bar)ᵀ * M = 1 ↔ (M.map hF.bar)ᵀ * 1 * M = 1 by rw [Matrix.mul_one],
    ← gramForm_isometry_iff hF 1 M]
  constructor
  · intro hg v w
    obtain ⟨x, rfl⟩ := e.equivFun.surjective v
    obtain ⟨y, rfl⟩ := e.equivFun.surjective w
    rw [hM, ← equivFun_apply_eq_mulVec, ← equivFun_apply_eq_mulVec, ← stdHermForm_eq_gramForm,
      ← form_eq_stdHermForm e he, ← form_eq_stdHermForm e he, hg]
  · intro hMiso x y
    rw [form_eq_stdHermForm e he, form_eq_stdHermForm e he, equivFun_apply_eq_mulVec,
      equivFun_apply_eq_mulVec, ← hM, stdHermForm_eq_gramForm, hMiso]

theorem mem_sesqSpecialUnitaryGroup_iff_glEquiv {B : W →ₛₗ[hF.bar] W →ₗ[F] F}
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) (g : LinearMap.GeneralLinearGroup F W) :
    g ∈ sesqSpecialUnitaryGroup B ↔ glEquiv e g ∈ unitarySU 2 1 F d := by
  rw [mem_sesqSpecialUnitaryGroup, mem_unitarySU_iff_unitaryU hF,
    mem_sesqUnitaryGroup_iff_glEquiv e he, coe_glEquiv, LinearMap.det_toMatrix]

end Coordinates

end FourUnitary

universe u

end CFSG.LocalAnalysis.GorensteinLyons
