module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Models
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Module Matrix Polynomial CFSG.QuasithinUnique.Setup.Family

theorem isSimpleGroup_gl32 : IsSimpleGroup GL32 := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (e₁.trans e₂).symm.isSimpleGroup

@[expose] def x0Mat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def x0InvMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def x0 : GL32 := ⟨x0Mat, x0InvMat, by decide, by decide⟩

theorem x0_val : ((x0 : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = x0Mat := rfl

theorem x0_inv_val : ((x0⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = x0InvMat := rfl

theorem x0_pow_seven : x0 ^ 7 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, x0_val, Units.val_one]; decide)

theorem x0_ne_one : x0 ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : GL32 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  simp only [x0_val, Units.val_one] at h1
  exact absurd h1 (by decide)

theorem orderOf_x0 : orderOf x0 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime x0_pow_seven x0_ne_one

@[expose] noncomputable def fL : (ZMod 2)[X] := X ^ 3 + X + 1

@[expose] noncomputable def gL : (ZMod 2)[X] := X ^ 4 + X ^ 2 + X + 1

theorem isCoprime_fL_gL : IsCoprime fL gL := ⟨-X, 1, by unfold fL gL; ring⟩

theorem fL_mul_gL : fL * gL = X ^ 7 + 1 := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
  unfold fL gL
  linear_combination (X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X) * h2

theorem aeval_fL_apply {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (T : Module.End (ZMod 2) M) (v : M) : aeval T fL v = T (T (T v)) + T v + v := by
  simp [fL, pow_succ, Module.End.mul_apply]

theorem aeval_fL_mul_gL_eq_zero {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    {T : Module.End (ZMod 2) M} (hT : T ^ 7 = 1) : aeval T (fL * gL) = 0 := by
  rw [fL_mul_gL]
  simp only [map_add, map_pow, aeval_X, map_one, hT]
  ext v
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.zero_apply]
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

section Conj

variable {K : Type*} [Field K] {E E' : Type*} [AddCommMonoid E] [Module K E] [AddCommMonoid E']
  [Module K E']

theorem apply_aeval_of_intertwine (φ : E →ₗ[K] E') {T : Module.End K E} {T' : Module.End K E'}
    (h : ∀ v, φ (T v) = T' (φ v)) (p : K[X]) (v : E) :
    φ (aeval T p v) = aeval T' p (φ v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    congr 1
    induction n generalizing v with
    | zero => simp
    | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, h, pow_succ, Module.End.mul_apply]

theorem finrank_ker_aeval_eq_of_equiv (e : E ≃ₗ[K] E') {T : Module.End K E}
    {T' : Module.End K E'} (h : ∀ v, e (T v) = T' (e v)) (p : K[X]) :
    finrank K ↥(LinearMap.ker (aeval T' p)) = finrank K ↥(LinearMap.ker (aeval T p)) := by
  have hmap : (LinearMap.ker (aeval T p)).map (e : E →ₗ[K] E') = LinearMap.ker (aeval T' p) := by
    ext w
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have h1 := apply_aeval_of_intertwine (e : E →ₗ[K] E') h p v
      simp only [LinearEquiv.coe_coe] at h1
      rw [← h1, hv, map_zero]
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      have h1 := apply_aeval_of_intertwine (e : E →ₗ[K] E') h p (e.symm w)
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
      rw [hw] at h1
      exact e.injective (by rw [h1, map_zero])
  rw [← hmap]
  exact (LinearEquiv.finrank_map_eq e _)

end Conj

theorem finrank_ker_fL_repV_x0 :
    finrank (ZMod 2) ↥(LinearMap.ker (aeval ((repV x0 : Vec3 ≃ₗ[ZMod 2] Vec3) :
      Module.End (ZMod 2) Vec3) fL)) = 3 := by
  have h : LinearMap.ker (aeval ((repV x0 : Vec3 ≃ₗ[ZMod 2] Vec3) :
      Module.End (ZMod 2) Vec3) fL) = ⊤ := by
    rw [eq_top_iff]
    intro v hv
    clear hv
    rw [LinearMap.mem_ker, aeval_fL_apply]
    simp only [LinearEquiv.coe_coe, repV_apply, x0_val]
    revert v
    decide
  rw [h, finrank_top]
  simp

theorem finrank_ker_fL_repV_x0_inv :
    finrank (ZMod 2) ↥(LinearMap.ker (aeval ((repV x0⁻¹ : Vec3 ≃ₗ[ZMod 2] Vec3) :
      Module.End (ZMod 2) Vec3) fL)) = 0 := by
  have h : LinearMap.ker (aeval ((repV x0⁻¹ : Vec3 ≃ₗ[ZMod 2] Vec3) :
      Module.End (ZMod 2) Vec3) fL) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, aeval_fL_apply] at hv
    simp only [LinearEquiv.coe_coe, repV_apply, x0_inv_val] at hv
    rw [Submodule.mem_bot]
    revert v
    decide
  rw [h, finrank_bot]

theorem finrank_ker_fL_repDual_x0 :
    finrank (ZMod 2) ↥(LinearMap.ker (aeval ((repDual x0 : Vec3 ≃ₗ[ZMod 2] Vec3) :
      Module.End (ZMod 2) Vec3) fL)) = 0 := by
  have h : LinearMap.ker (aeval ((repDual x0 : Vec3 ≃ₗ[ZMod 2] Vec3) :
      Module.End (ZMod 2) Vec3) fL) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, aeval_fL_apply] at hv
    simp only [LinearEquiv.coe_coe, repDual_apply, x0_inv_val] at hv
    rw [Submodule.mem_bot]
    revert v
    decide
  rw [h, finrank_bot]

theorem finrank_ker_fL_repDual_x0_inv :
    finrank (ZMod 2) ↥(LinearMap.ker (aeval ((repDual x0⁻¹ : Vec3 ≃ₗ[ZMod 2] Vec3) :
      Module.End (ZMod 2) Vec3) fL)) = 3 := by
  have h : LinearMap.ker (aeval ((repDual x0⁻¹ : Vec3 ≃ₗ[ZMod 2] Vec3) :
      Module.End (ZMod 2) Vec3) fL) = ⊤ := by
    rw [eq_top_iff]
    intro v hv
    clear hv
    rw [LinearMap.mem_ker, aeval_fL_apply]
    simp only [LinearEquiv.coe_coe, repDual_apply, inv_inv, x0_val]
    revert v
    decide
  rw [h, finrank_top]
  simp

section KerDim

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem kerDim_le_kerDim_conj (ρ : Representation (ZMod 2) G W) (p : (ZMod 2)[X]) (x h : G)
    (U : Submodule (ZMod 2) W) (hU : ∀ u ∈ U, ρ h u ∈ U) :
    kerDim ρ p x U ≤ kerDim ρ p (h * x * h⁻¹) U := by
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hint : ∀ v, ρ h (ρ x v) = ρ (h * x * h⁻¹) (ρ h v) := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have hmaps : ∀ v ∈ U ⊓ LinearMap.ker (aeval (ρ x) p),
      ρ h v ∈ U ⊓ LinearMap.ker (aeval (ρ (h * x * h⁻¹)) p) := by
    intro v hv
    refine ⟨hU v hv.1, ?_⟩
    show aeval (ρ (h * x * h⁻¹)) p (ρ h v) = 0
    rw [← apply_aeval_of_intertwine (ρ h) hint p v]
    have h0 : aeval (ρ x) p v = 0 := hv.2
    rw [h0, map_zero]
  set φ := (ρ h).restrict hmaps with hφ
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : ρ h (a : W) = ρ h (b : W) := congrArg Subtype.val hab
    have h2 : ρ h⁻¹ (ρ h (a : W)) = ρ h⁻¹ (ρ h (b : W)) := by rw [h1]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one] at h2
    exact Subtype.ext h2
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem kerDim_conj (ρ : Representation (ZMod 2) G W) (p : (ZMod 2)[X]) (x h : G)
    (U : Submodule (ZMod 2) W) (hU : ∀ u ∈ U, ρ h u ∈ U) (hU' : ∀ u ∈ U, ρ h⁻¹ u ∈ U) :
    kerDim ρ p (h * x * h⁻¹) U = kerDim ρ p x U := by
  refine le_antisymm ?_ (kerDim_le_kerDim_conj ρ p x h U hU)
  have := kerDim_le_kerDim_conj ρ p (h * x * h⁻¹) h⁻¹ U hU'
  rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this

omit [Finite W] in
theorem kerDim_bot (ρ : Representation (ZMod 2) G W) (p : (ZMod 2)[X]) (x : G) :
    kerDim ρ p x ⊥ = 0 := by
  unfold kerDim
  rw [bot_inf_eq, finrank_bot]

end KerDim

section InnImg

variable {G : Type*} [Group G]

theorem conj_mem_centralizer {L : Subgroup G} {l c : G} (hl : l ∈ L)
    (hc : c ∈ Subgroup.centralizer (L : Set G)) :
    l⁻¹ * c * l ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro k hk
  have h1 := hc (l * k * l⁻¹) (L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl))
  calc k * (l⁻¹ * c * l) = l⁻¹ * ((l * k * l⁻¹) * c) * l := by group
    _ = l⁻¹ * (c * (l * k * l⁻¹)) * l := by rw [h1]
    _ = l⁻¹ * c * l * k := by group

@[expose] def innImg (L B : Subgroup G) (eL : ↥L ≃* GL32) : Subgroup GL32 where
  carrier := {g | ∃ b ∈ B, ((eL.symm g : ↥L) : G)⁻¹ * b ∈ Subgroup.centralizer (L : Set G)}
  mul_mem' := by
    rintro g₁ g₂ ⟨b₁, hb₁, h₁⟩ ⟨b₂, hb₂, h₂⟩
    refine ⟨b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    rw [map_mul, Subgroup.coe_mul]
    have e : (((eL.symm g₁ : ↥L) : G) * ((eL.symm g₂ : ↥L) : G))⁻¹ * (b₁ * b₂) =
        (((eL.symm g₂ : ↥L) : G)⁻¹ * (((eL.symm g₁ : ↥L) : G)⁻¹ * b₁) *
          ((eL.symm g₂ : ↥L) : G)) * (((eL.symm g₂ : ↥L) : G)⁻¹ * b₂) := by group
    rw [e]
    exact Subgroup.mul_mem _ (conj_mem_centralizer (eL.symm g₂).2 h₁) h₂
  one_mem' := ⟨1, B.one_mem, by simp⟩
  inv_mem' := by
    rintro g ⟨b, hb, h⟩
    refine ⟨b⁻¹, B.inv_mem hb, ?_⟩
    rw [map_inv, Subgroup.coe_inv, inv_inv]
    have e : ((eL.symm g : ↥L) : G) * b⁻¹ =
        ((eL.symm g : ↥L) : G)⁻¹⁻¹ * (((eL.symm g : ↥L) : G)⁻¹ * b)⁻¹ *
          ((eL.symm g : ↥L) : G)⁻¹ := by group
    rw [e]
    exact conj_mem_centralizer (L.inv_mem (eL.symm g).2) (Subgroup.inv_mem _ h)

theorem mem_innImg_iff {L B : Subgroup G} {eL : ↥L ≃* GL32} {g : GL32} :
    g ∈ innImg L B eL ↔ ∃ b ∈ B, ∀ k ∈ L,
      b * k * b⁻¹ = ((eL.symm g : ↥L) : G) * k * ((eL.symm g : ↥L) : G)⁻¹ := by
  set l : G := ((eL.symm g : ↥L) : G) with hl
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, fun k hk => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp h k hk
    calc b * k * b⁻¹ = l * (l⁻¹ * b * k) * b⁻¹ := by group
      _ = l * (k * (l⁻¹ * b)) * b⁻¹ := by rw [h1]
      _ = l * k * l⁻¹ := by group
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have h1 := h k hk
    calc k * (l⁻¹ * b) = l⁻¹ * (l * k * l⁻¹) * b := by group
      _ = l⁻¹ * (b * k * b⁻¹) * b := by rw [h1]
      _ = l⁻¹ * b * k := by group

end InnImg

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
