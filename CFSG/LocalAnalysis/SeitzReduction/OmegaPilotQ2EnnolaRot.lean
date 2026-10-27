module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapGen
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.Sporadic.Schreier.TitsIso

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.RankThree.Classical2 (orthDerived)

section UnitRot

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

structure IsUnitPlane (a a' : Fin d → K) : Prop where
  map_left : Q a = 1
  map_right : Q a' = 1
  polar_eq : polar Q a a' = 1

@[expose] def unitRotFun (a a' : Fin d → K) (p s : K) (v : Fin d → K) : Fin d → K :=
  v + ((p + 1) * polar Q v a' + s * polar Q v a) • a +
    (s * polar Q v a' + (p + s + 1) * polar Q v a) • a'

@[expose] def unitRotLin (a a' : Fin d → K) (p s : K) : (Fin d → K) →ₗ[K] (Fin d → K) where
  toFun := unitRotFun Q a a' p s
  map_add' v w := by
    simp only [unitRotFun, polar_add_left]
    module
  map_smul' c v := by
    simp only [unitRotFun, polar_smul_left, smul_eq_mul, RingHom.id_apply]
    module

variable {Q}

theorem unitRotLin_apply (a a' : Fin d → K) (p s : K) (v : Fin d → K) :
    unitRotLin Q a a' p s v = v + ((p + 1) * polar Q v a' + s * polar Q v a) • a +
      (s * polar Q v a' + (p + s + 1) * polar Q v a) • a' := rfl

theorem unitRotLin_of_perp {a a' v : Fin d → K} (h1 : polar Q v a = 0) (h2 : polar Q v a' = 0)
    (p s : K) : unitRotLin Q a a' p s v = v := by
  rw [unitRotLin_apply, h1, h2]
  simp

theorem unitRotLin_one_zero (a a' v : Fin d → K) : unitRotLin Q a a' 1 0 v = v := by
  have h : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [unitRotLin_apply]
  simp [h]

theorem add_smul_add_smul_add (v a a' : Fin d → K) (c₁ c₂ c₃ c₄ : K) :
    v + c₁ • a + c₂ • a' + c₃ • a + c₄ • a' = v + (c₁ + c₃) • a + (c₂ + c₄) • a' := by
  module

theorem add_smul_add_smul_congr {v a a' : Fin d → K} {X Y X' Y' : K} (hX : X = X') (hY : Y = Y') :
    v + X • a + Y • a' = v + X' • a + Y' • a' := by
  rw [hX, hY]

theorem unitRotLin_conj {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (a a' : Fin d → K) (p s : K)
    (v : Fin d → K) :
    g (unitRotLin Q a a' p s (g.symm v)) = unitRotLin Q (g a) (g a') p s v := by
  have e1 : polar Q (g.symm v) a' = polar Q v (g a') := by
    rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, LinearEquiv.apply_symm_apply]
  have e2 : polar Q (g.symm v) a = polar Q v (g a) := by
    rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, LinearEquiv.apply_symm_apply]
  rw [unitRotLin_apply, unitRotLin_apply, e1, e2, map_add, map_add, map_smul, map_smul,
    LinearEquiv.apply_symm_apply]

namespace IsUnitPlane

variable {a a' : Fin d → K} (h : IsUnitPlane Q a a')
include h

theorem polar_symm : polar Q a' a = 1 := by
  rw [polar_comm]
  exact h.polar_eq

theorem polar_unitRotLin_right (p s : K) (v : Fin d → K) :
    polar Q (unitRotLin Q a a' p s v) a' = p * polar Q v a' + s * polar Q v a := by
  rw [unitRotLin_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    h.polar_eq, polar_self_charTwo, smul_eq_mul, smul_eq_mul]
  grind

theorem polar_unitRotLin_left (p s : K) (v : Fin d → K) :
    polar Q (unitRotLin Q a a' p s v) a = s * polar Q v a' + (p + s) * polar Q v a := by
  rw [unitRotLin_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    h.polar_symm, polar_self_charTwo, smul_eq_mul, smul_eq_mul]
  grind

theorem unitRotLin_comp (p s p' s' : K) (v : Fin d → K) :
    unitRotLin Q a a' p s (unitRotLin Q a a' p' s' v) =
      unitRotLin Q a a' (p * p' + s * s') (p * s' + p' * s + s * s') v := by
  conv_lhs => rw [unitRotLin_apply (Q := Q) a a' p s, h.polar_unitRotLin_right, h.polar_unitRotLin_left,
    unitRotLin_apply, add_smul_add_smul_add]
  rw [unitRotLin_apply]
  exact add_smul_add_smul_congr (by grind) (by grind)

theorem unitRotLin_left (p s : K) : unitRotLin Q a a' p s a = p • a + s • a' := by
  rw [unitRotLin_apply, h.polar_eq, polar_self_charTwo]
  have e : a + ((p + 1) * 1 + s * 0) • a + (s * 1 + (p + s + 1) * 0) • a' =
      (1 + ((p + 1) * 1 + s * 0)) • a + (s * 1 + (p + s + 1) * 0) • a' := by module
  rw [e, show 1 + ((p + 1) * 1 + s * 0) = p by grind, show s * 1 + (p + s + 1) * 0 = s by ring]

theorem unitRotLin_right (p s : K) : unitRotLin Q a a' p s a' = s • a + (p + s) • a' := by
  rw [unitRotLin_apply, h.polar_symm, polar_self_charTwo]
  have e : a' + ((p + 1) * 0 + s * 1) • a + (s * 0 + (p + s + 1) * 1) • a' =
      ((p + 1) * 0 + s * 1) • a + (1 + (s * 0 + (p + s + 1) * 1)) • a' := by module
  rw [e, show (p + 1) * 0 + s * 1 = s by ring, show 1 + (s * 0 + (p + s + 1) * 1) = p + s by grind]

theorem map_unitRotLin {p s : K} (hN : p ^ 2 + p * s + s ^ 2 = 1) (v : Fin d → K) :
    Q (unitRotLin Q a a' p s v) = Q v := by
  rw [unitRotLin_apply]
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_add_left, polar_smul_left,
    polar_smul_right, smul_eq_mul, h.map_left, h.map_right, h.polar_eq]
  grind

theorem unitRotLin_comp_inv {p s : K} (hN : p ^ 2 + p * s + s ^ 2 = 1) (v : Fin d → K) :
    unitRotLin Q a a' p s (unitRotLin Q a a' (p + s) s v) = v := by
  rw [h.unitRotLin_comp, show p * (p + s) + s * s = 1 by grind,
    show p * s + (p + s) * s + s * s = 0 by grind, unitRotLin_one_zero]

theorem unitRotLin_inv_comp {p s : K} (hN : p ^ 2 + p * s + s ^ 2 = 1) (v : Fin d → K) :
    unitRotLin Q a a' (p + s) s (unitRotLin Q a a' p s v) = v := by
  rw [h.unitRotLin_comp, show (p + s) * p + s * s = 1 by grind,
    show (p + s) * s + p * s + s * s = 0 by grind, unitRotLin_one_zero]

@[expose] noncomputable def unitRotEquiv {p s : K} (hN : p ^ 2 + p * s + s ^ 2 = 1) :
    (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  LinearEquiv.ofLinearMap (unitRotLin Q a a' p s) (unitRotLin Q a a' (p + s) s)
    (LinearMap.ext fun v => h.unitRotLin_comp_inv hN v)
    (LinearMap.ext fun v => h.unitRotLin_inv_comp hN v)

theorem unitRotEquiv_apply {p s : K} (hN : p ^ 2 + p * s + s ^ 2 = 1) (v : Fin d → K) :
    h.unitRotEquiv hN v = unitRotLin Q a a' p s v := rfl

theorem unitRotEquiv_mem_orthogonalGroup {p s : K} (hN : p ^ 2 + p * s + s ^ 2 = 1) :
    h.unitRotEquiv hN ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => h.map_unitRotLin hN v

end IsUnitPlane

theorem IsAnisoCoord.unitRotLin_eq_anisoRotLin {a a' : Fin d} (h : IsAnisoCoord Q a a' 1 1)
    (p s : K) (v : Fin d → K) :
    unitRotLin Q (Pi.single a 1) (Pi.single a' 1) p s v = anisoRotLin a a' 1 1 p s v := by
  have e1 : polar Q v (Pi.single a' 1) = v a := by rw [polar_comm, h.polar_right, one_mul]
  have e2 : polar Q v (Pi.single a 1) = v a' := by rw [polar_comm, h.polar_left, one_mul]
  rw [unitRotLin_apply, e1, e2]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, anisoRotLin_apply]
  by_cases hia : i = a
  · subst hia
    simp [h.ne]
    grind
  · by_cases hib : i = a'
    · subst hib
      simp [h.ne.symm]
      grind
    · simp [hia, hib]

end UnitRot

section Param

variable {K F : Type} [Field K] [Field F]

structure EnnolaParam (K F : Type) [Field K] [Field F] where
  ι : K →+* F
  ω : F
  sq : ω * ω = ω + 1
  bij : Function.Bijective fun z : K × K => ι z.1 + ι z.2 * ω
  two : ∀ p : K, p = 0 ∨ p = 1
  cube : ∀ x : Fˣ, x ^ 3 = 1

namespace EnnolaParam

variable (E : EnnolaParam K F)

@[expose] noncomputable def param (x : F) : K × K := (Equiv.ofBijective _ E.bij).symm x

theorem ell_param (x : F) : E.ι (E.param x).1 + E.ι (E.param x).2 * E.ω = x :=
  (Equiv.ofBijective _ E.bij).apply_symm_apply x

theorem param_eq_iff {x : F} {z : K × K} : E.param x = z ↔ E.ι z.1 + E.ι z.2 * E.ω = x := by
  constructor
  · rintro rfl
    exact E.ell_param x
  · rintro rfl
    exact (Equiv.ofBijective _ E.bij).symm_apply_apply z

theorem ell_mul (p s p' s' : K) :
    (E.ι p + E.ι s * E.ω) * (E.ι p' + E.ι s' * E.ω) =
      E.ι (p * p' + s * s') + E.ι (p * s' + p' * s + s * s') * E.ω := by
  simp only [map_add, map_mul]
  linear_combination (E.ι s * E.ι s') * E.sq

theorem param_mul (x y : F) : E.param (x * y) =
    ((E.param x).1 * (E.param y).1 + (E.param x).2 * (E.param y).2,
      (E.param x).1 * (E.param y).2 + (E.param y).1 * (E.param x).2 +
        (E.param x).2 * (E.param y).2) := by
  rw [param_eq_iff, ← E.ell_mul, E.ell_param, E.ell_param]

theorem param_one : E.param 1 = (1, 0) := by
  rw [param_eq_iff]
  simp

variable [CharP K 2]

theorem norm_param {x : F} (hx : x ≠ 0) :
    (E.param x).1 ^ 2 + (E.param x).1 * (E.param x).2 + (E.param x).2 ^ 2 = 1 := by
  have hz : E.param x ≠ (0, 0) := fun h0 => hx (by rw [← E.ell_param x, h0]; simp)
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rcases E.two (E.param x).1 with h1 | h1 <;> rcases E.two (E.param x).2 with h2 | h2
  · exact absurd (Prod.ext h1 h2) hz
  · rw [h1, h2]
    ring
  · rw [h1, h2]
    ring
  · rw [h1, h2]
    linear_combination h11

include E in
theorem two_eq_zero_F : (2 : F) = 0 := by
  rw [← map_ofNat E.ι 2, CharTwo.two_eq_zero, map_zero]

theorem ell_conj_param {x : F} (hx : x ≠ 0) :
    E.ι (E.param x).1 + E.ι (E.param x).2 * (E.ω + 1) = x⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  have hN := congrArg E.ι (E.norm_param hx)
  simp only [map_add, map_mul, map_pow, map_one] at hN
  have h2 := E.two_eq_zero_F
  set p := (E.param x).1
  set s := (E.param x).2
  have hx' : E.ι p + E.ι s * E.ω = x := E.ell_param x
  rw [← hx']
  linear_combination hN + E.ι s ^ 2 * E.sq + (E.ι p * E.ι s * E.ω + E.ι s ^ 2 * E.ω) * h2

variable {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' : Fin d → K}

@[expose] noncomputable def rotHom (h : IsUnitPlane Q a a') :
    Fˣ →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) where
  toFun x := h.unitRotEquiv (E.norm_param x.ne_zero)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    rw [h.unitRotEquiv_apply, Units.val_one, E.param_one]
    exact unitRotLin_one_zero a a' v
  map_mul' x y := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, h.unitRotEquiv_apply, h.unitRotEquiv_apply, h.unitRotEquiv_apply,
      h.unitRotLin_comp, Units.val_mul, E.param_mul]

theorem rotHom_apply (h : IsUnitPlane Q a a') (x : Fˣ) (v : Fin d → K) :
    E.rotHom h x v = unitRotLin Q a a' (E.param x).1 (E.param x).2 v := rfl

theorem rotHom_mem_orthogonalGroup (h : IsUnitPlane Q a a') (x : Fˣ) :
    E.rotHom h x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  h.unitRotEquiv_mem_orthogonalGroup (E.norm_param x.ne_zero)

theorem rotHom_left (h : IsUnitPlane Q a a') (x : Fˣ) :
    E.rotHom h x a = (E.param x).1 • a + (E.param x).2 • a' :=
  h.unitRotLin_left _ _

theorem rotHom_right (h : IsUnitPlane Q a a') (x : Fˣ) :
    E.rotHom h x a' = (E.param x).2 • a + ((E.param x).1 + (E.param x).2) • a' :=
  h.unitRotLin_right _ _

theorem rotHom_of_perp (h : IsUnitPlane Q a a') (x : Fˣ) {v : Fin d → K}
    (h1 : polar Q v a = 0) (h2 : polar Q v a' = 0) : E.rotHom h x v = v :=
  unitRotLin_of_perp h1 h2 _ _

theorem rotHom_mem_orthDerived [Finite K] (h : IsUnitPlane Q a a')
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (x : Fˣ) :
    E.rotHom h x ∈ orthDerived Q := by
  have hx : x = x ^ 2 * x ^ 2 := by
    rw [← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, E.cube, one_mul]
  set g := E.rotHom h (x ^ 2) with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := E.rotHom_mem_orthogonalGroup h _
  have hgg : E.rotHom h x = g * g := by
    rw [hg, ← map_mul, ← hx]
  rw [hgg]
  apply CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  refine CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨mul_mem hgO hgO, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff_even,
    CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hgO hgO]
  exact CharTwo.add_self_eq_zero _

end EnnolaParam

end Param

end CFSG.SeitzReduction.OmegaPilot
