module

public import CFSG.Fischer.Classification.PartII.O2Field
public import CFSG.Fischer.Classification.PartII.Herm.Classify
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace O2Mod

@[expose] def toF4 (x : ZMod 2) : F4 := if x = 0 then 0 else 1

theorem toF4_add : ∀ x y : ZMod 2, toF4 (x + y) = toF4 x + toF4 y := by decide

theorem f4_smul_identity : ∀ (d : F4) (x y : ZMod 2),
    F4.ω * toF4 (F4.re d * x + F4.im d * y) + toF4 (F4.re d * y + F4.im d * (y + x)) =
      d ^ 2 * (F4.ω * toF4 x + toF4 y) := by
  decide

theorem f4_conj_identity : ∀ x y : ZMod 2,
    F4.ω * toF4 x + toF4 (y + x) = (F4.ω * toF4 x + toF4 y) ^ 2 := by
  decide

theorem f4_nondeg : ∀ x y : ZMod 2, F4.ω * toF4 x + toF4 y = 0 → x = 0 := by decide

theorem omega_toF4_eq_zero_iff : ∀ x y : ZMod 2, F4.ω * toF4 x + toF4 y = 0 ↔ x = 0 ∧ y = 0 := by
  decide

theorem omega_toF4_eq_one_iff : ∀ x y : ZMod 2, F4.ω * toF4 x + toF4 y = 1 ↔ x = 0 ∧ y = 1 := by
  decide

section Form

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (J : V →ₗ[ZMod 2] V)
  (hJ : ∀ v, J (J v) = J v + v) (b : LinearMap.BilinForm (ZMod 2) V)

@[expose, reducible] def kModule : Module K V where
  smul c v := f4End J hJ (eF4.symm c) v
  one_smul v := by
    show f4End J hJ (eF4.symm 1) v = v
    rw [map_one, map_one, Module.End.one_apply]
  mul_smul c d v := by
    show f4End J hJ (eF4.symm (c * d)) v = f4End J hJ (eF4.symm c) (f4End J hJ (eF4.symm d) v)
    rw [map_mul, map_mul, Module.End.mul_apply]
  smul_zero c := map_zero _
  smul_add c u v := map_add _ u v
  add_smul c d v := by
    show f4End J hJ (eF4.symm (c + d)) v = f4End J hJ (eF4.symm c) v + f4End J hJ (eF4.symm d) v
    rw [map_add, map_add, LinearMap.add_apply]
  zero_smul v := by
    show f4End J hJ (eF4.symm 0) v = 0
    rw [map_zero, map_zero, LinearMap.zero_apply]

@[expose] def hF4 (u v : V) : F4 := F4.ω * toF4 (b u v) + toF4 (b (J u) v)

@[expose] def hform (u v : V) : K := eF4 (hF4 J b u v)

variable (hb : ∀ u v, b u v = b v u) (hbJ : ∀ u v, b (J u) (J v) = b u v)

include hJ hbJ in
theorem form_J_right (u v : V) : b u (J v) = b (J u) v + b u v := by
  have hu : J (J u + u) = u := by
    rw [map_add, hJ]
    calc J u + u + J u = u + (J u + J u) := by abel
      _ = u := by rw [Symplectic.zmod_two_add_self, add_zero]
  calc b u (J v) = b (J (J u + u)) (J v) := by rw [hu]
    _ = b (J u) v + b u v := by rw [hbJ, map_add, LinearMap.add_apply]

include hJ in
theorem kModule_smul_eq (c : K) (v : V) :
    (kModule J hJ).toSMul.smul c v =
      F4.re (eF4.symm c) • v + F4.im (eF4.symm c) • J v := rfl

include hJ in
theorem kModule_omega (v : V) : (kModule J hJ).toSMul.smul ω v = J v := by
  rw [kModule_smul_eq, omega_eq, RingEquiv.symm_apply_apply, F4.re_ω, F4.im_ω, zero_smul,
    one_smul, zero_add]

include hJ hb hbJ in
theorem isHermForm_hform :
    letI := kModule J hJ
    Herm.IsHermForm frob (hform J b) := by
  let _ := kModule J hJ
  refine ⟨fun x x' y => ?_, fun c x y => ?_, fun x y => ?_⟩
  · simp only [hform, hF4, map_add, LinearMap.add_apply, toF4_add, mul_add]
    abel
  · obtain ⟨d, rfl⟩ := eF4.surjective c
    have hc : eF4 d • x = F4.re d • x + F4.im d • J x := by
      show (kModule J hJ).toSMul.smul (eF4 d) x = _
      rw [kModule_smul_eq, RingEquiv.symm_apply_apply]
    have h1 : b (eF4 d • x) y = F4.re d * b x y + F4.im d * b (J x) y := by
      rw [hc, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    have h2 : b (J (eF4 d • x)) y =
        F4.re d * b (J x) y + F4.im d * (b (J x) y + b x y) := by
      simp only [hc, map_add, map_smul, hJ, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul]
    rw [hform, hF4, h1, h2, f4_smul_identity, map_mul, frob_apply, map_pow]
    rfl
  · have h1 : b (J y) x = b (J x) y + b x y := by
      rw [hb, form_J_right J hJ b hbJ]
    rw [hform, hform, frob_eF4, hF4, hF4, hb y x, h1, f4_conj_identity]

theorem hform_nondegenerate (hnd : ∀ u, (∀ v, b u v = 0) → u = 0) (u : V)
    (hu : ∀ v, hform J b u v = 0) : u = 0 :=
  hnd u fun v => f4_nondeg _ _ (by
    have := hu v
    rw [hform, ← map_zero eF4, eF4_inj] at this
    exact this)

include hJ hb hbJ in
theorem exists_hermEquiv [Finite V] (hnd : ∀ u, (∀ v, b u v = 0) → u = 0) :
    ∃ (N : ℕ) (ξ : V ≃+ (Fin N → K)), (∀ v, ξ (J v) = ω • ξ v) ∧
      ∀ u v, herm frob (ξ u) (ξ v) = hform J b u v := by
  let _ := kModule J hJ
  have : Module.Finite K V := Module.Finite.of_finite
  obtain ⟨e, he⟩ := exists_linearEquiv_herm_of_form isUnitaryInvolution_frob
    (isHermForm_hform J hJ b hb hbJ) (hform_nondegenerate J b hnd) rfl
  refine ⟨_, e.toAddEquiv, fun v => ?_, he⟩
  have hv : J v = ω • v := (kModule_omega J hJ v).symm
  show e (J v) = ω • e v
  rw [hv, e.map_smul]

end Form

variable {H : Type} [Group H] {E μ : Set H}

instance instFiniteSecModule (E μ : Set H) [Finite H] : Finite (SecModule E μ) :=
  Module.finite_of_finite (ZMod 2)

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E) (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4)
include hμ hP h4

theorem exists_hermEquiv :
    ∃ (N : ℕ) (ξ : SecModule E μ ≃+ (Fin N → K)), (∀ v, ξ (hμ.jmod hP h4 v) = ω • ξ v) ∧
      ∀ u v, herm frob (ξ u) (ξ v) = hform (hμ.jmod hP h4) (secForm hP) u v := by
  have := Pair.finite hP
  exact O2Mod.exists_hermEquiv (hμ.jmod hP h4) (hμ.jmod_jmod hP h4) (secForm hP)
    (secForm_comm hP) (hμ.secForm_jmod hP h4) (secForm_nondegenerate hP)

end IsTwinSection

end O2Mod

end CFSG.Fischer.Classification
