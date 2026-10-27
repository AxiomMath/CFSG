module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryScalarCentralizer

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Module CFSG.LinearAlgebra QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

namespace FourUnitary

section Scalars

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W]

variable (F W) in
@[expose] def scalarGL : Fˣ →* LinearMap.GeneralLinearGroup F W :=
  Units.map (algebraMap F (Module.End F W)).toMonoidHom

theorem scalarGL_apply (s : Fˣ) (x : W) :
    ((scalarGL F W s : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) x = (s : F) • x :=
  Module.algebraMap_end_apply F F W (s : F) x

theorem scalarGL_commute (s : Fˣ) (g : LinearMap.GeneralLinearGroup F W) :
    g * scalarGL F W s = scalarGL F W s * g :=
  Units.ext (LinearMap.ext fun x => by
    simp only [Units.val_mul, Module.End.mul_apply, scalarGL_apply, map_smul])

variable (B : W →ₛₗ[hF.bar] W →ₗ[F] F)

@[expose] def suScalars (hsc : ∀ s : Fˣ, scalarGL F W s ∈ sesqSpecialUnitaryGroup B) :
    Subgroup (sesqSpecialUnitaryGroup B) :=
  ((scalarGL F W).codRestrict _ hsc).range

instance suScalars_normal (hsc : ∀ s : Fˣ, scalarGL F W s ∈ sesqSpecialUnitaryGroup B) :
    (suScalars B hsc).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨s, rfl⟩ := hn
  refine ⟨s, Subtype.ext ?_⟩
  change scalarGL F W s = (g : LinearMap.GeneralLinearGroup F W) * scalarGL F W s *
    (g : LinearMap.GeneralLinearGroup F W)⁻¹
  rw [scalarGL_commute, mul_inv_cancel_right]

end Scalars

end FourUnitary

namespace OrderThreeHermitian

open FourUnitary

theorem natCard_omegaField : Nat.card OmegaField = 4 := by
  have : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_omegaField, Nat.card_zmod]
  norm_num

theorem unitaryFieldData_omegaField : UnitaryFieldData 2 1 OmegaField :=
  ⟨Nat.prime_two, le_rfl, by rw [natCard_omegaField]; norm_num⟩

theorem omega_ne_zero : omega ≠ 0 := by
  intro h
  have h2 := omega_sq
  rw [h, zero_pow two_ne_zero, zero_add] at h2
  exact zero_ne_one h2

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  have h2 := omega_sq
  rw [h, one_pow, one_add_one_eq_two, omegaField_two_eq_zero] at h2
  exact one_ne_zero h2

theorem eq_one_or_omega (s : OmegaField) (hs : s ≠ 0) : s = 1 ∨ s = omega ∨ s = omega ^ 2 := by
  rcases eq_zero_or_one_or_of_ne unitaryFieldData_omegaField omega_ne_zero omega_ne_one s with
    h | h | h | h
  · exact absurd h hs
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def fixedSpace (c : Module.End (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.ker (c - 1)

@[expose] def movedSpace (c : Module.End (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.range (c - 1)

@[expose] def traceEnd (c : Module.End (ZMod 2) V) : Module.End (ZMod 2) V :=
  1 + c + c ^ 2

theorem apply_mem_movedSpace (c : Module.End (ZMod 2) V) {w : V} (hw : w ∈ movedSpace c) :
    c w ∈ movedSpace c := by
  obtain ⟨v, rfl⟩ := hw
  refine ⟨c v, ?_⟩
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]

theorem sq_add_self_add_one_on_moved {c : Module.End (ZMod 2) V} (hc : c ^ 3 = 1) {w : V}
    (hw : w ∈ movedSpace c) : c (c w) + c w + w = 0 := by
  obtain ⟨v, rfl⟩ := hw
  have h3 : c (c (c v)) = v := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_two, ← pow_succ, hc,
      Module.End.one_apply]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, h3]
  abel

@[expose] def MovedSpace (c : Module.End (ZMod 2) V) (_hc : c ^ 3 = 1) : Type _ :=
  movedSpace c

variable {c : Module.End (ZMod 2) V} {hc : c ^ 3 = 1}

instance : AddCommGroup (MovedSpace c hc) :=
  inferInstanceAs (AddCommGroup (movedSpace c))

instance : Module (ZMod 2) (MovedSpace c hc) :=
  inferInstanceAs (Module (ZMod 2) (movedSpace c))

variable (c hc) in
@[expose] def toV : MovedSpace c hc →ₗ[ZMod 2] V :=
  (movedSpace c).subtype

theorem toV_injective : Function.Injective (toV c hc) :=
  Subtype.val_injective

theorem toV_mem (x : MovedSpace c hc) : toV c hc x ∈ movedSpace c :=
  (x : movedSpace c).2

variable (c hc) in
@[expose] def restrictC : Module.End (ZMod 2) (MovedSpace c hc) :=
  c.restrict fun _ hw => apply_mem_movedSpace c hw

theorem toV_restrictC (x : MovedSpace c hc) : toV c hc (restrictC c hc x) = c (toV c hc x) :=
  rfl

theorem restrictC_rel : restrictC c hc ^ 2 + restrictC c hc + 1 = 0 := by
  refine LinearMap.ext fun x => toV_injective ?_
  simp only [LinearMap.add_apply, pow_two, Module.End.mul_apply, Module.End.one_apply, map_add,
    toV_restrictC, LinearMap.zero_apply, map_zero]
  exact sq_add_self_add_one_on_moved hc (toV_mem x)

instance : Module OmegaField (MovedSpace c hc) :=
  Module.compHom _ (omegaHom (restrictC c hc) restrictC_rel)

theorem smul_def (a : OmegaField) (x : MovedSpace c hc) :
    a • x = omegaHom (restrictC c hc) restrictC_rel a x :=
  rfl

theorem toV_omega_smul (x : MovedSpace c hc) : toV c hc (omega • x) = c (toV c hc x) := by
  rw [smul_def, omegaHom_omega, toV_restrictC]

theorem algebraMap_smul' (a : ZMod 2) (x : MovedSpace c hc) :
    algebraMap (ZMod 2) OmegaField a • x = a • x := by
  rw [smul_def, omegaHom_algebraMap, Module.algebraMap_end_apply]

@[expose] def orderThreeForm (q : QuadraticForm (ZMod 2) V) (c : Module.End (ZMod 2) V)
    (hc : c ^ 3 = 1) (x y : MovedSpace c hc) : OmegaField :=
  omega ^ 2 * algebraMap (ZMod 2) OmegaField (polar q (toV c hc x) (toV c hc y)) +
    algebraMap (ZMod 2) OmegaField (polar q (toV c hc x) (c (toV c hc y)))

end OrderThreeHermitian

end CFSG.LocalAnalysis.GorensteinLyons
