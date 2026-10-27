module

public import CFSG.LargeExtraspecial.PSL10Fix
public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.PSLPSU10

open Subgroup CFSG.Open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

@[expose] noncomputable def suEnd (B : W →ₛₗ[hF.bar] W →ₗ[F] F) :
    sesqSpecialUnitaryGroup B →* Module.End F W :=
  (Units.coeHom (Module.End F W)).comp (sesqSpecialUnitaryGroup B).subtype

theorem suEnd_injective : Function.Injective (suEnd B) := fun _ _ h => Subtype.ext (Units.ext h)

theorem suEnd_isometry (g : sesqSpecialUnitaryGroup B) (x y : W) :
    B (suEnd B g x) (suEnd B g y) = B x y :=
  (mem_sesqSpecialUnitaryGroup.mp g.2).1 x y

theorem add_self_of_unitaryFieldData (hF : UnitaryFieldData 2 1 F) (w : W) : w + w = 0 := by
  have : CharP F 2 := hF.charP
  rw [← two_smul F w, CharTwo.two_eq_zero, zero_smul]

theorem end_add_self_of_unitaryFieldData (hF : UnitaryFieldData 2 1 F) (X : Module.End F W) :
    X + X = 0 :=
  LinearMap.ext fun w => add_self_of_unitaryFieldData hF (X w)

theorem exists_eq_hermTransvection [FiniteDimensional F W] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {t : sesqSpecialUnitaryGroup B} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hP : IsPGroup 2 (timmesfeldFStar (centralizer ({t} : Set (sesqSpecialUnitaryGroup B)))))
    (hZ : Nat.card (center (timmesfeldFStar
      (centralizer ({t} : Set (sesqSpecialUnitaryGroup B))))) = 2) :
    ∃ w : W, w ≠ 0 ∧ B w w = 0 ∧ suEnd B t = hermTransvection B w 1 := by
  have : Finite F := hF.finite
  have : CharP F 2 := hF.charP
  have : Finite W := Module.finite_of_finite F
  have : Finite (W →ₗ[F] W) := Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨D, hD⟩ : ∃ D, suEnd B t - 1 = D := ⟨_, rfl⟩
  have hTT : suEnd B t * suEnd B t = 1 := by rw [← map_mul, ht, map_one]
  have hDD' : (suEnd B t - 1) * (suEnd B t - 1) = 0 := by
    have e : (suEnd B t - 1) * (suEnd B t - 1) =
        (suEnd B t * suEnd B t + 1) - (suEnd B t + suEnd B t) := by noncomm_ring
    rw [e, hTT, end_add_self_of_unitaryFieldData hF, end_add_self_of_unitaryFieldData hF,
      sub_zero]
  have hDD : D * D = 0 := hD ▸ hDD'
  have hcomm : ∀ c : centralizer ({t} : Set (sesqSpecialUnitaryGroup B)),
      D * suEnd B c = suEnd B c * D := fun c => hD ▸ sub_one_mul_map_of_mem (suEnd B) c
  have hD0 : D ≠ 0 := by
    rintro rfl
    exact ht1 (suEnd_injective (by rw [map_one]; exact sub_eq_zero.mp hD))
  have hTx : ∀ x, suEnd B t (suEnd B t x) = x := fun x => by
    rw [← Module.End.mul_apply, hTT, Module.End.one_apply]
  have hDx : ∀ x, D x = suEnd B t x - x := fun x => by rw [← hD]; rfl
  have hDadj : ∀ x y, B (D x) y = B x (D y) := by
    intro x y
    have h1 : B (suEnd B t x) y = B x (suEnd B t y) := by
      calc B (suEnd B t x) y = B (suEnd B t x) (suEnd B t (suEnd B t y)) := by rw [hTx]
        _ = B x (suEnd B t y) := suEnd_isometry _ _ _
    rw [hDx, hDx, map_sub, LinearMap.sub_apply, map_sub, h1]
  have hU : LinearMap.range D ≠ ⊥ := by
    rw [Ne, LinearMap.range_eq_bot]
    exact hD0
  obtain ⟨w, ⟨u, hu⟩, hw0, hwfix⟩ := exists_ne_zero_forall_eq hP
    ((suEnd B).comp ((centralizer ({t} : Set (sesqSpecialUnitaryGroup B))).subtype.comp
      (timmesfeldFStar _).subtype)) hU (by
        rintro g _ ⟨v, rfl⟩
        refine ⟨suEnd B ((g : centralizer ({t} : Set (sesqSpecialUnitaryGroup B))) :
          sesqSpecialUnitaryGroup B) v, ?_⟩
        exact LinearMap.congr_fun (hcomm _) v)
  have hwfix' : ∀ g ∈ timmesfeldFStar (centralizer ({t} : Set (sesqSpecialUnitaryGroup B))),
      suEnd B g w = w := fun g hg => hwfix ⟨g, hg⟩
  have hww : B w w = 0 := by
    rw [← hu, hDadj, ← Module.End.mul_apply, hDD, LinearMap.zero_apply, map_zero]
  have hc1 : (1 : F) + hF.bar 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  have hsU : hermTransvectionGL B hww 1 ∈ sesqSpecialUnitaryGroup B :=
    mem_sesqSpecialUnitaryGroup.mpr ⟨fun x y => hermTransvection_isometry hB hww hc1 x y,
      det_hermTransvection B hww 1⟩
  set s : sesqSpecialUnitaryGroup B := ⟨_, hsU⟩
  have hs : suEnd B s = hermTransvection B w 1 := rfl
  have hV1 : suEnd B s - 1 = D * (B w).smulRight u := by
    ext x
    rw [hs, LinearMap.sub_apply, hermTransvection_apply, Module.End.one_apply,
      add_sub_cancel_left, Module.End.mul_apply, LinearMap.smulRight_apply, map_smul, hu, one_mul]
  have hV2 : suEnd B s - 1 = (B u).smulRight w * D := by
    ext x
    rw [hs, LinearMap.sub_apply, hermTransvection_apply, Module.End.one_apply,
      add_sub_cancel_left, Module.End.mul_apply, LinearMap.smulRight_apply, ← hDadj, hu, one_mul]
  have hVD : (suEnd B s - 1) * D = 0 := by rw [hV2, mul_assoc, hDD, mul_zero]
  have hDV : D * (suEnd B s - 1) = 0 := by rw [hV1, ← mul_assoc, hDD, zero_mul]
  have hst : s * t = t * s := by
    apply suEnd_injective
    obtain ⟨V, hV⟩ : ∃ V, suEnd B s - 1 = V := ⟨_, rfl⟩
    rw [hV] at hVD hDV
    have hT : suEnd B t = D + 1 := (sub_eq_iff_eq_add.mp hD)
    have hS : suEnd B s = V + 1 := (sub_eq_iff_eq_add.mp hV)
    have e1 : (V + 1) * (D + 1) = V * D + V + D + 1 := by noncomm_ring
    have e2 : (D + 1) * (V + 1) = D * V + V + D + 1 := by noncomm_ring
    rw [map_mul, map_mul, hT, hS, e1, e2, hVD, hDV]
  set sC : centralizer ({t} : Set (sesqSpecialUnitaryGroup B)) :=
    ⟨s, mem_centralizer_singleton_iff.mpr hst⟩
  have hsA : sC ∈ axisGroupOf (suEnd B) t hDD' := by
    rw [mem_axisGroupOf, hD]
    exact ⟨⟨_, hV1⟩, ⟨_, hV2⟩⟩
  set tC : centralizer ({t} : Set (sesqSpecialUnitaryGroup B)) :=
    ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  have htZ : tC ∈ center (centralizer ({t} : Set (sesqSpecialUnitaryGroup B))) :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have htC1 : tC ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hsc : ∀ x ∈ timmesfeldFStar (centralizer ({t} : Set (sesqSpecialUnitaryGroup B))),
      x * sC = sC * x := by
    intro x hx
    apply Subtype.ext
    apply suEnd_injective
    have hxw : ∀ z, B w (suEnd B x z) = B w z := fun z => by
      conv_lhs => rw [← hwfix' x hx]
      exact suEnd_isometry _ _ _
    ext z
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, hs, hermTransvection_apply, hermTransvection_apply, map_add, map_smul,
      hwfix' x hx, hxw]
  rcases eq_one_or_eq_of_centralizes_fstar hZ htZ htC1 (axisGroupOf_normal _ t hDD')
    (axisGroupOf_comm _ suEnd_injective t hDD') hsA hsc with h | h
  · exfalso
    have h1 : suEnd B s = 1 := by
      have := congrArg (fun c : centralizer ({t} : Set (sesqSpecialUnitaryGroup B)) =>
        suEnd B (c : sesqSpecialUnitaryGroup B)) h
      simpa using this
    apply hw0
    apply hBl
    intro z
    have h2 := LinearMap.congr_fun h1 z
    rw [hs, hermTransvection_apply, Module.End.one_apply, add_eq_left, one_mul,
      smul_eq_zero] at h2
    exact h2.resolve_right hw0
  · refine ⟨w, hw0, hww, ?_⟩
    rw [← hs]
    exact congrArg (fun c : centralizer ({t} : Set (sesqSpecialUnitaryGroup B)) =>
      suEnd B (c : sesqSpecialUnitaryGroup B)) h.symm

end CFSG.LargeExtraspecial.S14.PSLPSU10
