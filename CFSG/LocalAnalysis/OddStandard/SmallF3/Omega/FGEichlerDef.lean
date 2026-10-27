module

public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  {B : LinearMap.BilinForm (ZMod 3) V} {ρ : V →ₗ[ZMod 3] V}

@[expose] def fgPlus (ρ : V →ₗ[ZMod 3] V) : Submodule (ZMod 3) V :=
  LinearMap.ker (ρ - LinearMap.id)

@[expose] def fgMinus (ρ : V →ₗ[ZMod 3] V) : Submodule (ZMod 3) V :=
  LinearMap.ker (ρ + LinearMap.id)

theorem mem_fgPlus {v : V} : v ∈ fgPlus ρ ↔ ρ v = v := by
  rw [fgPlus, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_fgMinus {v : V} : v ∈ fgMinus ρ ↔ ρ v = -v := by
  rw [fgMinus, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_eq_zero_iff_eq_neg]

theorem fg_plus_isotropic (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y) {u v : V} (hu : u ∈ fgPlus ρ)
    (hv : v ∈ fgPlus ρ) : B u v = 0 := by
  have hu' : ρ u = u := mem_fgPlus.mp hu
  have hv' : ρ v = v := mem_fgPlus.mp hv
  have h : B u v = -B u v := by
    have h' := hρB u v
    rwa [hu', hv'] at h'
  have h2 : (2 : ZMod 3) * B u v = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

theorem fg_minus_isotropic (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y) {u v : V}
    (hu : u ∈ fgMinus ρ) (hv : v ∈ fgMinus ρ) : B u v = 0 := by
  have hu' : ρ u = -u := mem_fgMinus.mp hu
  have hv' : ρ v = -v := mem_fgMinus.mp hv
  have h : B u v = -B u v := by
    have h' := hρB u v
    rw [hu', hv'] at h'
    simpa using h'
  have h2 : (2 : ZMod 3) * B u v = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

theorem fg_isCompl_plus_minus (hρ2 : ∀ v, ρ (ρ v) = v) : IsCompl (fgPlus ρ) (fgMinus ρ) := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2'
    rw [mem_fgPlus] at h1
    rw [fgMinus, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at h2'
    rw [h1] at h2'
    have hvv : (2 : ZMod 3) • v = 0 := by rw [two_smul]; exact h2'
    exact (smul_eq_zero.1 hvv).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v = (2 : ZMod 3)⁻¹ • (v + ρ v) + (2 : ZMod 3)⁻¹ • (v - ρ v) := by
      rw [← smul_add, add_add_sub_cancel, ← two_smul (ZMod 3) v, smul_smul,
        inv_mul_cancel₀ h2, one_smul]
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [fgPlus, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_add,
        hρ2, sub_eq_zero, add_comm]
    · rw [fgMinus, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_sub,
        hρ2, ← smul_add]
      simp

theorem fg_finrank_plus_minus [FiniteDimensional (ZMod 3) V] (hB : B.Nondegenerate)
    (hsymm : ∀ x y, B x y = B y x) (hρ2 : ∀ v, ρ (ρ v) = v)
    (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y) (hdim : Module.finrank (ZMod 3) V = 6) :
    Module.finrank (ZMod 3) (fgPlus ρ) = 3 ∧ Module.finrank (ZMod 3) (fgMinus ρ) = 3 := by
  have hcompl : IsCompl (fgPlus ρ) (fgMinus ρ) := fg_isCompl_plus_minus hρ2
  have hsum : Module.finrank (ZMod 3) (fgPlus ρ) + Module.finrank (ZMod 3) (fgMinus ρ) = 6 := by
    rw [← hdim]
    exact Submodule.finrank_add_eq_of_isCompl hcompl
  let Φ : fgMinus ρ →ₗ[ZMod 3] Module.Dual (ZMod 3) (fgPlus ρ) :=
    (LinearMap.domRestrict' (fgPlus ρ)).comp (LinearMap.comp B (fgMinus ρ).subtype)
  have hΦinj : Function.Injective Φ := by
    intro w1 w2 hw
    have hsub : (w1 : V) - (w2 : V) = 0 := by
      refine hB.1 _ ?_
      intro z
      have hz : z ∈ fgPlus ρ ⊔ fgMinus ρ := by
        rw [hcompl.codisjoint.eq_top]
        exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hz with ⟨a, ha, b, hb, rfl⟩
      have hwa : B (w1 : V) a = B (w2 : V) a := by
        have := congrArg (fun f : Module.Dual (ZMod 3) (fgPlus ρ) => f ⟨a, ha⟩) hw
        simpa only [Φ, LinearMap.comp_apply, LinearMap.domRestrict'_apply,
          Submodule.subtype_apply] using this
      have hb1 : B (w1 : V) b = 0 := fg_minus_isotropic hρB w1.property hb
      have hb2 : B (w2 : V) b = 0 := fg_minus_isotropic hρB w2.property hb
      simp only [map_add, map_sub, LinearMap.sub_apply, hwa, hb1, hb2, sub_self, add_zero]
    exact Subtype.ext (sub_eq_zero.mp hsub)
  have hle1 : Module.finrank (ZMod 3) (fgMinus ρ) ≤ Module.finrank (ZMod 3) (fgPlus ρ) := by
    have h := LinearMap.finrank_le_finrank_of_injective hΦinj
    rwa [Subspace.dual_finrank_eq] at h
  let Ψ : fgPlus ρ →ₗ[ZMod 3] Module.Dual (ZMod 3) (fgMinus ρ) :=
    (LinearMap.domRestrict' (fgMinus ρ)).comp (LinearMap.comp B (fgPlus ρ).subtype)
  have hΨinj : Function.Injective Ψ := by
    intro u1 u2 hu
    have hsub : (u1 : V) - (u2 : V) = 0 := by
      refine hB.1 _ ?_
      intro z
      have hz : z ∈ fgPlus ρ ⊔ fgMinus ρ := by
        rw [hcompl.codisjoint.eq_top]
        exact Submodule.mem_top
      rcases Submodule.mem_sup.mp hz with ⟨a, ha, b, hb, rfl⟩
      have hub : B (u1 : V) b = B (u2 : V) b := by
        have := congrArg (fun f : Module.Dual (ZMod 3) (fgMinus ρ) => f ⟨b, hb⟩) hu
        simpa only [Ψ, LinearMap.comp_apply, LinearMap.domRestrict'_apply,
          Submodule.subtype_apply] using this
      have ha1 : B (u1 : V) a = 0 := fg_plus_isotropic hρB u1.property ha
      have ha2 : B (u2 : V) a = 0 := fg_plus_isotropic hρB u2.property ha
      simp only [map_add, map_sub, LinearMap.sub_apply, hub, ha1, ha2, sub_self, zero_sub,
        zero_add]
    exact Subtype.ext (sub_eq_zero.mp hsub)
  have hle2 : Module.finrank (ZMod 3) (fgPlus ρ) ≤ Module.finrank (ZMod 3) (fgMinus ρ) := by
    have h := LinearMap.finrank_le_finrank_of_injective hΨinj
    rwa [Subspace.dual_finrank_eq] at h
  have heq : Module.finrank (ZMod 3) (fgPlus ρ) = Module.finrank (ZMod 3) (fgMinus ρ) :=
    le_antisymm hle2 hle1
  constructor <;> omega

@[expose] def fgEichler (B : LinearMap.BilinForm (ZMod 3) V) (u w : V) : V →ₗ[ZMod 3] V :=
  LinearMap.id + (B w).smulRight u - (B u).smulRight w

theorem fgEichler_apply (u w x : V) : fgEichler B u w x = x + B w x • u - B u x • w := by
  simp [fgEichler, LinearMap.smulRight_apply]

theorem fg_eichler_isom (hsymm : ∀ x y, B x y = B y x) {u w : V} (hu : B u u = 0)
    (hw : B w w = 0) (huw : B u w = 0) (x y : V) :
    B (fgEichler B u w x) (fgEichler B u w y) = B x y := by
  rw [fgEichler_apply, fgEichler_apply]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm x u, hsymm x w, hsymm w u, hu, hw, huw]
  ring

theorem fg_eichler_comm (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    (hsymm : ∀ x y, B x y = B y x) {u w : V} {ε : ZMod 3} (hu : ρ u = ε • u)
    (hw : ρ w = (-ε) • w) (x : V) : ρ (fgEichler B u w x) = fgEichler B u w (ρ x) := by
  have hw' : B w (ρ x) = ε * B w x := by
    have h := hρB w (ρ x)
    rw [hw, hρ2 x] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    linear_combination h
  have hu' : B u (ρ x) = -ε * B u x := by
    have h := hρB u (ρ x)
    rw [hu, hρ2 x] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    linear_combination h
  rw [fgEichler_apply, fgEichler_apply]
  simp only [map_add, map_sub, map_smul, hu, hw, hw', hu']
  module

theorem fg_eichler_inv (hsymm : ∀ x y, B x y = B y x) {u w : V} (hu : B u u = 0)
    (hw : B w w = 0) (huw : B u w = 0) (x : V) :
    fgEichler B w u (fgEichler B u w x) = x := by
  rw [fgEichler_apply, fgEichler_apply]
  have huy : B u (x + B w x • u - B u x • w) = B u x := by
    simp [map_add, map_sub, map_smul, hu, huw]
  have hwy : B w (x + B w x • u - B u x • w) = B w x := by
    simp [map_add, map_sub, map_smul, hw, huw, hsymm w u]
  rw [huy, hwy]
  abel

private theorem fg_eichler_sq (hsymm : ∀ x y, B x y = B y x) {u w : V} (hu : B u u = 0)
    (hw : B w w = 0) (huw : B u w = 0) (y : V) :
    fgEichler B u w (fgEichler B u w y) =
      y + (2 : ZMod 3) • (B w y • u - B u y • w) := by
  rw [fgEichler_apply, fgEichler_apply]
  have huy : B u (y + B w y • u - B u y • w) = B u y := by
    simp [map_add, map_sub, map_smul, hu, huw]
  have hwy : B w (y + B w y • u - B u y • w) = B w y := by
    simp [map_add, map_sub, map_smul, hw, huw, hsymm w u]
  rw [huy, hwy]
  module

theorem fg_eichler_cube (hsymm : ∀ x y, B x y = B y x) {u w : V} (hu : B u u = 0)
    (hw : B w w = 0) (huw : B u w = 0) (x : V) :
    fgEichler B u w (fgEichler B u w (fgEichler B u w x)) = x := by
  have huy : B u (x + B w x • u - B u x • w) = B u x := by
    simp [map_add, map_sub, map_smul, hu, huw]
  have hwy : B w (x + B w x • u - B u x • w) = B w x := by
    simp [map_add, map_sub, map_smul, hw, huw, hsymm w u]
  rw [fg_eichler_sq (B := B) hsymm hu hw huw (fgEichler B u w x)]
  rw [fgEichler_apply]
  rw [hwy, huy]
  have h3 : (2 : ZMod 3) • (B w x • u - B u x • w) + (B w x • u - B u x • w) = 0 := by
    rw [show (2 : ZMod 3) = -1 by decide, neg_smul, one_smul, neg_add_cancel]
  rw [add_sub_assoc, add_assoc, add_comm (B w x • u - B u x • w), h3, add_zero]

theorem fg_exists_eichler_equiv (hsymm : ∀ x y, B x y = B y x) {u w : V} (hu : B u u = 0)
    (hw : B w w = 0) (huw : B u w = 0) :
    ∃ σ : V ≃ₗ[ZMod 3] V, ∀ x, σ x = fgEichler B u w x := by
  have hwu : B w u = 0 := by rw [hsymm w u, huw]
  refine ⟨LinearEquiv.ofLinearMap (fgEichler B u w) (fgEichler B w u) ?_ ?_,
    fun x => rfl⟩
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    exact fg_eichler_inv hsymm hw hu hwu x
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    exact fg_eichler_inv hsymm hu hw huw x

end CFSG.OddStandard.SmallF3.Omega
