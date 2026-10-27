module

public import CFSG.Quasithin.Background.Module
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6.WeilDual

open Module CFSG.Quasithin

variable {V : Type} [CommGroup V] (K : Type) [Field K] [Algebra (ZMod 2) K]
  [Module (ZMod 2) (Additive V)]

@[expose] def autLin (g : MulAut V) : Additive V →ₗ[ZMod 2] Additive V :=
  AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (g : V →* V))

theorem autLin_apply (g : MulAut V) (v : Additive V) :
    autLin g v = Additive.ofMul (g (Additive.toMul v)) := rfl

theorem autLin_mul (g h : MulAut V) : autLin (g * h) = autLin g ∘ₗ autLin h := by
  ext v
  rfl

theorem autLin_one : autLin (1 : MulAut V) = LinearMap.id := by
  ext v
  rfl

@[expose] def act (g : MulAut V) : Module.End K (Additive V →ₗ[ZMod 2] K) where
  toFun φ := φ ∘ₗ autLin g⁻¹
  map_add' _ _ := LinearMap.add_comp _ _ _
  map_smul' _ _ := LinearMap.smul_comp _ _ _

theorem act_apply (g : MulAut V) (φ : Additive V →ₗ[ZMod 2] K) (v : Additive V) :
    act K g φ v = φ (autLin g⁻¹ v) := rfl

@[expose] def actHom : MulAut V →* Module.End K (Additive V →ₗ[ZMod 2] K) where
  toFun := act K
  map_one' := by
    ext φ v
    simp [act_apply, autLin_one]
  map_mul' g h := by
    ext φ v
    simp only [Module.End.mul_apply, act_apply, mul_inv_rev, autLin_mul, LinearMap.comp_apply]

theorem actHom_apply (g : MulAut V) (φ : Additive V →ₗ[ZMod 2] K) (v : Additive V) :
    actHom K g φ v = φ (autLin g⁻¹ v) := rfl

theorem exists_act_ne_one (g : MulAut V) (hg : g ≠ 1) :
    ∃ φ : Additive V →ₗ[ZMod 2] K, actHom K g φ ≠ φ := by
  obtain ⟨v, hv⟩ : ∃ v : V, g v ≠ v := by
    by_contra h
    push Not at h
    exact hg (MulEquiv.ext h)
  set u : Additive V := Additive.ofMul (g v) with hu
  have hw : autLin g⁻¹ u - u ≠ 0 := by
    intro h
    apply hv
    have h1 : autLin g⁻¹ u = u := sub_eq_zero.mp h
    have h2 : g⁻¹ (g v) = g v := h1
    have h3 : v = g v := by
      have := congrArg g h2
      simpa using this
    exact h3.symm
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hw
  refine ⟨(Algebra.linearMap (ZMod 2) K) ∘ₗ f, fun h => ?_⟩
  have h1 := congrArg (fun φ : Additive V →ₗ[ZMod 2] K => φ u) h
  simp only [actHom_apply, LinearMap.comp_apply, Algebra.linearMap_apply] at h1
  apply hf
  have h2 : f (autLin g⁻¹ u) = f u := (algebraMap (ZMod 2) K).injective h1
  rw [map_sub, h2]
  exact sub_self _

section Frobenius

variable [CharP K 2]

@[expose] def frob (φ : Additive V →ₗ[ZMod 2] K) : Additive V →ₗ[ZMod 2] K :=
  AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' (fun v => (φ v) ^ 2) (fun a b => by
    rw [map_add, CharTwo.add_sq]))

theorem frob_apply (φ : Additive V →ₗ[ZMod 2] K) (v : Additive V) : frob K φ v = (φ v) ^ 2 := rfl

theorem frob_ne_zero {φ : Additive V →ₗ[ZMod 2] K} (hφ : φ ≠ 0) : frob K φ ≠ 0 := by
  intro h
  apply hφ
  ext v
  have := congrArg (fun ψ : Additive V →ₗ[ZMod 2] K => ψ v) h
  simpa [frob_apply] using this

theorem actHom_frob (g : MulAut V) (φ : Additive V →ₗ[ZMod 2] K) :
    actHom K g (frob K φ) = frob K (actHom K g φ) := rfl

theorem frob_smul (c : K) (φ : Additive V →ₗ[ZMod 2] K) :
    frob K (c • φ) = c ^ 2 • frob K φ := by
  ext v
  simp [frob_apply, mul_pow]

end Frobenius

section Rank

variable [Finite V]

theorem finrank_range_act_sub_one_le (x : MulAut V) {m : ℕ}
    (hx : Nat.card (commV (Subgroup.zpowers x)) ≤ 2 ^ m) :
    finrank K (LinearMap.range (actHom K x - 1)) ≤ m := by
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  set d : Additive V →ₗ[ZMod 2] Additive V := autLin x⁻¹ - LinearMap.id with hd
  set A : Submodule (ZMod 2) (Additive V) := LinearMap.range d with hA
  have hN : ∀ φ : Additive V →ₗ[ZMod 2] K, (actHom K x - 1) φ = φ ∘ₗ d := by
    intro φ
    ext v
    simp [hd, actHom_apply]
  let Θ : (↥A →ₗ[ZMod 2] K) →ₗ[K] (Additive V →ₗ[ZMod 2] K) :=
    { toFun := fun ψ => ψ ∘ₗ d.rangeRestrict
      map_add' := fun _ _ => LinearMap.add_comp _ _ _
      map_smul' := fun _ _ => LinearMap.smul_comp _ _ _ }
  have hle : LinearMap.range (actHom K x - 1) ≤ LinearMap.range Θ := by
    rintro _ ⟨φ, rfl⟩
    refine ⟨φ ∘ₗ A.subtype, ?_⟩
    show (φ ∘ₗ A.subtype) ∘ₗ d.rangeRestrict = _
    rw [hN, LinearMap.comp_assoc, LinearMap.subtype_comp_rangeRestrict]
  have h1 : finrank K (LinearMap.range (actHom K x - 1)) ≤ finrank K (↥A →ₗ[ZMod 2] K) :=
    (Submodule.finrank_mono hle).trans (LinearMap.finrank_range_le Θ)
  rw [Module.finrank_linearMap_self] at h1
  refine h1.trans ?_
  have hcard : Nat.card ↥A ≤ Nat.card (commV (Subgroup.zpowers x)) := by
    refine Nat.card_le_card_of_injective (fun a => ⟨Additive.toMul (a : Additive V), ?_⟩) ?_
    · obtain ⟨v, hv⟩ := a.2
      rw [← hv]
      show Additive.toMul (autLin x⁻¹ v - v) ∈ _
      rw [toMul_sub]
      exact Subgroup.subset_closure ⟨x⁻¹, inv_mem (Subgroup.mem_zpowers x), Additive.toMul v, by
        simp [autLin_apply, div_eq_mul_inv]⟩
    · intro a b hab
      have h1 := congrArg (fun y : ↥(commV (Subgroup.zpowers x)) => (y : V)) hab
      exact Subtype.ext (Additive.toMul.injective h1)
  have h2 : Nat.card ↥A = 2 ^ finrank (ZMod 2) ↥A := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [h2] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (hcard.trans hx)

end Rank

end CFSG.CGT.PushingUpLit.CGT6.WeilDual
