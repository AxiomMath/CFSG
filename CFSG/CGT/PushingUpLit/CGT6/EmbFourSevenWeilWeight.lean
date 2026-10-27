module

public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenWeilBound
public import CFSG.CGT.PushingUpLit.CGT6.EmbFourSevenWeilDefs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.CGT.PushingUpLit.CGT6.WeilCount

open Module
open scoped commutatorElement

section Invariant

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] {Γ : Type} [Group Γ]

@[expose] def restrictAct (ρ₀ : Γ →* Module.End K W) (U : Submodule K W)
    (hU : ∀ g, ∀ u ∈ U, ρ₀ g u ∈ U) : Γ →* Module.End K ↥U where
  toFun g := (ρ₀ g).restrict (hU g)
  map_one' := by
    ext u
    simp
  map_mul' g h := by
    ext u
    simp

@[expose] def WeilData.ofInvariant (ρ₀ : Γ →* Module.End K W) (U : Submodule K W)
    (hU : ∀ g, ∀ u ∈ U, ρ₀ g u ∈ U) (lam : Subgroup.center Γ →* Kˣ)
    (hlam : ∀ z : Subgroup.center Γ, ∀ u ∈ U, ρ₀ z u = (lam z : K) • u)
    (hcomm : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ)
    (hnd : ∀ g : Γ, (∀ h : Γ, lam ⟨⁅g, h⁆, hcomm g h⟩ = 1) → g ∈ Subgroup.center Γ) :
    WeilData K ↥U Γ where
  ρ := (restrictAct ρ₀ U hU).toHomUnits
  lam := lam
  hlam z := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    show ρ₀ z (u : W) = (lam z : K) • (u : W)
    exact hlam z u u.2
  hcomm := hcomm
  hnd := hnd

@[expose] def restrictUnit (U : Submodule K W) (t t' : Module.End K W) (htt' : t * t' = 1)
    (ht't : t' * t = 1) (ht : ∀ u ∈ U, t u ∈ U) (ht' : ∀ u ∈ U, t' u ∈ U) :
    (Module.End K ↥U)ˣ where
  val := t.restrict ht
  inv := t'.restrict ht'
  val_inv := LinearMap.ext fun u => Subtype.ext (congrArg (fun f => f (u : W)) htt')
  inv_val := LinearMap.ext fun u => Subtype.ext (congrArg (fun f => f (u : W)) ht't)

@[expose] def WeilTwist.ofInvariant (ρ₀ : Γ →* Module.End K W) (U : Submodule K W)
    (hU : ∀ g, ∀ u ∈ U, ρ₀ g u ∈ U) (lam : Subgroup.center Γ →* Kˣ)
    (hlam : ∀ z : Subgroup.center Γ, ∀ u ∈ U, ρ₀ z u = (lam z : K) • u)
    (hcomm : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ)
    (hnd : ∀ g : Γ, (∀ h : Γ, lam ⟨⁅g, h⁆, hcomm g h⟩ = 1) → g ∈ Subgroup.center Γ)
    (σ : MulAut Γ) (hσc : ∀ z ∈ Subgroup.center Γ, σ z = z) (t t' : Module.End K W)
    (htt' : t * t' = 1) (ht't : t' * t = 1) (ht : ∀ u ∈ U, t u ∈ U) (ht' : ∀ u ∈ U, t' u ∈ U)
    (hT : ∀ g, ρ₀ (σ g) = t * ρ₀ g * t') :
    WeilTwist (WeilData.ofInvariant ρ₀ U hU lam hlam hcomm hnd) where
  σ := σ
  T := restrictUnit U t t' htt' ht't ht ht'
  hσc := hσc
  hT g := by
    refine Units.ext (LinearMap.ext fun u => Subtype.ext ?_)
    show ρ₀ (σ g) (u : W) = t (ρ₀ g (t' (u : W)))
    exact congrArg (fun f => f (u : W)) (hT g)

end Invariant

section Bound

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] {Γ : Type} [Group Γ]
  [Fintype Γ]

theorem restrict_pow_apply (U : Submodule K W) (t : Module.End K W) (ht : ∀ u ∈ U, t u ∈ U)
    (n : ℕ) (u : ↥U) : (((t.restrict ht) ^ n) u : W) = (t ^ n) (u : W) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    exact congrArg t (ih _)

theorem weight_bound [FiniteDimensional K W] (hA : ArithStmt) {p j : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hj : 2 ≤ j) (ρ₀ : Γ →* Module.End K W) (U : Submodule K W)
    (hU : ∀ g, ∀ u ∈ U, ρ₀ g u ∈ U) (lam : Subgroup.center Γ →* Kˣ)
    (hlam : ∀ z : Subgroup.center Γ, ∀ u ∈ U, ρ₀ z u = (lam z : K) • u)
    (hcomm : ∀ g h : Γ, ⁅g, h⁆ ∈ Subgroup.center Γ)
    (hnd : ∀ g : Γ, (∀ h : Γ, lam ⟨⁅g, h⁆, hcomm g h⟩ = 1) → g ∈ Subgroup.center Γ)
    (σ : MulAut Γ) (hσc : ∀ z ∈ Subgroup.center Γ, σ z = z) (t t' : Module.End K W)
    (htt' : t * t' = 1) (ht't : t' * t = 1) (ht : ∀ u ∈ U, t u ∈ U) (ht' : ∀ u ∈ U, t' u ∈ U)
    (hT : ∀ g, ρ₀ (σ g) = t * ρ₀ g * t') (hΓ : (Fintype.card Γ : K) ≠ 0) (ζ : K)
    (hζ : IsPrimitiveRoot ζ 5) (σb : MulAut (Γ ⧸ Subgroup.center Γ))
    (hσb : ∀ g : Γ, σb (QuotientGroup.mk g) = QuotientGroup.mk (σ g)) (h5 : σb ^ 5 = 1)
    (hT5 : t ^ 5 = 1) (hM : Nat.card (Γ ⧸ Subgroup.center Γ) = p ^ j)
    (hC1 : Nat.card (MonoidHom.eqLocus
      (σb : (Γ ⧸ Subgroup.center Γ) →* (Γ ⧸ Subgroup.center Γ)) (MonoidHom.id _)) * p ≤
        Nat.card (Γ ⧸ Subgroup.center Γ))
    (hC2 : p ≠ 5 → Nat.card (MonoidHom.eqLocus
      (σb : (Γ ⧸ Subgroup.center Γ) →* (Γ ⧸ Subgroup.center Γ)) (MonoidHom.id _)) * p ^ 2 ≤
        Nat.card (Γ ⧸ Subgroup.center Γ))
    (hC3 : p = 3 → Nat.card (MonoidHom.eqLocus
      (σb : (Γ ⧸ Subgroup.center Γ) →* (Γ ⧸ Subgroup.center Γ)) (MonoidHom.id _)) * 81 ≤
        Nat.card (Γ ⧸ Subgroup.center Γ))
    (hU0 : U ≠ ⊥) :
    (if p = 3 then 3 else 2) ≤ finrank K (Submodule.map (t - 1) U) := by
  set D := WeilData.ofInvariant ρ₀ U hU lam hlam hcomm hnd with hD
  set Tw := WeilTwist.ofInvariant ρ₀ U hU lam hlam hcomm hnd σ hσc t t' htt' ht't ht ht' hT
    with hTw
  have hTt : (Tw.T : Module.End K ↥U) = t.restrict ht := rfl
  have hT5' : (Tw.T : Module.End K ↥U) ^ 5 = 1 := by
    rw [hTt]
    refine LinearMap.ext fun u => Subtype.ext ?_
    rw [restrict_pow_apply, hT5]
    rfl
  obtain ⟨e, he1, he2⟩ := Tw.weil_bound hΓ ζ hζ σb hσb h5 hT5'
  set a := finrank K (Module.End.eigenspace (Tw.T : Module.End K ↥U) 1) with ha
  set S := finrank K ↥U with hS
  have hCpos : 1 ≤ Nat.card (MonoidHom.eqLocus
      (σb : (Γ ⧸ Subgroup.center Γ) →* (Γ ⧸ Subgroup.center Γ)) (MonoidHom.id _)) :=
    Nat.card_pos
  have hS1 : 1 ≤ S := Submodule.one_le_finrank_iff.mpr hU0
  have haS : a ≤ S := Submodule.finrank_le _
  have key := hA p j _ _ S a e hp hodd hj hM hCpos hC1 hC2 hC3 he1 hS1 haS he2
  have hker : LinearMap.ker ((t - 1).domRestrict U) =
      Module.End.eigenspace (Tw.T : Module.End K ↥U) 1 := by
    ext u
    simp [sub_eq_zero, hTt, Subtype.ext_iff]
  have hrn := LinearMap.finrank_range_add_finrank_ker ((t - 1).domRestrict U)
  rw [hker, LinearMap.range_domRestrict] at hrn
  omega

end Bound

end CFSG.CGT.PushingUpLit.CGT6.WeilCount
