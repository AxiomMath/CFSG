module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ScalarDescent
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section Desc

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F]
  {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
  {W' : Type} [AddCommGroup W'] [Module (ZMod p) W'] [Module.Finite (ZMod p) W']

omit [Finite F] in
theorem exists_ne_zero_hom_of_extendScalars
    (σ : Representation (ZMod p) (SLm F) W) (σ' : Representation (ZMod p) (SLm F) W')
    (f : (CFSG.Theory.Representation.extendScalars F σ).asModule →ₗ[MonoidAlgebra F (SLm F)]
      (CFSG.Theory.Representation.extendScalars F σ').asModule) (hf : f ≠ 0) :
    ∃ g : σ.asModule →ₗ[MonoidAlgebra (ZMod p) (SLm F)] σ'.asModule, g ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hf
  have hsub : ∀ h : Representation.IntertwiningMap σ σ', h = 0 := fun h =>
    (Representation.IntertwiningMap.equivLinearMapAsModule σ σ').map_eq_zero_iff.mp
      (hcon _)
  let e := CFSG.Theory.Representation.intertwiningMapBaseChangeEquiv (E := F) σ σ'
  let e2 := Representation.IntertwiningMap.equivLinearMapAsModule
    (CFSG.Theory.Representation.extendScalars F σ) (CFSG.Theory.Representation.extendScalars F σ')
  obtain ⟨z, hz⟩ := (e.trans e2).surjective f
  have hz0 : ∀ z : F ⊗[ZMod p] (Representation.IntertwiningMap σ σ'), z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a h => rw [hsub h, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [← hz, hz0 z, map_zero]

omit [Finite F] in
theorem natCard_end_eq_pow_finrank_extendScalars
    (σ : Representation (ZMod p) (SLm F) W) :
    Nat.card (Module.End (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) =
      p ^ Module.finrank F (Module.End (MonoidAlgebra F (SLm F))
        (CFSG.Theory.Representation.extendScalars F σ).asModule) := by
  let e1 := Representation.IntertwiningMap.equivLinearMapAsModule σ σ
  let e2 := CFSG.Theory.Representation.intertwiningMapBaseChangeEquiv (E := F) σ σ
  let e3 := Representation.IntertwiningMap.equivLinearMapAsModule
    (CFSG.Theory.Representation.extendScalars F σ) (CFSG.Theory.Representation.extendScalars F σ)
  have h1 : Nat.card (Module.End (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) =
      Nat.card (Representation.IntertwiningMap σ σ) := Nat.card_congr e1.toEquiv.symm
  have h2 : Nat.card (Representation.IntertwiningMap σ σ) =
      p ^ Module.finrank (ZMod p) (Representation.IntertwiningMap σ σ) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have h3 : Module.finrank F (Module.End (MonoidAlgebra F (SLm F))
        (CFSG.Theory.Representation.extendScalars F σ).asModule) =
      Module.finrank (ZMod p) (Representation.IntertwiningMap σ σ) := by
    rw [← (e2.trans e3).finrank_eq, Module.finrank_baseChange]
  rw [h1, h2, h3]

end Desc

end CFSG.GH74.GLS.Stage4.Rest
