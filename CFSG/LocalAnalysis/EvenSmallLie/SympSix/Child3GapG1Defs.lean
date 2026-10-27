module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Defs

public noncomputable section

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def InputLamZero : Prop :=
  ∀ {G : Type} [Group G] [Finite G], CFSG.oddCore G = ⊥ → ∀ {L : Subgroup G},
    CFSG.Assembly.ComponentType.IsStandardSubgroup L → ¬ L.Normal → center L = ⊥ →
    CFSG.Blueprint.LieModel L .PSp 3 2 1 →
  ∀ (T : Sylow 2 (centralizer (L : Set G))), IsCyclic (T : Subgroup (centralizer (L : Set G))) →
  ∀ {z : G}, z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype →
    orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ →
  ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt), b.Nondegenerate → finrank (ZMod 2) V = 6 →
  ∀ (φ : L ≃* bilinIsometryGroup b) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V)
    (he : IsSymplecticBasis b e),
    conjClass (normalizer ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔
        zpowers z : Subgroup G) : Set G)) z =
      z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G) →
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let τ : ↥(binarySymMatrices 3) → G := fun B => tauHom φ he (Multiplicative.ofAdd B)
    let θ₂ : ↥(binarySymMatrices 3) × ZMod 2 → G := fun x => τ x.1 * z ^ x.2.val
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let A₂ := pullSub φ (pointwiseStabilizer b (lagrangianOf e))
    let R₂ := A₂ ⊔ zpowers z
    let N₂ := normalizer (R₂ : Set G)
    let D₂ := CFSG.Assembly.pCoreOf 2 N₂
    let A₁ := pullSub φ (pointRadical b hb u f)
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    ∀ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) →
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
      lam = 0 → ¬ IsElementaryAbelian 2 (sp6C₂ φ he z) → False

end CFSG.EvenSmallLie.Child3
