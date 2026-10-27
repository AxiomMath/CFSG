module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64PointTwoGroup
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64OtherParabolic
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64Lagrangian

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBI

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank
open BinarySymplecticSix BinarySymplecticSix.Degree64 BinarySymplecticSix.FusionOrbits
  BinarySymplecticSix.RadicalLabels
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem pointLabel_eq_ptHom {G : Type} [Group G] {L : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V} {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
    (he : IsSymplecticBasis b e) (hb : b.IsAlt) (φ : L ≃* bilinIsometryGroup b) {z : G}
    (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2)
    (w : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) (t ε : ZMod 2) :
    ((φ.symm (pointElt hb (mem_pairOrth_left w.2) (t + (e.repr w (Sum.inl 1) *
        e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)))) : L) : G) *
        z ^ ε.val =
      ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, t), ε)) := by
  rw [show e.repr (w : V) (Sum.inl 1) * e.repr (w : V) (Sum.inr 1) +
      e.repr (w : V) (Sum.inl 2) * e.repr (w : V) (Sum.inr 2) = ptQuad e w from rfl,
    ← ptHomV_ptQuad he hb w (t + ptQuad e w), add_assoc, zmod_two_add_self_eq_zero, add_zero]
  rfl

theorem exists_action_parameters
    {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (normalizer ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔
        zpowers z : Subgroup G) : Set G)) z =
      z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G)) :
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
    ∃ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) ∧
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) := by
  obtain ⟨-, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, -, -, -, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ, D₂, F₂, ν₂, hD₂, -, hD₂N, -, hD₂n, -, -, -, hν₂z, hν₂eq, hν₂surj, hact₂, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  obtain ⟨-, hfull₁⟩ := degree64_point_fusion_of_lagrangian he hb hnd φ hzC hsup hinf hz hV hD₂N
    hD₂n hν₂z hν₂eq hν₂surj hact₂
  obtain ⟨lam₀, D₁, F₁, ν₁, hD₁, -, -, -, -, -, -, -, -, -, -, hν₁z, -, -, hact₁, -⟩ :=
    degree64_point_two_group he hb hnd φ hzC hsup hinf hz hfull₁
  intro u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂' A₁ B₁ N₁ D₁'
  refine ⟨κ, lam₀, ?_, ?_⟩
  · intro d hd C B ε hdz
    have hd' : d ∈ D₂ := by
      rw [hD₂]
      exact hd
    have hC : C = ν₂ d := by
      have h := radHom_injective φ he hzC hz hinf (hdz.symm.trans (hν₂z d hd'))
      exact congrArg Prod.fst (Multiplicative.ofAdd.injective h)
    subst hC
    exact hact₂ d hd' B ε
  · intro d hd a v ε hdz
    have hd' : d ∈ D₁ := by
      rw [hD₁]
      exact hd
    have hθ : ∀ x : (E × ZMod 2) × ZMod 2,
        θ₁ x = ptHom he hb φ hzC hz (Multiplicative.ofAdd x) := fun x =>
      pointLabel_eq_ptHom he hb φ hzC hz x.1.1 x.1.2 x.2
    have ha : a = ν₁ d := by
      rw [hθ] at hdz
      have h := ptHom_injective he hb φ hzC hz hinf (hdz.symm.trans (hν₁z d hd'))
      exact congrArg Prod.fst (Multiplicative.ofAdd.injective h)
    subst ha
    rw [hθ, hθ]
    exact hact₁ d hd' v ε

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBI
